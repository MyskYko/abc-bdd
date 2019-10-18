/**CFile****************************************************************

  FileName    [extraUtilCspf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [Minimization using permissible functions and the simple BDD package]

  Author      [Yukio Miyasaka]
  
  Affiliation [The University of Tokyo]

  Date        []

  Revision    []

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "extra.h"
#include "misc/vec/vec.h"
#include "aig/gia/gia.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Abc_NandMan_ Abc_NandMan;
struct Abc_NandMan_ 
{
  int nGiaObjs;
  int nObjsAlloc;
  Vec_Int_t * vPis;
  Vec_Int_t * vPos;
  Vec_Int_t * vObjs;
  Vec_Int_t ** pvFanins;
  Vec_Int_t ** pvFanouts;
  int * pBddFuncs;
  int * pRank;
  unsigned * pGFuncs;
  Vec_Int_t ** pvCFuncs;
  
  int nMem;
  int nVerbose;
  
  Abc_BddMan * pBdd;
  Gia_Man_t * pDc;

  Vec_Int_t * vPiCkts;
  Vec_Int_t * vPiIdxs;
};

static inline int      Abc_BddNandConst0() { return 0; }  // = Gia_ObjId( pGia, Gia_ManConst0( pGia ) );

static inline int      Abc_BddNandObjIsPi( Abc_NandMan * p, int id ) { return (int)( p->pvFanins[id] == 0 ); }
static inline int      Abc_BddNandObjIsPo( Abc_NandMan * p, int id ) { return (int)( p->pvFanouts[id] == 0 ); }

static inline unsigned Abc_BddNandObjGetBddFunc( Abc_NandMan * p, int id ) { return p->pBddFuncs[id];            }
static inline void     Abc_BddNandObjSetBddFunc( Abc_NandMan * p, int id, unsigned Value ) { p->pBddFuncs[id] = Value; }

// TODO : modify counting 0 of bdd function
static inline int      Abc_BddNandCount0s( Abc_NandMan * p, int id, int nOverflow ) { return Abc_BddCount0s( p->pBdd, Abc_BddNandObjGetBddFunc( p, id ), nOverflow ); }

static inline int      Abc_BddNandObjIsEmpty( Abc_NandMan * p, int id ) { return (int)( p->pvFanins[id] == 0 && p->pvFanouts[id] == 0 ); }
static inline int      Abc_BddNandObjIsDead( Abc_NandMan * p, int id ) { return (int)( Vec_IntSize( p->pvFanouts[id] ) == 0 ); }
static inline int      Abc_BddNandObjIsEmptyOrDead( Abc_NandMan * p, int id ) { return ( Abc_BddNandObjIsEmpty( p, id ) || Abc_BddNandObjIsDead( p, id ) ); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_BddNandDescendantList_rec( Vec_Int_t ** children, Vec_Int_t * list, int id )
{
  int j, idj, index;
  Vec_IntForEachEntry( children[id], idj, j )
    {
      index = Vec_IntFind( list, idj );
      if ( index == -1 && children[idj] != 0 ) // idj is not in list and is not leaf
	{ 
	  Vec_IntPush( list, idj );
	  Abc_BddNandDescendantList_rec( children, list, idj );
	}
    }
}
static inline void Abc_BddNandDescendantSortedList( Abc_NandMan * p, Vec_Int_t ** children, Vec_Int_t * sortedList, int parent )
{
  int i, id, index;
  Vec_Int_t * list = Vec_IntAlloc( 1 );
  Abc_BddNandDescendantList_rec( children, list, parent );
  Vec_IntForEachEntry( p->vObjs, id, i )
    {
      index = Vec_IntFind( list, id );
      if ( index != -1 )
	{
	  Vec_IntDrop( list, index );      
	  Vec_IntPush( sortedList, id );
	  if ( Vec_IntSize( list ) == 0 ) break;
	}
    }
  Vec_IntFree( list );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_BddNandObjEntry( Abc_NandMan * p, int id )
{
  int j, idj, index, index_;
  index = Vec_IntSize( p->vObjs );
  Vec_IntForEachEntry( p->pvFanouts[id], idj, j )
    {
      index_ = Vec_IntFind( p->vObjs, idj );
      if ( index_ != -1 && index_ < index ) index = index_;
    }
  Vec_IntInsert( p->vObjs, index, id );
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      index_ = Vec_IntFind( p->vObjs, idj );
      if ( index_ > index )
	{
	  Vec_IntDrop( p->vObjs, index_ );
	  Abc_BddNandObjEntry( p, idj );
	  index = Vec_IntFind( p->vObjs, id );
	}
    }
}
static inline void Abc_BddNandConnect( Abc_NandMan * p, int fanin, int fanout, int fSort )
{ // uniqueness of conenction must be confirmed beforehand
  Vec_IntPush( p->pvFanins[fanout], fanin );    
  Vec_IntPush( p->pvFanouts[fanin], fanout );
  if ( fSort )
    {
      int index_fanout = Vec_IntFind( p->vObjs, fanout );
      int index_fanin = Vec_IntFind( p->vObjs, fanin );
      if ( index_fanout != -1 && index_fanout < index_fanin )
	{ // Omit the case fanout is not in vObjs for G3, and sort.
	  Vec_IntDrop( p->vObjs, index_fanin );
	  Abc_BddNandObjEntry( p, fanin );
	}
    }
}
static inline void Abc_BddNandDisconnect( Abc_NandMan * p, int fanin, int fanout )
{
  Vec_IntRemove( p->pvFanins[fanout], fanin );    
  Vec_IntRemove( p->pvFanouts[fanin], fanout );
}
static inline void Abc_BddNandRemoveNode( Abc_NandMan * p, int id )
{
  int j, idj;
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    Vec_IntRemove( p->pvFanouts[idj], id );
  Vec_IntForEachEntry( p->pvFanouts[id], idj, j )
    Vec_IntRemove( p->pvFanins[idj], id );
  Vec_IntFree( p->pvFanins[id] );
  Vec_IntFree( p->pvFanouts[id] );
  p->pvFanins[id] = 0;
  p->pvFanouts[id] = 0;
  Vec_IntRemove( p->vObjs, id );
}
static inline int Abc_BddNandCountWire( Abc_NandMan * p )
{
  int i, id, count;
  count = 0;
  Vec_IntForEachEntry( p->vObjs, id, i )
    count += Vec_IntSize( p->pvFanins[id] );
  return count;
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandGia2Net( Abc_NandMan * p, Gia_Man_t * pGia )
{
  Gia_Obj_t * pObj, * pObj0, * pObj1;
  int i, id, idj, id0, id1;
  // constant
  id = Abc_BddNandConst0();
  p->pBddFuncs[id] = Abc_BddLitConst0();
  p->pvFanins[id] = 0;
  p->pvFanouts[id] = Vec_IntAlloc( 1 );
  idj = id + p->nGiaObjs;
  p->pvFanins[idj] = Vec_IntAlloc( 1 );
  p->pvFanouts[idj] = Vec_IntAlloc( 1 );
  Vec_IntPush( p->vObjs, idj );
  Abc_BddNandConnect( p, id, idj, 0 );
  // pi
  Gia_ManForEachCi( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      p->pBddFuncs[id] = Abc_BddLitIthVar( i );
      p->pvFanins[id] = 0;
      p->pvFanouts[id] = Vec_IntAlloc( 1 );
      Vec_IntPush( p->vPis, id );
      idj = id + p->nGiaObjs;
      p->pvFanins[idj] = Vec_IntAlloc( 1 );
      p->pvFanouts[idj] = Vec_IntAlloc( 1 );
      Vec_IntPush( p->vObjs, idj );
      Abc_BddNandConnect( p, id, idj, 0 );
    }
  // gate
  Gia_ManForEachAnd( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      p->pvFanins[id] = Vec_IntAlloc( 1 );
      p->pvFanouts[id] = Vec_IntAlloc( 1 );
      pObj0 = Gia_ObjFanin0( pObj );
      pObj1 = Gia_ObjFanin1( pObj );
      id0 = Gia_ObjId( pGia, pObj0 );
      id1 = Gia_ObjId( pGia, pObj1 );
      if ( (  Gia_ObjIsCi( pObj0 ) &&  Gia_ObjFaninC0( pObj ) ) ||
	   ( !Gia_ObjIsCi( pObj0 ) && !Gia_ObjFaninC0( pObj ) ) )
	id0 += p->nGiaObjs;
      if ( (  Gia_ObjIsCi( pObj1 ) &&  Gia_ObjFaninC1( pObj ) ) ||
	   ( !Gia_ObjIsCi( pObj1 ) && !Gia_ObjFaninC1( pObj ) ) )  
	id1 += p->nGiaObjs;
      Abc_BddNandConnect( p, id0, id, 0 );
      Abc_BddNandConnect( p, id1, id, 0 );
      Vec_IntPush( p->vObjs, id );
      // create inverter
      idj = id + p->nGiaObjs;
      p->pvFanins[idj] = Vec_IntAlloc( 1 );
      p->pvFanouts[idj] = Vec_IntAlloc( 1 );
      Abc_BddNandConnect( p, id, idj, 0 );
      Vec_IntPush( p->vObjs, idj );    
    }
  // po
  Gia_ManForEachCo( pGia, pObj, i )
    {
      if ( p->pDc != NULL && i >= Gia_ManCoNum( pGia ) / 2 ) break;
      id = Gia_ObjId( pGia, pObj );
      p->pvFanins[id] = Vec_IntAlloc( 1 );
      p->pvFanouts[id] = 0;
      pObj0 = Gia_ObjFanin0( pObj );
      id0 = Gia_ObjId( pGia, pObj0 );
      if ( (  ( id0 == Abc_BddNandConst0() || Gia_ObjIsCi( pObj0 ) ) &&  Gia_ObjFaninC0( pObj ) ) ||
	   ( !( id0 == Abc_BddNandConst0() || Gia_ObjIsCi( pObj0 ) ) && !Gia_ObjFaninC0( pObj ) ) )
	id0 += p->nGiaObjs;
      Abc_BddNandConnect( p, id0, id, 0 );
      Vec_IntPush( p->vPos, id );
    }
  // remove redundant nodes
  Vec_IntForEachEntryReverse( p->vObjs, id, i )
    if ( Vec_IntSize( p->pvFanouts[id] ) == 0 )
      Abc_BddNandRemoveNode( p, id );
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandDc( Abc_NandMan * p )
{
  int i;
  Gia_Obj_t * pObj;
  // TODO : keep generated bdds and restore after refresh
  // TODO : error handling
  assert( !Abc_BddGia( p->pDc, p->pBdd ) );
  Gia_ManForEachCo( p->pDc, pObj, i )
    p->pGFuncs[Vec_IntEntry( p->vPos, i )] = pObj->Value;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_NandMan * Abc_BddNandManAlloc( Gia_Man_t * pGia, int nMem, int fDc, int nVerbose )
{
  Abc_NandMan * p = ABC_CALLOC( Abc_NandMan, 1 );
  p->nGiaObjs = pGia->nObjs;
  p->nObjsAlloc = pGia->nObjs + pGia->nObjs;
  p->vPis = Vec_IntAlloc( Gia_ManCiNum( pGia ) );
  p->vPos = Vec_IntAlloc( Gia_ManCoNum( pGia ) );
  p->vObjs = Vec_IntAlloc( 1 );
  // TODO : error handling
  p->pvFanins  = ABC_CALLOC( Vec_Int_t *, p->nObjsAlloc );
  p->pvFanouts = ABC_CALLOC( Vec_Int_t *, p->nObjsAlloc );
  p->pBddFuncs = ABC_CALLOC( int        , p->nObjsAlloc );
  p->pRank     = ABC_CALLOC( int        , p->nObjsAlloc );
  p->pGFuncs   = ABC_CALLOC( unsigned   , p->nObjsAlloc );
  p->pvCFuncs  = ABC_CALLOC( Vec_Int_t *, p->nObjsAlloc );
  p->nMem = nMem;
  p->nVerbose = nVerbose;
  p->vPiCkts = Vec_IntAlloc( 1 );
  p->vPiIdxs = Vec_IntAlloc( 1 );
  if ( fDc )
    {
      int i;
      const int nDcPos = Gia_ManCoNum( pGia ) / 2;
      int * vDcPos = ABC_CALLOC( int, nDcPos );
      for ( i = 0; i < nDcPos; i++ )
	vDcPos[i] = nDcPos + i;
      p->pDc= Gia_ManDupCones( pGia, vDcPos, nDcPos, 0 );
      ABC_FREE( vDcPos );
    }
  else p->pDc = NULL;
  Abc_BddNandGia2Net( p, pGia );
  return p;
}
static inline void Abc_BddNandManFree( Abc_NandMan * p )
{
  int i;
  Vec_IntFree( p->vPis );
  Vec_IntFree( p->vPos );
  Vec_IntFree( p->vObjs );
  Vec_IntFree( p->vPiCkts );
  Vec_IntFree( p->vPiIdxs );
  ABC_FREE( p->pBddFuncs );
  ABC_FREE( p->pRank );
  ABC_FREE( p->pGFuncs );
  for ( i = 0; i < p->nObjsAlloc; i++ )
    {
      if ( p->pvFanins[i] ) Vec_IntFree( p->pvFanins[i] );
      if ( p->pvFanouts[i] ) Vec_IntFree( p->pvFanouts[i] );
      if ( p->pvCFuncs[i] ) Vec_IntFree( p->pvCFuncs[i] );
    }
  ABC_FREE( p->pvFanins );
  ABC_FREE( p->pvFanouts );
  ABC_FREE( p->pvCFuncs );
  Abc_BddManFree( p->pBdd );
  if ( p->pDc != NULL ) Gia_ManStop( p->pDc );
  ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// TODO : consider change the method to rank
static inline void Abc_BddNandRank( Abc_NandMan * p, int id )
{
  if ( Abc_BddNandObjIsPi( p, id ) )
    p->pRank[id] = 1 << 30; // assume this is the max
  else if ( Vec_IntSize( p->vPis ) <= 20 )
    {
      p->pRank[id] = Vec_IntSize( p->pvFanouts[id] ) << Vec_IntSize( p->vPis );
      p->pRank[id] += Abc_BddNandCount0s( p, id, 0 );
    }
  else
    {
      int nOverflow = Vec_IntSize( p->vPis ) - 20;
      p->pRank[id] = Vec_IntSize( p->pvFanouts[id] ) << 20;
      p->pRank[id] += Abc_BddNandCount0s( p, id, nOverflow );
    }
  assert( p->pRank[id] >= 0 );
}
static inline void Abc_BddNandRankAll( Abc_NandMan * p )
{
  int i, id;
  Vec_IntForEachEntry( p->vPis, id, i )
    Abc_BddNandRank( p, id );
  Vec_IntForEachEntry( p->vObjs, id, i )
    Abc_BddNandRank( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandSortFanin( Abc_NandMan * p, int id )
{
  int j, k, idj, idk, best_j, best_idj;
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      best_j = j;
      best_idj = idj;
      Vec_IntForEachEntryStart( p->pvFanins[id], idk, k, j + 1 )
	if ( p->pRank[idj] > p->pRank[idk] )
	  {
	    best_j = k;
	    best_idj = idk;
	  }
      Vec_IntWriteEntry( p->pvFanins[id], j, best_idj );
      Vec_IntWriteEntry( p->pvFanins[id], best_j, idj );
    }
}
static inline void Abc_BddNandSortFaninAll( Abc_NandMan * p )
{
  int i, id;
  Vec_IntForEachEntry( p->vObjs, id, i )
    Abc_BddNandSortFanin( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_BddNandBuild( Abc_NandMan * p, int id )
{
  int j, idj;
  unsigned Value = Abc_BddLitConst1();
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjGetBddFunc( p, idj ) );
      if ( Abc_BddLitIsInvalid( Value ) ) return 1;
    }
  Abc_BddNandObjSetBddFunc( p, id, Abc_BddLitNot( Value ) );
  return 0;
}
static inline int Abc_BddNandBuildAll( Abc_NandMan * p )
{
  int i, id;
  Vec_IntForEachEntry( p->vObjs, id, i )
    if ( Abc_BddNandBuild( p, id ) ) return 1;
  return 0;
}
static inline int Abc_BddNandBuildFanoutCone( Abc_NandMan * p, int startId )
{ // including startId itself
  int i, id;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  Vec_IntPush( targets, startId );
  Abc_BddNandDescendantSortedList( p, p->pvFanouts, targets, startId );
  Vec_IntForEachEntry( targets, id, i )
    if ( Abc_BddNandBuild( p, id ) )
      {
	Vec_IntFree( targets );
	return 1;
      }
  Vec_IntFree( targets );
  return 0;
}
static inline int Abc_BddNandCheck( Abc_NandMan * p )
{
  int i, j, id, idj;
  unsigned Value;
  Vec_IntForEachEntry( p->vObjs, id, i )
    {
      Value = Abc_BddLitConst1();
      Vec_IntForEachEntry( p->pvFanins[id], idj, j )
	Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjGetBddFunc( p, idj ) );
      if ( !Abc_BddLitIsEq( Abc_BddNandObjGetBddFunc( p, id ), Abc_BddLitNot( Value ) ) )
	{
	  printf( "error : different at %d %10u %10u\n", id, Abc_BddNandObjGetBddFunc( p, id ), Abc_BddLitNot( Value ) );
	  return 1;
	}
    }
  return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_BddNandCspfG( Abc_NandMan * p, int id )
{
  int j, idj, index;
  unsigned c;
  p->pGFuncs[id] = Abc_BddLitConst1();
  Vec_IntForEachEntry( p->pvFanouts[id], idj, j )
    {
      if ( Abc_BddNandObjIsPo( p, idj ) )
	p->pGFuncs[id] = Abc_BddAnd( p->pBdd, p->pGFuncs[id], p->pGFuncs[idj] );
	// pGFuncs[idj] will be 0 unless external don't care of po is given.
      else
	{
	  index = Vec_IntFind( p->pvFanins[idj], id );
	  c = (unsigned)Vec_IntEntry( p->pvCFuncs[idj], index );
	  p->pGFuncs[id] = Abc_BddAnd( p->pBdd, p->pGFuncs[id], c );
	}
    }
  if ( Abc_BddLitIsInvalid( p->pGFuncs[id] ) ) return 1;
  return 0;
}
static inline int Abc_BddNandCspfC( Abc_NandMan * p, int id ) {
  int j, k, idj, idk;
  unsigned fanins, fi, fj, already1, c, dc1;
  if ( p->pvCFuncs[id] )
    Vec_IntFree( p->pvCFuncs[id] );
  p->pvCFuncs[id] = Vec_IntAlloc( Vec_IntSize( p->pvFanins[id] ) );
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      fanins = Abc_BddLitConst1();
      Vec_IntForEachEntryStart( p->pvFanins[id], idk, k, j + 1 )
	fanins = Abc_BddAnd( p->pBdd, fanins, Abc_BddNandObjGetBddFunc( p, idk ) );
      if ( Abc_BddLitIsInvalid( fanins ) ) return 1;
      fi = Abc_BddNandObjGetBddFunc( p, id );
      fj = Abc_BddNandObjGetBddFunc( p, idj );
      already1 = Abc_BddAnd( p->pBdd, fi, fj );
      if ( Abc_BddLitIsInvalid( already1 ) ) return 1;
      c = Abc_BddOr( p->pBdd, p->pGFuncs[id], Abc_BddLitNot( fanins ) );
      if ( Abc_BddLitIsInvalid( c ) ) return 1;
      c = Abc_BddOr( p->pBdd, c, already1 );
      if ( Abc_BddLitIsInvalid( c ) ) return 1;
      dc1 = Abc_BddOr( p->pBdd, fj, c );
      if ( Abc_BddLitIsInvalid( dc1 ) ) return 1;
      if ( Abc_BddLitIsConst1( dc1 ) )
	{
	  Abc_BddNandDisconnect( p, idj, id );
	  if ( Vec_IntSize( p->pvFanins[id] ) == 0 )
	    {
	      Vec_IntForEachEntry( p->pvFanouts[id], idk, k )
		if ( Vec_IntFind( p->pvFanins[idk], Abc_BddNandConst0() ) == -1 )
		  Abc_BddNandConnect( p, Abc_BddNandConst0(), idk, 0 );
	      Abc_BddNandRemoveNode( p, id );
	      return 0;
	    }
	  j--;
	  continue;
	}
      Vec_IntPush( p->pvCFuncs[id], c );
    }
  return 0;
}
static inline int Abc_BddNandCspf( Abc_NandMan * p )
{
  int i, id;
  Vec_IntForEachEntryReverse( p->vObjs, id, i )
    {
      if ( Vec_IntSize( p->pvFanouts[id] ) == 0 )
	{
	  Abc_BddNandRemoveNode( p, id );
	  continue;
	}
      if ( Abc_BddNandCspfG( p, id ) ) return 1;
      if ( Abc_BddNandCspfC( p, id ) ) return 1;
    }
  return Abc_BddNandBuildAll( p );
}
static inline int Abc_BddNandCspfFaninCone( Abc_NandMan * p, int startId )
{
  int i, id;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  if ( Abc_BddNandCspfC( p, startId ) ) return 1;
  Abc_BddNandDescendantSortedList( p, p->pvFanins, targets, startId );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Vec_IntSize( p->pvFanouts[id] ) == 0 )
	{
	  Abc_BddNandRemoveNode( p, id );
	  continue;
	}
      if ( Abc_BddNandCspfG( p, id ) ) return 1;
      if ( Abc_BddNandCspfC( p, id ) ) return 1;
    }
  Vec_IntFree( targets );
  return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_BddNandTryConnect( Abc_NandMan * p, int fanin, int fanout )
{
  if ( Vec_IntFind( p->pvFanins[fanout], fanin ) != -1 ) return 0; // already connected
  unsigned ffanin = Abc_BddNandObjGetBddFunc( p, fanin );
  unsigned ffanout = Abc_BddNandObjGetBddFunc( p, fanout );
  unsigned gfanout = p->pGFuncs[fanout];
  unsigned connectable = Abc_BddOr( p->pBdd, ffanout, gfanout );
  if( Abc_BddLitIsInvalid( connectable ) ) return -1;
  connectable = Abc_BddOr( p->pBdd, ffanin, connectable );
  if ( Abc_BddLitIsConst1( connectable ) )
    {
      Abc_BddNandConnect( p, fanin, fanout, 1 );
      return 1;
    }
  return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandRefresh( Abc_NandMan * p )
{
  if ( p->nVerbose > 1 ) printf( "Refresh\n" );
  abctime clk0 = Abc_Clock();
  Abc_BddManFree( p->pBdd );
  p->pBdd = Abc_BddManAlloc( Vec_IntSize( p->vPis ), 1 << p->nMem, (int)( p->nVerbose > 2 ) );
  // TODO : error handling
  if ( p->pDc != NULL ) Abc_BddNandDc( p );
  int out = 0;
  out += Abc_BddNandBuildAll( p );
  out += Abc_BddNandCspf( p );
  assert( !out );
  if ( p->nVerbose > 1 ) ABC_PRT( "Refresh took", Abc_Clock() - clk0 );
}
static inline void Abc_BddNandRefreshIfNeeded( Abc_NandMan * p )
{
  if ( Abc_BddIsLimit( p->pBdd ) )
    Abc_BddNandRefresh( p );
}

static inline void Abc_BddNandBuild_Refresh( Abc_NandMan * p, int id ) { if ( Abc_BddNandBuild( p, id ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandBuildAll_Refresh( Abc_NandMan * p ) { if ( Abc_BddNandBuildAll( p ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandBuildFanoutCone_Refresh( Abc_NandMan * p, int startId ) { if ( Abc_BddNandBuildFanoutCone( p, startId ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandCspfC_Refresh( Abc_NandMan * p, int id ) { if ( Abc_BddNandCspfC( p, id ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandCspf_Refresh( Abc_NandMan * p ) { if ( Abc_BddNandCspf( p ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandCspfFaninCone_Refresh( Abc_NandMan * p, int startId ) { if ( Abc_BddNandCspfFaninCone( p, startId ) ) Abc_BddNandRefresh( p ); }
static inline int Abc_BddNandTryConnect_Refresh( Abc_NandMan * p, int fanin, int fanout )
{
  int c = Abc_BddNandTryConnect( p, fanin, fanout );
  if ( c == -1 )
    {
      Abc_BddNandRefresh( p );
      if ( Abc_BddNandObjIsEmptyOrDead( p, fanin ) ) return 0;
      if ( Abc_BddNandObjIsEmptyOrDead( p, fanout ) ) return 0;
      c = Abc_BddNandTryConnect( p, fanin, fanout );
    }
  return c;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandCspfEager( Abc_NandMan * p )
{
  int wires = 0;
  while ( wires != Abc_BddNandCountWire( p ) )
    {
      wires = Abc_BddNandCountWire( p );
      Abc_BddNandRankAll( p );
      Abc_BddNandSortFaninAll( p );
      Abc_BddNandCspf_Refresh( p );
    }
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandG1EagerReduce( Abc_NandMan * p, int id, int idj )
{
  int wire =  Abc_BddNandCountWire( p );
  Abc_BddNandCspfFaninCone_Refresh( p, id );
  if ( wire == Abc_BddNandCountWire( p ) )
    {
      Abc_BddNandDisconnect( p, idj, id );
      Abc_BddNandBuildFanoutCone_Refresh( p, id );
      if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) return;
      Abc_BddNandCspfFaninCone_Refresh( p, id );
      return;
    }
  Abc_BddNandBuildAll_Refresh( p );
  Abc_BddNandCspfEager( p );
}
static inline void Abc_BddNandG1WeakReduce( Abc_NandMan * p, int id, int idj )
{
  int wire =  Abc_BddNandCountWire( p );
  Abc_BddNandCspfC_Refresh( p, id );
  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ||
       Abc_BddNandObjIsEmptyOrDead( p, idj ) )
    return; // If this, we don't need to do below.
  if ( wire == Abc_BddNandCountWire( p ) )
    Abc_BddNandDisconnect( p, idj, id );
  Abc_BddNandBuild_Refresh( p, id );
}
static inline void Abc_BddNandG1( Abc_NandMan * p, int fWeak )
{
  int i, j, id, idj;
  Vec_Int_t * targets, * fanouts;
  targets = Vec_IntDup( p->vObjs );
  fanouts = Vec_IntAlloc( 1 );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) continue;
      if ( p->nVerbose > 1 )
	printf( "G1 for %d in %d gates\n", i, Vec_IntSize(targets) );
      Vec_IntClear( fanouts );
      Abc_BddNandDescendantList_rec( p->pvFanouts, fanouts, id );
      // try connecting pi
      Vec_IntForEachEntry( p->vPis, idj, j )
	{
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) break;
	  if ( Abc_BddNandTryConnect_Refresh( p, idj, id ) == 1 )
	    {
	      if ( fWeak ) Abc_BddNandG1WeakReduce( p, id, idj );	
	      else Abc_BddNandG1EagerReduce( p, id, idj );
	    }
	}
      // try connecting candidate
      Vec_IntForEachEntry( targets, idj, j )
	{
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) break;
	  if ( Abc_BddNandObjIsEmptyOrDead( p, idj ) ) continue;
	  if ( id == idj ) continue;
	  if ( Vec_IntFind( fanouts, idj ) != -1 ) continue;
	  if ( Abc_BddNandTryConnect_Refresh( p, idj, id ) == 1 )
	    {
	      if ( fWeak ) Abc_BddNandG1WeakReduce( p, id, idj );
	      else Abc_BddNandG1EagerReduce( p, id, idj );
	    }
	}
      // recalculate fanouts for option
      if ( fWeak )
	{
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) continue;
	  Abc_BddNandCspfFaninCone_Refresh( p, id );
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) continue;
	  Abc_BddNandBuildAll_Refresh( p );
	}
    }
  Vec_IntFree( targets );
  Vec_IntFree( fanouts );
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandG3( Abc_NandMan * p )
{
  int i,j,k, id, idj, idk, out, wire, new_id;
  unsigned fi, fj, gi, gj, f1, f0, a, b, mergible, figj, fjgi, fx, gx, Value, eq;
  Vec_Int_t * targets, * fanouts;
  new_id = Vec_IntSize( p->vPis ) + 1;
  while ( !Abc_BddNandObjIsEmpty( p, new_id ) )
    {
      new_id++;
      // TODO : error handling
      assert( new_id < p->nObjsAlloc );
    }
  targets = Vec_IntDup( p->vObjs );
  fanouts = Vec_IntAlloc( 1 );
  // optimize
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( i == 0 ) break;
      for ( j = i - 1; (j >= 0) && (((idj) = Vec_IntEntry(targets, j)), 1); j-- )
	{ //  Vec_IntForEachEntryReverseStart(targets, idj, j, i - 1)
	  Abc_BddNandRefreshIfNeeded( p );
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) break;
	  if ( Abc_BddNandObjIsEmptyOrDead( p, idj ) ) continue;
	  if ( p->nVerbose > 1 )
	    printf( "G3 between %d %d in %d gates\n", i, j, Vec_IntSize(targets) );
	  fi = Abc_BddNandObjGetBddFunc( p, id );
	  fj = Abc_BddNandObjGetBddFunc( p, idj );
	  gi = p->pGFuncs[id];
	  gj = p->pGFuncs[idj];
	  // calculate intersection. if it is impossible, continue.
	  f1 = Abc_BddAnd( p->pBdd, fi, fj );
	  f0 = Abc_BddAnd( p->pBdd, Abc_BddLitNot( fi ), Abc_BddLitNot( fj ) );
	  if ( Abc_BddLitIsInvalid( f1 ) || Abc_BddLitIsInvalid( f0 ) ) continue;
	  a = Abc_BddOr( p->pBdd, f1, f0 );
	  if ( Abc_BddLitIsInvalid( a ) ) continue;
	  b = Abc_BddOr( p->pBdd, gi, gj );
	  if ( Abc_BddLitIsInvalid( b ) ) continue;
	  mergible = Abc_BddOr( p->pBdd, a, b );
	  if ( !Abc_BddLitIsConst1( mergible ) ) continue;
	  // create BDD of intersection. both F and G.
	  figj = Abc_BddAnd( p->pBdd, fi, gj );
	  if ( Abc_BddLitIsInvalid( figj ) ) continue;
	  fjgi = Abc_BddAnd( p->pBdd, fj, gi );
	  if ( Abc_BddLitIsInvalid( fjgi ) ) continue;
	  fx = Abc_BddOr( p->pBdd, figj, fjgi );
	  if ( Abc_BddLitIsInvalid( fx ) ) continue;
	  fx = Abc_BddOr( p->pBdd, fx, f1 );
	  if ( Abc_BddLitIsInvalid( fx ) ) continue;
	  gx = Abc_BddAnd( p->pBdd, gi, gj );
	  if ( Abc_BddLitIsInvalid( gx ) ) continue;
	  Abc_BddNandObjSetBddFunc( p, new_id, fx );
	  p->pGFuncs[new_id] = gx;
	  p->pvFanins[new_id] = Vec_IntAlloc( 1 );
	  p->pvFanouts[new_id] = Vec_IntAlloc( 1 );
	  // for all living nodes, if it is not included in fanouts of i and j, and i and j themselves, try connect it to new node.
	  Vec_IntClear( fanouts );
	  Abc_BddNandDescendantList_rec( p->pvFanouts, fanouts, id );
	  Abc_BddNandDescendantList_rec( p->pvFanouts, fanouts, idj );
	  Vec_IntPushUnique( fanouts, id );
	  Vec_IntPushUnique( fanouts, idj );
	  eq = Abc_BddOr( p->pBdd, Abc_BddLitNot( fx ), gx );
	  Value = Abc_BddLitConst1();
	  Vec_IntForEachEntry( p->vPis, idk, k ) 
	    if ( Abc_BddNandTryConnect( p, idk, new_id ) == 1 )
	      {
		if ( Abc_BddLitIsConst1( eq ) ) break;
		if ( Abc_BddLitIsInvalid( Value ) || Abc_BddLitIsInvalid( eq ) ) break;
		Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjGetBddFunc( p, idk ) );
		eq = Abc_BddOr( p->pBdd, eq, Abc_BddLitNot( Value ) );
	      }
	  Vec_IntForEachEntry( targets, idk, k )
	    {
	      if ( Abc_BddNandObjIsEmptyOrDead( p, idk ) ) continue;
	      if ( Vec_IntFind( fanouts, idj ) != -1 ) continue;
	      if ( Abc_BddNandTryConnect( p, idk, new_id ) == 1 )
		{
		  if ( Abc_BddLitIsConst1( eq ) ) break;
		  if ( Abc_BddLitIsInvalid( Value ) || Abc_BddLitIsInvalid( eq ) ) break;
		  Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjGetBddFunc( p, idk ) );
		  eq = Abc_BddOr( p->pBdd, eq, Abc_BddLitNot( Value ) );
		}
	    }
	  if ( Vec_IntSize( p->pvFanins[new_id] ) == 0 )
	    {
	      Abc_BddNandRemoveNode( p, new_id );
	      continue;
	    }
	  //	  assert( !Abc_BddNandCheck( p ) );
	  //	  assert( Abc_BddOr( p->pBdd, Abc_BddOr( p->pBdd, fx, gx ), Value ) == 1 );
	  // check the F of new node satisfies F and G.
	  if ( !Abc_BddLitIsConst1( eq ) ) {
	    Abc_BddNandRemoveNode( p, new_id );
	    continue;
	  }
	  //	  assert( Abc_BddOr( p->pBdd, Abc_BddOr( p->pBdd, fx^1, gx ), Value^1 ) == 1 );
	  // reduce the inputs
	  Abc_BddNandObjSetBddFunc( p, new_id, Abc_BddLitNot( Value ) );
	  p->pGFuncs[new_id] = Abc_BddAnd( p->pBdd, p->pGFuncs[id] ,p->pGFuncs[idj] );
	  if ( Abc_BddLitIsInvalid( p->pGFuncs[new_id] ) )
	    {
	      Abc_BddNandRemoveNode( p, new_id );	  
	      continue;
	    }
	  Vec_IntForEachEntry( p->pvFanouts[id], idk, k )
	    Abc_BddNandConnect( p, new_id, idk, 0 );
	  Vec_IntForEachEntry( p->pvFanouts[idj], idk, k )
	    if ( Vec_IntFind( p->pvFanouts[new_id], idk ) == -1 )
	      Abc_BddNandConnect( p, new_id, idk, 0 );
	  Abc_BddNandObjEntry( p, new_id );
	  Abc_BddNandSortFanin( p, new_id );
	  out = Abc_BddNandCspfC( p, new_id );
	  wire = Vec_IntSize( p->pvFanins[id] ) + Vec_IntSize( p->pvFanins[idj] );
	  if ( out || Vec_IntSize( p->pvFanins[new_id] ) > wire - 1 )
	    {
	      Abc_BddNandRemoveNode( p, new_id );
	      continue;
	    }
	  // if inputs < inputs_before - 1, do the followings
	  // remove merged (replaced) nodes
	  Abc_BddNandRemoveNode( p, id );
	  Abc_BddNandRemoveNode( p, idj );
	  // calculate function of new node
	  Abc_BddNandBuildFanoutCone_Refresh( p, new_id );
	  Abc_BddNandCspf_Refresh( p );
	  while ( !Abc_BddNandObjIsEmpty( p, new_id ) )
	    {
	      new_id++;
	      assert( new_id < p->nObjsAlloc );
	    }
	  break;
	}
    }
  Vec_IntFree( targets );
  Vec_IntFree( fanouts );
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandG1multi( Abc_NandMan * p, int fWeak )
{
  int i, j, id, idj;
  Vec_Int_t * targets, * targets2, * fanouts;
  targets = Vec_IntDup( p->vObjs );
  targets2 = Vec_IntAlloc( 1 );
  fanouts = Vec_IntAlloc( 1 );
  Vec_IntForEachEntryStart( p->vPos, id, i, Vec_IntSize( p->vPos ) / 2 )
    Abc_BddNandDescendantList_rec( p->pvFanins, targets2, id );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) continue;
      if ( p->nVerbose > 1 )
	printf( "G1-multi for %d in %d gates\n", i, Vec_IntSize(targets) );
      Vec_IntClear( fanouts );
      Abc_BddNandDescendantList_rec( p->pvFanouts, fanouts, id );
      Vec_IntForEachEntry( p->vPis, idj, j )
	{
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) break;
	  if ( Abc_BddNandTryConnect_Refresh( p, idj, id ) == 1 )
	    {
	      if ( fWeak ) Abc_BddNandG1WeakReduce( p, id, idj );	
	      else Abc_BddNandG1EagerReduce( p, id, idj );
	    }
	}
      Vec_IntForEachEntry( targets2, idj, j )
	{
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) break;
	  if ( Abc_BddNandObjIsEmptyOrDead( p, idj ) ) continue;
	  if ( id == idj ) continue;
	  if ( Vec_IntFind( fanouts, idj ) != -1 ) continue;
	  if ( Abc_BddNandTryConnect_Refresh( p, idj, id ) == 1 )
	    {
	      if ( fWeak ) Abc_BddNandG1WeakReduce( p, id, idj );
	      else Abc_BddNandG1EagerReduce( p, id, idj );
	    }
	}
      if ( fWeak )
	{
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) continue;
	  Abc_BddNandCspfFaninCone_Refresh( p, id );
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) continue;
	  Abc_BddNandBuildAll_Refresh( p );
	}
    }
  Vec_IntFree( targets );
  Vec_IntFree( targets2 );
  Vec_IntFree( fanouts );
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

p***********************************************************************/
static inline Gia_Man_t * Abc_BddNandNets2Gia( Vec_Ptr_t * vNets, Vec_Int_t * vPoCkts, Vec_Int_t * vPoIdxs, Vec_Int_t * vExternalCs, Gia_Man_t * pOld )
{
  Gia_Man_t * pNew, * pTemp;
  Gia_Obj_t * pObj;
  int i, j, k, id, idj, id0, id1, Value, cond;
  int * Values;
  int ** vvPoValues = ABC_CALLOC( int *, Vec_PtrSize( vNets ) + 1 );
  Abc_NandMan * p;
  pNew = Gia_ManStart( pOld->nObjs );
  pNew->pName = Abc_UtilStrsav( pOld->pName );
  pNew->pSpec = Abc_UtilStrsav( pOld->pSpec );
  Gia_ManHashAlloc( pNew );
  vvPoValues[0] = ABC_CALLOC( int, Gia_ManCiNum( pOld ) );
  Gia_ManForEachCi( pOld, pObj, i )
    vvPoValues[0][i] = Gia_ManAppendCi( pNew );
  Vec_PtrForEachEntryReverse( Abc_NandMan *, vNets, p, k )
    {
      Values = ABC_CALLOC( int, p->nObjsAlloc );
      vvPoValues[k+1] = ABC_CALLOC( int, Vec_IntSize( p->vPos ) );
      id = Abc_BddNandConst0();
      Values[id] = Abc_BddLitConst0();
      Vec_IntForEachEntry( p->vPis, id, i )
	Values[id] = vvPoValues[Vec_IntEntry( p->vPiCkts, i ) + 1][Vec_IntEntry( p->vPiIdxs, i )];
      Vec_IntForEachEntry( p->vObjs, id, i )
	{
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) continue;
	  if ( Vec_IntSize( p->pvFanins[id] ) == 1 )
	    {
	      id0 = Vec_IntEntry( p->pvFanins[id], 0 );
	      Values[id] = Abc_LitNot( Values[id0] );
	    }
	  else // if ( Vec_IntSize( p->pvFanins[id] ) >= 2 )
	    {
	      id0 = Vec_IntEntry( p->pvFanins[id], 0 );
	      id1 = Vec_IntEntry( p->pvFanins[id], 1 );
	      Values[id] = Gia_ManHashAnd( pNew, Values[id0], Values[id1] );
	      Vec_IntForEachEntryStart( p->pvFanins[id], idj, j, 2 )
		Values[id] = Gia_ManHashAnd( pNew, Values[id], Values[idj] );
	      Values[id] = Abc_LitNot( Values[id] );
	    }
	}
      Vec_IntForEachEntry( p->vPos, id, i )
	{
	  id0 = Vec_IntEntry( p->pvFanins[id], 0 );
	  Value = Values[id0];
	  vvPoValues[k+1][i] = Value;
	}
      ABC_FREE( Values );
    }
  Vec_IntForEachEntry( vExternalCs, cond, i )
    {
      Value = vvPoValues[Vec_IntEntry( vPoCkts, i ) + 1][Vec_IntEntry( vPoIdxs, i )];
      Gia_ManAppendCo( pNew, Abc_LitNotCond( Value, cond ) );
    }
  //    if ( p->pDc != NULL ) Gia_ManDupAppendShare( pNew, p->pDc );
  pNew = Gia_ManCleanup( pTemp = pNew );
  Gia_ManStop( pTemp );
  return pNew;
}
static inline void Abc_BddNandSetPoInfo( Gia_Man_t * pGia, Vec_Ptr_t * vNets, Vec_Ptr_t * vvPis, Vec_Ptr_t * vvPos, Vec_Int_t * vExternalPos, Vec_Int_t * vPoCkts, Vec_Int_t * vPoIdxs )
{
  int i, j, k, id;
  Gia_Obj_t * pObj;
  Vec_Int_t * vId, * vCkts, * vIdxs, * vPis, * vPos;
  Abc_NandMan * p;
  vId = Vec_IntAlloc( 1 );
  vCkts = Vec_IntAlloc( 1 );
  vIdxs = Vec_IntAlloc( 1 );
  // Generate Po list
  Gia_ManForEachCi( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      Vec_IntPush( vId, id );
      Vec_IntPush( vCkts, -1 );
      Vec_IntPush( vIdxs, i );
    }
  Vec_PtrForEachEntry( Vec_Int_t *, vvPos, vPos, j )
    Vec_IntForEachEntry( vPos, id, i )
    {
      Vec_IntPush( vId, id );
      Vec_IntPush( vCkts, j );
      Vec_IntPush( vIdxs, i );
    }
  // Assign Pi info
  Vec_PtrForEachEntry( Abc_NandMan *, vNets, p, j )
    {
      vPis = (Vec_Int_t *)Vec_PtrEntry( vvPis, j );
      Vec_IntForEachEntry( vPis, id, i )
	{
	  k = Vec_IntFind( vId, id );
	  Vec_IntPush( p->vPiCkts, Vec_IntEntry( vCkts, k ) );
	  Vec_IntPush( p->vPiIdxs, Vec_IntEntry( vIdxs, k ) );
	}
    }
  Vec_IntForEachEntry( vExternalPos, id, i )
    {
      k = Vec_IntFind( vId, id );
      Vec_IntPush( vPoCkts, Vec_IntEntry( vCkts, k ) );
      Vec_IntPush( vPoIdxs, Vec_IntEntry( vIdxs, k ) );
    }
  Vec_IntFree( vId );
  Vec_IntFree( vCkts );
  Vec_IntFree( vIdxs );
}
static inline int Abc_BddNandCountNewFanins( Gia_Man_t * pGia, Gia_Obj_t * pObj, int * pParts, int part )
{
  int id0, id1;
  Gia_Obj_t * pObj0, * pObj1;  
  pObj0 = Gia_ObjFanin0( pObj );
  id0 = Gia_ObjId( pGia, pObj0 );
  pObj1 = Gia_ObjFanin1( pObj );
  id1 = Gia_ObjId( pGia, pObj1 );
  return (int)(pParts[id0] != part) + (int)(pParts[id1] != part);
}
static inline void Abc_BddNandGia2Nets( Gia_Man_t * pOld, Vec_Ptr_t * vNets, Vec_Int_t * vPoCkts, Vec_Int_t * vPoIdxs, Vec_Int_t * vExternalCs, int nMem, int fDc, int nWindowSize, int nVerbose )
{
  int i, j, id, lit, newId, part;
  int * pFanouts, * pParts;
  Vec_Int_t * vPis, * vPos, * vTempPos, * vNodes, * vExternalPos, * vCands;
  Vec_Ptr_t * vvPis, * vvPos;
  Gia_Man_t * pGia, * pNew;
  Gia_Obj_t * pObj, * pObj0, * pObj1;
  Abc_NandMan * p;
  pGia = Gia_ManDup ( pOld );
  pFanouts = ABC_CALLOC( int, pGia->nObjs );
  pParts = ABC_CALLOC( int, pGia->nObjs );
  // TODO : error handling
  assert( pFanouts );
  assert( pParts );
  Abc_BddGiaCountFanout( pGia, pFanouts );
  vExternalPos = Vec_IntAlloc( 1 );
  vCands = Vec_IntAlloc( 1 );
  vvPis = Vec_PtrAlloc( 1 );
  vvPos = Vec_PtrAlloc( 1 );
  vTempPos = Vec_IntAlloc( 1 );
  vNodes = Vec_IntAlloc( 1 );
  // get po information
  Gia_ManForEachCo( pGia, pObj, i )
    {
      Vec_IntPush( vExternalCs, Gia_ObjFaninC0( pObj ) );
      pObj = Gia_ObjFanin0( pObj );
      id = Gia_ObjId( pGia, pObj );
      Vec_IntPush( vExternalPos, id );
      if ( Gia_ObjIsConst0( pObj ) || Gia_ObjIsCi( pObj ) ) continue;
      pFanouts[id]--;
      Vec_IntPush( vCands, id );
    }
  // Partition
  part = 0;
  while ( 1 )
    {
      part++;
      vPis = Vec_IntAlloc( 1 );
      vPos = Vec_IntAlloc( 1 );
      Vec_IntClear( vTempPos );
      Vec_IntClear( vNodes );
      while ( 1 )
	{
	  newId = Abc_BddNandConst0();
	  Vec_IntForEachEntry( vPis, id, i )
	    { pObj = Gia_ManObj( pGia, id );
	      if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) &&
		   pFanouts[id] == 0 && Abc_BddNandCountNewFanins( pGia, pObj, pParts, part ) == 0 )
		{ newId = id; Vec_IntDrop( vPis, i ); break; } }
	  if ( newId == Abc_BddNandConst0() )
	    Vec_IntForEachEntry( vPis, id, i )
	      { pObj = Gia_ManObj( pGia, id );
		if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) &&
		     pFanouts[id] == 0 && Abc_BddNandCountNewFanins( pGia, pObj, pParts, part ) == 1 )
		  { newId = id; Vec_IntDrop( vPis, i ); break; } }
	  if ( newId == Abc_BddNandConst0() )
	    Vec_IntForEachEntry( vPis, id, i )
	      { pObj = Gia_ManObj( pGia, id );
		if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) && pFanouts[id] == 0 )
		  { newId = id; Vec_IntDrop( vPis, i ); break; } }
	  if ( newId == Abc_BddNandConst0() )
	    Vec_IntForEachEntry( vCands, id, i )
	      { pObj = Gia_ManObj( pGia, id );
		if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) &&
		     pFanouts[id] == 0 && Abc_BddNandCountNewFanins( pGia, pObj, pParts, part ) == 0 )
		  { newId = id; break; } }
	  if ( newId == Abc_BddNandConst0() )
	    Vec_IntForEachEntry( vCands, id, i )
	      { pObj = Gia_ManObj( pGia, id );
		if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) &&
		     pFanouts[id] == 0 && Abc_BddNandCountNewFanins( pGia, pObj, pParts, part ) == 1 )
		  { newId = id; break; } }
	  if ( newId == Abc_BddNandConst0() )
	    Vec_IntForEachEntry( vCands, id, i )
	      { pObj = Gia_ManObj( pGia, id );
		if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) && pFanouts[id] == 0 )
		  { newId = id; break; } }
	  if ( newId == Abc_BddNandConst0() ) break;
	  i = Vec_IntFind( vCands, newId );
	  if ( i != -1 )
	    {
	      Vec_IntDrop( vCands, i );
	      Vec_IntPush( vPos, newId );
	      lit = Gia_Obj2Lit( pGia, pObj );
	      lit = Gia_ManAppendCo( pGia, lit );
	      pObj = Gia_Lit2Obj( pGia, lit );
	      id = Gia_ObjId( pGia, pObj );
	      Vec_IntPush( vTempPos, id );
	    }
	  Vec_IntPush( vNodes, newId );
	  pObj = Gia_ManObj( pGia, newId );
	  pObj0 = Gia_ObjFanin0( pObj );
	  id = Gia_ObjId( pGia, pObj0 );
	  if ( !Gia_ObjIsCi( pObj0 ) ) pFanouts[id]--;
	  assert( pFanouts[id] >= 0 );
	  if ( pParts[id] != part )
	    {
	      pParts[id] = part;
	      Vec_IntPush( vPis, id );
	    }
	  pObj1 = Gia_ObjFanin1( pObj );
	  id = Gia_ObjId( pGia, pObj1 );
	  if ( !Gia_ObjIsCi( pObj1 ) ) pFanouts[id]--;
	  assert( pFanouts[id] >= 0 );
	  if ( pParts[id] != part )
	    {
	      pParts[id] = part;
	      Vec_IntPush( vPis, id );
	    }
	  if ( Vec_IntSize( vNodes ) >= nWindowSize ) break;
	  if ( Vec_IntSize( vPis ) > 100 ) break;
	}
      Vec_IntSort( vNodes, 0 );
      pNew = Gia_ManDupFromVecs( pGia, vPis, vNodes, vTempPos, 0 );
      // TODO : fDC
      p = Abc_BddNandManAlloc( pNew, nMem, 0, (int)( nVerbose > 2 ) );
      Vec_PtrPush( vNets, p );
      Vec_PtrPush( vvPis, vPis );
      Vec_PtrPush( vvPos, vPos );
      Vec_IntForEachEntry( vPis, id, i )
	Vec_IntPushUnique( vCands, id );
      if ( newId == Abc_BddNandConst0() ) break;
    }
  // create map to inputs
  Abc_BddNandSetPoInfo( pGia, vNets, vvPis, vvPos, vExternalPos, vPoCkts, vPoIdxs );
  Gia_ManStop( pGia );
  ABC_FREE( pFanouts );
  ABC_FREE( pParts );
  Vec_IntFree( vExternalPos );
  Vec_IntFree( vCands );
  Vec_IntFree( vTempPos );
  Vec_IntFree( vNodes );
  Vec_PtrForEachEntry( Vec_Int_t *, vvPis, vPis, i )
    Vec_IntFree( vPis );
  Vec_PtrFree( vvPis );
  Vec_PtrForEachEntry( Vec_Int_t *, vvPos, vPos, i )
    Vec_IntFree( vPos );
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandPrintStats( Abc_NandMan * p, char * prefix, abctime clk0 )
{
  printf( "\r%-10s: gates = %5d, wires = %5d, AIG node = %5d", prefix, Vec_IntSize( p->vObjs ), Abc_BddNandCountWire( p ), Abc_BddNandCountWire( p ) - Vec_IntSize( p->vObjs ) );
  ABC_PRT( ", time ", Abc_Clock() - clk0 );
}
Gia_Man_t * Abc_BddNandGiaTest( Gia_Man_t * pGia, int nMem, int nType, int fRep, int fDc, int nWindowSize, int nVerbose )
{
  int i, id;
  Abc_NandMan * p;
  Gia_Obj_t * pObj;
  Vec_Ptr_t * vNets;
  Vec_Int_t * vPoCkts, * vPoIdxs, * vExternalCs;
  vNets = Vec_PtrAlloc( 1 );
  vPoCkts = Vec_IntAlloc( 1 );
  vPoIdxs = Vec_IntAlloc( 1 );
  vExternalCs = Vec_IntAlloc( 1 );
  if ( nWindowSize == 0 )
    {
      p = Abc_BddNandManAlloc( pGia, nMem, fDc, nVerbose );
      Vec_IntForEachEntry( p->vPis, id, i )
	{
	  Vec_IntPush( p->vPiCkts, -1 );
	  Vec_IntPush( p->vPiIdxs, i );
	}
      Vec_PtrPush( vNets, p );
      Gia_ManForEachCo( pGia, pObj, i )
	{
	  Vec_IntPush( vExternalCs, 0 );
	  Vec_IntPush( vPoCkts, 0 );
	  Vec_IntPush( vPoIdxs, i );
	}
    }
  else
    Abc_BddNandGia2Nets( pGia, vNets, vPoCkts, vPoIdxs, vExternalCs, nMem, fDc, nWindowSize, nVerbose );
  // optimize
  abctime clk0 = Abc_Clock();
  Vec_PtrForEachEntry( Abc_NandMan *, vNets, p, i )
    {
      // TODO : error handling
      assert( ( 1u << p->nMem ) > Vec_IntSize( p->vPis ) + 2 );
      p->pBdd = Abc_BddManAlloc( Vec_IntSize( p->vPis ), 1 << p->nMem, (int)( nVerbose > 2 ) );
      if ( p->pDc != NULL ) Abc_BddNandDc( p );
      assert( !Abc_BddNandBuildAll( p ) );
      if ( nVerbose ) Abc_BddNandPrintStats( p, "initial", clk0 );
      Abc_BddNandCspfEager( p );
      if ( nVerbose ) Abc_BddNandPrintStats( p, "cspf", clk0 );
      // TODO : mspf
      int wire = 0;
      while ( wire != Abc_BddNandCountWire( p ) )
	{
	  wire = Abc_BddNandCountWire( p );
	  switch ( nType ) {
	  case 0:
	    break;
	  case 1:
	    Abc_BddNandG1( p, 0 );
	    if ( nVerbose ) Abc_BddNandPrintStats( p, "g1", clk0 );
	    break;
	  case 2:
	    Abc_BddNandG1( p, 1 );
	    if ( nVerbose ) Abc_BddNandPrintStats( p, "g1-weak", clk0 );
	    break;
	  case 3:
	    Abc_BddNandG3( p );
	    if ( nVerbose ) Abc_BddNandPrintStats( p, "g3", clk0 );
	    break;
	  case 4:
	    Abc_BddNandG1multi( p, 0 );
	    if ( nVerbose ) Abc_BddNandPrintStats( p, "g1-multi", clk0 );
	    break;
	  default:
	    assert( 0 );
	  }
	  Abc_BddNandCspfEager( p );
	  if ( !fRep ) break;
	}
    }
  if ( nVerbose ) ABC_PRT( "total ", Abc_Clock() - clk0 );
  Gia_Man_t * pNew = Abc_BddNandNets2Gia( vNets, vPoCkts, vPoIdxs, vExternalCs, pGia );
  Vec_IntFree( vPoCkts );
  Vec_IntFree( vPoIdxs );
  Vec_IntFree( vExternalCs );
  Vec_PtrForEachEntry( Abc_NandMan *, vNets, p, i )
    Abc_BddNandManFree( p );
  Vec_PtrFree( vNets );
  return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

