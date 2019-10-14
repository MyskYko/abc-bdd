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
  int nObjs;
  Vec_Int_t * pis;
  Vec_Int_t * pos;
  Vec_Int_t ** faninList;
  Vec_Int_t ** fanoutList;
  int * newNodeValues;
  Vec_Int_t * livingNodes;
  int * rank;
  unsigned * G;
  Vec_Int_t ** C;
  Abc_BddMan * pBdd;
  char * filename;
  int nMem;
  int nVerbose;
  int fDc;
};

static inline int      Abc_BddNandCompl( Abc_NandMan * p, int id )    { return id + p->nGiaObjs;                }
static inline int      Abc_BddNandIsPiNode( Abc_NandMan * p, int id ) { return (int)( p->faninList[id] == 0 );  }
static inline int      Abc_BddNandIsPoNode( Abc_NandMan * p, int id ) { return (int)( p->fanoutList[id] == 0 ); }
static inline unsigned Abc_BddNandObjValue( Abc_NandMan * p, int id ) { return p->newNodeValues[id];            }
static inline void     Abc_BddNandObjValueWrite( Abc_NandMan * p, int id, unsigned Value ) { p->newNodeValues[id] = Value; }
static inline int      Abc_BddNandCount0s( Abc_NandMan * p, int id, int nOverflow ) { return Abc_BddCount0s( p->pBdd, Abc_BddNandObjValue( p, id ), nOverflow ); }
static inline int      Abc_BddNandIsEmptyNode( Abc_NandMan * p, int id ) { return (int)( p->faninList[id] == 0 && p->fanoutList[id] == 0 ); }
static inline int      Abc_BddNandIsDeadNode( Abc_NandMan * p, int id ) { return (int)( Vec_IntSize( p->fanoutList[id] ) == 0 ); }
static inline int      Abc_BddNandIsEmptyOrDeadNode( Abc_NandMan * p, int id ) { return ( Abc_BddNandIsEmptyNode( p, id ) || Abc_BddNandIsDeadNode( p, id ) ); }

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
  int idj; int j, k;
  Vec_IntForEachEntry( children[id], idj, j )
    {
      k = Vec_IntFind( list, idj );
      if ( k == -1 && children[idj] != 0 )
	{ // idj is not in list and is not leaf
	  Vec_IntPush( list, idj );
	  Abc_BddNandDescendantList_rec( children, list, idj );
	}
    }
}
static inline void Abc_BddNandDescendantSortedList( Abc_NandMan * p, Vec_Int_t ** children, Vec_Int_t * sortedList, int parent )
{
  int id; int i;
  int index;
  Vec_Int_t * list = Vec_IntAlloc( 1 );
  Abc_BddNandDescendantList_rec( children, list, parent );
  Vec_IntForEachEntry( p->livingNodes, id, i )
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
void Abc_BddNandInsertLivingNode( Abc_NandMan * p, int id )
{
  int index_, index = Vec_IntSize( p->livingNodes );
  int idj; int j;
  Vec_IntForEachEntry( p->fanoutList[id], idj, j )
    {
      index_ = Vec_IntFind( p->livingNodes, idj );
      if ( index_ != -1 && index_ < index ) index = index_;
    }
  Vec_IntInsert( p->livingNodes, index, id );
  Vec_IntForEachEntry( p->faninList[id], idj, j )
    {
      index_ = Vec_IntFind( p->livingNodes, idj );
      if ( index_ > index )
	{
	  Vec_IntDrop( p->livingNodes, index_ );
	  Abc_BddNandInsertLivingNode( p, idj );
	  index = Vec_IntFind( p->livingNodes, id );
	}
    }
}
static inline void Abc_BddNandConnect( Abc_NandMan * p, int fanin, int fanout, int fSort )
{ // uniqueness of conenction must be confirmed beforehand
  Vec_IntPush( p->faninList[fanout], fanin );    
  Vec_IntPush( p->fanoutList[fanin], fanout );
  if ( fSort )
    {
      int index_fanout = Vec_IntFind( p->livingNodes, fanout );
      int index_fanin = Vec_IntFind( p->livingNodes, fanin );
      if ( index_fanout != -1 && index_fanout < index_fanin )
	{ // Omit the case fanout is not in livingNodes for G3, and sort.
	  Vec_IntDrop( p->livingNodes, index_fanin );
	  Abc_BddNandInsertLivingNode( p, fanin );
	}
    }
}
static inline void Abc_BddNandDisconnect( Abc_NandMan * p, int fanin, int fanout )
{
  Vec_IntRemove( p->faninList[fanout], fanin );    
  Vec_IntRemove( p->fanoutList[fanin], fanout );
}
static inline void Abc_BddNandRemoveNode( Abc_NandMan * p, int id )
{
  int j; int idj;
  Vec_IntForEachEntry( p->faninList[id], idj, j ) Vec_IntRemove( p->fanoutList[idj], id );
  Vec_IntForEachEntry( p->fanoutList[id], idj, j ) Vec_IntRemove( p->faninList[idj], id );
  Vec_IntFree( p->faninList[id] );
  Vec_IntFree( p->fanoutList[id] );
  p->faninList[id] = 0;
  p->fanoutList[id] = 0;
  Vec_IntRemove( p->livingNodes, id );
}
static inline int Abc_BddNandCountWire( Abc_NandMan * p )
{
  int i; int id;
  int count = 0;
  Vec_IntForEachEntry( p->livingNodes, id, i ) count += Vec_IntSize( p->faninList[id] );
  return count;
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandGenNet( Abc_NandMan * p, Gia_Man_t * pGia )
{
  Gia_Obj_t * pObj, * pObj0, * pObj1;
  int i; int id, idj, id0, id1;
  // constant
  id = 0;
  p->newNodeValues[id] = Abc_BddLitConst0();
  p->faninList[id] = 0;
  p->fanoutList[id] = Vec_IntAlloc( 1 );
  idj = Abc_BddNandCompl( p, id );
  p->newNodeValues[idj] = Abc_BddLitConst1();
  p->faninList[idj] = 0;
  p->fanoutList[idj] = Vec_IntAlloc( 1 );
  // pi
  Gia_ManForEachCi( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      p->newNodeValues[id] = Abc_BddLitIthVar( i );
      p->faninList[id] = 0;
      p->fanoutList[id] = Vec_IntAlloc( 1 );
      Vec_IntPush( p->pis, id );
      idj = Abc_BddNandCompl( p, id );
      p->newNodeValues[idj] = Abc_BddLitNot( Abc_BddLitIthVar( i ) );
      p->faninList[idj] = Vec_IntAlloc( 1 );
      p->fanoutList[idj] = Vec_IntAlloc( 1 );
      Vec_IntPush( p->livingNodes, idj );
      Abc_BddNandConnect( p, id, idj, 0 );
    }
  // gate
  Gia_ManForEachAnd( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      p->faninList[id] = Vec_IntAlloc( 1 );
      p->fanoutList[id] = Vec_IntAlloc( 1 );
      pObj0 = Gia_ObjFanin0( pObj );
      pObj1 = Gia_ObjFanin1( pObj );
      id0 = Gia_ObjId( pGia, pObj0 );
      id1 = Gia_ObjId( pGia, pObj1 );
      if ( (  Gia_ObjIsCi( pObj0 ) &&  Gia_ObjFaninC0( pObj ) ) ||
	   ( !Gia_ObjIsCi( pObj0 ) && !Gia_ObjFaninC0( pObj ) ) )
	id0 = Abc_BddNandCompl( p, id0 );
      Abc_BddNandConnect( p, id0, id, 0 );
      if ( (  Gia_ObjIsCi( pObj1 ) &&  Gia_ObjFaninC1( pObj ) ) ||
	   ( !Gia_ObjIsCi( pObj1 ) && !Gia_ObjFaninC1( pObj ) ) )  
	id1 = Abc_BddNandCompl( p, id1 );
      Abc_BddNandConnect( p, id1, id, 0 );
      Vec_IntPush( p->livingNodes, id );
      // create inverter
      idj = Abc_BddNandCompl( p, id );
      p->faninList[idj] = Vec_IntAlloc( 1 );
      p->fanoutList[idj] = Vec_IntAlloc( 1 );
      Abc_BddNandConnect( p, id, idj, 0 );
      Vec_IntPush( p->livingNodes, idj );    
    }
  // po
  Gia_ManForEachCo( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      p->faninList[id] = Vec_IntAlloc( 1 );
      p->fanoutList[id] = 0;
      pObj0 = Gia_ObjFanin0( pObj );
      id0 = Gia_ObjId( pGia, pObj0 );
      if ( (  ( id0 == 0 || Gia_ObjIsCi( pObj0 ) ) &&  Gia_ObjFaninC0( pObj ) ) ||
	   ( !( id0 == 0 || Gia_ObjIsCi( pObj0 ) ) && !Gia_ObjFaninC0( pObj ) ) )
	id0 = Abc_BddNandCompl( p, id0 );
      Abc_BddNandConnect( p, id0, id, 0 );
      Vec_IntPush( p->pos, id );
    }
  // remove redundant nodes
  Vec_IntForEachEntry( p->livingNodes, id, i )
    if ( Vec_IntSize( p->fanoutList[id] ) == 0 ) Abc_BddNandRemoveNode( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_NandMan * Abc_BddNandManAlloc( Gia_Man_t * pGia, char * Filename, int nMem, int fDc, int nVerbose )
{
  Abc_NandMan * p = ABC_CALLOC( Abc_NandMan, 1 );
  p->nGiaObjs = pGia->nObjs;
  p->nObjs = pGia->nObjs + pGia->nObjs;
  p->pis = Vec_IntAlloc( Gia_ManCiNum( pGia ) );
  p->pos = Vec_IntAlloc( Gia_ManCoNum( pGia ) );
  p->faninList = ABC_CALLOC( Vec_Int_t *, p->nObjs );
  p->fanoutList = ABC_CALLOC( Vec_Int_t *, p->nObjs );
  p->newNodeValues = ABC_CALLOC( int, p->nObjs );
  p->livingNodes = Vec_IntAlloc( 1 );
  p->rank = ABC_CALLOC( int, p->nObjs );
  p->G = ABC_CALLOC( unsigned, p->nObjs );
  p->C = ABC_CALLOC( Vec_Int_t *, p->nObjs );
  p->filename = Filename;
  p->nMem = nMem;
  p->fDc = fDc;
  p->nVerbose = nVerbose;
  return p;
}
static inline void Abc_BddNandManFree( Abc_NandMan * p )
{
  int i;
  Vec_IntFree( p->pis );
  Vec_IntFree( p->pos );
  for ( i = 0; i < p->nObjs; i++ )
    {
      if ( p->faninList[i] != 0 ) Vec_IntFree( p->faninList[i] );
      if ( p->fanoutList[i] != 0 ) Vec_IntFree( p->fanoutList[i] );
    }
  ABC_FREE( p->faninList );
  ABC_FREE( p->fanoutList );
  ABC_FREE( p->newNodeValues );
  Vec_IntFree( p->livingNodes );
  ABC_FREE( p->rank );
  ABC_FREE( p->G );
  ABC_FREE( p->C );
  Abc_BddManFree( p->pBdd );
  ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandPrintNet( Abc_NandMan * p )
{
  int id, idj; int i, j, k;
  FILE *fp;
  fp = fopen( p->filename, "w" );
  fprintf( fp, ".model test\n" );
  fprintf( fp, ".inputs" );
  Vec_IntForEachEntry( p->pis, id, i )
    fprintf( fp, " pi%d", id - 1 );
  fprintf( fp, "\n.outputs" );
  Vec_IntForEachEntry( p->pos, id, i )
    fprintf( fp, " po%d", i );
  fprintf( fp, "\n" );
  fprintf( fp, ".names const0\n0\n" );
  fprintf( fp, ".names const1\n1\n" );
  Vec_IntForEachEntry( p->livingNodes, id, i )
    if ( p->faninList[id]                 != 0 &&
	 p->fanoutList[id]                != 0 &&
	 Vec_IntSize( p->faninList[id] )  != 0 &&
	 Vec_IntSize( p->fanoutList[id] ) != 0 )
      {
	fprintf( fp,".names " );
	Vec_IntForEachEntry( p->faninList[id], idj, j )
	  if ( idj == 0 )
	    fprintf( fp, "const0 " );	  
	  else if ( idj == Abc_BddNandCompl( p, 0 ) )
	    fprintf( fp, "const1 " );
	  else if ( idj <= Vec_IntSize( p->pis ) ) // assuming (id of pi <= num pi)
	    fprintf( fp, "pi%d ", idj - 1 );
	  else
	    fprintf( fp, "n%d ", idj );
	fprintf( fp, "n%d\n", id );
	for ( k = 0; k < Vec_IntSize( p->faninList[id] ); k++ ) 
	  fprintf( fp, "1" );
	fprintf( fp, " 0\n" );
      }
  Vec_IntForEachEntry( p->pos, id, i )
    {
      idj = Vec_IntEntry( p->faninList[id], 0 );
      fprintf( fp, ".names " );
      if ( idj == 0 )
	fprintf( fp, "const0 " );	  
      else if ( idj == Abc_BddNandCompl( p, 0 ) )
	fprintf( fp, "const1 " );
      else if ( idj <= Vec_IntSize( p->pis ) ) // assuming (id of pi <= num pi)
	fprintf( fp, "pi%d ", idj - 1 );
      else
	fprintf( fp, "n%d ", idj );
      fprintf( fp, "po%d\n", i );
      fprintf( fp, "1 1\n" );
    }
  fprintf( fp, ".end\n" );
  fflush( fp );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandRank( Abc_NandMan * p, int id )
{
  if ( Abc_BddNandIsPiNode( p, id ) )
    p->rank[id] = 1 << 30; // assume this is max
  else
    {
      if ( Vec_IntSize( p->pis ) <= 20 )
	{
	  p->rank[id] = Vec_IntSize( p->fanoutList[id] ) << Vec_IntSize( p->pis );
	  p->rank[id] += Abc_BddNandCount0s( p, id, 0 );
	}
      else
	{
	  int nOverflow = Vec_IntSize( p->pis ) - 20;
	  p->rank[id] = Vec_IntSize( p->fanoutList[id] ) << 20;
	  p->rank[id] += Abc_BddNandCount0s( p, id, nOverflow );
	}
    }
  assert( p->rank[id] >= 0 );
}
static inline void Abc_BddNandRankAll( Abc_NandMan * p )
{
  int id; int i;
  Vec_IntForEachEntry( p->pis, id, i ) Abc_BddNandRank( p, id );
  Vec_IntForEachEntry( p->livingNodes, id, i ) Abc_BddNandRank( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandSortFanin( Abc_NandMan * p, int id )
{
  int idj, idk; int j, k;
  int best_idj; int best_j;
  Vec_IntForEachEntry( p->faninList[id], idj, j )
    {
      best_j = j;
      best_idj = idj;
      Vec_IntForEachEntryStart( p->faninList[id], idk, k, j + 1 )
	if ( p->rank[idj] > p->rank[idk] )
	  {
	    best_j = k;
	    best_idj = idk;
	  }
      Vec_IntWriteEntry( p->faninList[id], j, best_idj );
      Vec_IntWriteEntry( p->faninList[id], best_j, idj );
    }
}
static inline void Abc_BddNandSortFaninAll( Abc_NandMan * p )
{
  int id;
  int i;
  Vec_IntForEachEntry( p->livingNodes, id, i ) Abc_BddNandSortFanin( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_BddNandBuild( Abc_NandMan * p, int id )
{
  int idj; int j;
  unsigned Value = Abc_BddLitConst1();
  Vec_IntForEachEntry( p->faninList[id], idj, j )
    {
      Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjValue( p, idj ) );
      if ( Abc_BddLitIsInvalid( Value ) ) return 1;
    }
  Abc_BddNandObjValueWrite( p, id, Abc_BddLitNot( Value ) );
  return 0;
}
static inline int Abc_BddNandBuildAll( Abc_NandMan * p )
{
  int id; int i;
  Vec_IntForEachEntry( p->livingNodes, id, i )
    if ( Abc_BddNandBuild( p, id ) ) return 1;
  return 0;
}
static inline int Abc_BddNandBuildFanoutCone( Abc_NandMan * p, int startId )
{ // including startId itself
  int id; int i;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  Vec_IntPush( targets, startId );
  Abc_BddNandDescendantSortedList( p, p->fanoutList, targets, startId );
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
  int id, idj; int i, j;
  unsigned Value;
  Vec_IntForEachEntry( p->livingNodes, id, i )
    {
      Value = Abc_BddLitConst1();
      Vec_IntForEachEntry( p->faninList[id], idj, j )
	Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjValue( p, idj ) );
      if ( !Abc_BddLitIsEq( Abc_BddNandObjValue( p, id ), Abc_BddLitNot( Value ) ) )
	{
	  printf( "error : different at %d %10u %10u\n", id, Abc_BddNandObjValue( p, id ), Abc_BddLitNot( Value ) );
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
  int j; int idj;
  int index;
  unsigned c;
  p->G[id] = 1;
  Vec_IntForEachEntry( p->fanoutList[id], idj, j )
    {
      if ( Abc_BddNandIsPoNode( p, idj ) )
	p->G[id] = Abc_BddAnd( p->pBdd, p->G[id], p->G[idj] );
	// G[idj] will be 0 unless external don't care of the po is given.
      else
	{
	  index = Vec_IntFind( p->faninList[idj], id );
	  c = (unsigned)Vec_IntEntry( p->C[idj], index );
	  p->G[id] = Abc_BddAnd( p->pBdd, p->G[id], c );
	}
    }
  if ( Abc_BddLitIsInvalid( p->G[id] ) ) return 1;
  return 0;
}
static inline int Abc_BddNandCspfC( Abc_NandMan * p, int id ) {
  int j, k;
  int idj, idk;
  unsigned fanins, fi, fj, already1, c, dc1;
  if ( p->C[id] != 0 ) Vec_IntFree( p->C[id] );
  p->C[id] = Vec_IntAlloc( Vec_IntSize( p->faninList[id] ) );
  Vec_IntForEachEntry( p->faninList[id], idj, j )
    {
      fanins = Abc_BddLitConst1();
      Vec_IntForEachEntryStart( p->faninList[id], idk, k, j + 1 )
	fanins = Abc_BddAnd( p->pBdd, fanins, Abc_BddNandObjValue( p, idk ) );
      if ( Abc_BddLitIsInvalid( fanins ) ) return 1;
      fi = Abc_BddNandObjValue( p, id );
      fj = Abc_BddNandObjValue( p, idj );
      already1 = Abc_BddAnd( p->pBdd, fi, fj );
      if ( Abc_BddLitIsInvalid( already1 ) ) return 1;
      c = Abc_BddOr( p->pBdd, p->G[id], Abc_BddLitNot( fanins ) );
      if ( Abc_BddLitIsInvalid( c ) ) return 1;
      c = Abc_BddOr( p->pBdd, c, already1 );
      if ( Abc_BddLitIsInvalid( c ) ) return 1;
      dc1 = Abc_BddOr( p->pBdd, fj, c );
      if ( Abc_BddLitIsInvalid( dc1 ) ) return 1;
      if ( Abc_BddLitIsConst1( dc1 ) )
	{
	  Abc_BddNandDisconnect( p, idj, id );
	  if ( Vec_IntSize( p->faninList[id] ) == 0 )
	    {
	      Vec_IntForEachEntry( p->fanoutList[id], idk, k )
		Abc_BddNandConnect( p, 0, idk, 0 ); // duplication of const0 inputs may happen
	      Abc_BddNandRemoveNode( p, id );
	      return 0;
	    }
	  j--;
	  continue;
	}
      Vec_IntPush( p->C[id], c );
    }
  return 0;
}
static inline int Abc_BddNandCspf( Abc_NandMan * p )
{
  int id; int i;
  Vec_IntForEachEntryReverse( p->livingNodes, id, i )
    {
      if ( Vec_IntSize( p->fanoutList[id] ) == 0 )
	{ // remove the node
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
  int id;
  int i;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  Abc_BddNandDescendantSortedList( p, p->faninList, targets, startId );
  //  Vec_IntPush( targets, startId );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Vec_IntSize( p->fanoutList[id] ) == 0 )
	{ // remove the node
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
static inline void Abc_BddNandRefresh( Abc_NandMan * p )
{
  assert( !p->fDc );
  if ( p->nVerbose > 1 ) printf( "Refresh\n");
  int out;
  abctime clk0 = Abc_Clock();
  Abc_BddManFree( p->pBdd );
  p->pBdd = Abc_BddManAlloc( Vec_IntSize( p->pis ), 1 << p->nMem, (int)( p->nVerbose > 2 ) );
  out = Abc_BddNandBuildAll( p );
  out += Abc_BddNandCspf( p );
  assert( !out );
  if ( p->nVerbose > 1 ) ABC_PRT( "Refresh took", Abc_Clock() - clk0 );
}
static inline void Abc_BddNandBuildRefresh( Abc_NandMan * p, int id ) { if ( Abc_BddNandBuild( p, id ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandBuildAllRefresh( Abc_NandMan * p ) { if ( Abc_BddNandBuildAll( p ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandBuildFanoutConeRefresh( Abc_NandMan * p, int startId ) { if ( Abc_BddNandBuildFanoutCone( p, startId ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandCspfCRefresh( Abc_NandMan * p, int id ) { if ( Abc_BddNandCspfC( p, id ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandCspfRefresh( Abc_NandMan * p ) { if ( Abc_BddNandCspf( p ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandCspfFaninConeRefresh( Abc_NandMan * p, int startId ) { if ( Abc_BddNandCspfFaninCone( p, startId ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandRefreshIfNeeded( Abc_NandMan * p )
{
  if ( Abc_BddIsLimit( p->pBdd ) ) Abc_BddNandRefresh( p );
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
      Abc_BddNandCspfRefresh( p );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_BddNandTryConnect( Abc_NandMan * p, int fanin, int fanout )
{
  if ( Vec_IntFind( p->faninList[fanout], fanin ) != -1 ) return 0; // already connected
  unsigned ffanin = Abc_BddNandObjValue( p, fanin );
  unsigned ffanout = Abc_BddNandObjValue( p, fanout );
  unsigned gfanout = p->G[fanout];
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
static inline int Abc_BddNandTryConnectRefreshing( Abc_NandMan * p, int fanin, int fanout )
{
  int c = Abc_BddNandTryConnect( p, fanin, fanout );
  if ( c == -1 )
    {
      Abc_BddNandRefresh( p );
      if ( Abc_BddNandIsEmptyOrDeadNode( p, fanin ) ) return 0;
      if ( Abc_BddNandIsEmptyOrDeadNode( p, fanout ) ) return 0;
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
static inline void Abc_BddNandG1EagerReduce( Abc_NandMan * p, int id, int idj )
{
  int wire =  Abc_BddNandCountWire( p );
  Abc_BddNandCspfCRefresh( p, id );
  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) return;
  Abc_BddNandCspfFaninConeRefresh( p, id );
  if ( wire == Abc_BddNandCountWire( p ) )
    {
      Abc_BddNandDisconnect( p, idj, id );
      Abc_BddNandBuildFanoutConeRefresh( p, id );
      if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) return;
      Abc_BddNandCspfCRefresh( p, id );
      if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) return;
      Abc_BddNandCspfFaninConeRefresh( p, id );
    }
  else
    {
      Abc_BddNandBuildAllRefresh( p );
      Abc_BddNandCspfEager( p );
    }
}
static inline void Abc_BddNandG1WeakReduce( Abc_NandMan * p, int id, int idj )
{
  int wire =  Abc_BddNandCountWire( p );
  Abc_BddNandCspfCRefresh( p, id );
  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) return;
  if ( Abc_BddNandIsEmptyOrDeadNode( p, idj ) ) return;
  if ( wire == Abc_BddNandCountWire( p ) )
    Abc_BddNandDisconnect( p, idj, id );
  Abc_BddNandBuildRefresh( p, id );
}
static inline void Abc_BddNandG1( Abc_NandMan * p, int fWeak )
{
  int id, idj; int i, j;
  Vec_Int_t * targets = Vec_IntDup( p->livingNodes );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) continue;
      if ( p->nVerbose > 1 )
	printf( "G1 for %d in %d gates\n", i, Vec_IntSize(targets) );
      Vec_Int_t * fanouts = Vec_IntAlloc( 1 );
      Abc_BddNandDescendantList_rec( p->fanoutList, fanouts, id );
      // try connecting pi
      Vec_IntForEachEntry( p->pis, idj, j )
	{
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) break;
	  if ( Abc_BddNandTryConnectRefreshing( p, idj, id ) == 1 )
	    {
	      if ( fWeak ) Abc_BddNandG1WeakReduce( p, id, idj );	
	      else Abc_BddNandG1EagerReduce( p, id, idj );
	    }
	}
      // try connecting candidate
      Vec_IntForEachEntry( targets, idj, j )
	{
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) break;
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, idj ) ) continue;
	  if ( id == idj ) continue;
	  if ( Vec_IntFind( fanouts, idj ) != -1 ) continue;
	  if ( Abc_BddNandTryConnectRefreshing( p, idj, id ) == 1 )
	    {
	      if ( fWeak ) Abc_BddNandG1WeakReduce( p, id, idj );
	      else Abc_BddNandG1EagerReduce( p, id, idj );
	    }
	}
      // recalculate fanouts for option
      if ( fWeak )
	{
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) continue;
	  Abc_BddNandCspfCRefresh( p, id );
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) continue;
	  Abc_BddNandCspfFaninConeRefresh( p, id );
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) continue;
	  Abc_BddNandBuildAllRefresh( p );
	}
      Vec_IntFree( fanouts );
    }
  Vec_IntFree( targets );
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandG3( Abc_NandMan * p )
{
  int i,j,k; int id, idj, idk;
  unsigned fi, fj, gi, gj, f1, f0, a, b, mergible, figj, fjgi, fx, gx, Value, eq;
  int out, wire;
  Vec_Int_t * fanouts;
  int new_id = Vec_IntSize( p->pis ) + 1;
  while ( !Abc_BddNandIsEmptyNode( p, new_id ) )
    {
      new_id++;
      assert( new_id < p->nObjs );
    }
  Vec_Int_t * targets = Vec_IntDup( p->livingNodes );
  // optimize
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( i == 0 ) break;
      for ( j = i - 1; (j >= 0) && (((idj) = Vec_IntEntry(targets, j)), 1); j-- )
	{ //  Vec_IntForEachEntryReverseStart(targets, idj, j, i - 1)
	  Abc_BddNandRefreshIfNeeded( p );
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) break;
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, idj ) ) continue;
	  if ( p->nVerbose > 1 )
	    printf( "G3 between %d %d in %d gates\n", i, j, Vec_IntSize(targets) );
	  fi = Abc_BddNandObjValue( p, id );
	  fj = Abc_BddNandObjValue( p, idj );
	  gi = p->G[id];
	  gj = p->G[idj];
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
	  Abc_BddNandObjValueWrite( p, new_id, fx );
	  p->G[new_id] = gx;
	  p->faninList[new_id] = Vec_IntAlloc( 1 );
	  p->fanoutList[new_id] = Vec_IntAlloc( 1 );
	  // for all living nodes, if it is not included in fanouts of i and j, and i and j themselves, try connect it to new node.
	  fanouts = Vec_IntAlloc( 1 );
	  Abc_BddNandDescendantList_rec( p->fanoutList, fanouts, id );
	  Abc_BddNandDescendantList_rec( p->fanoutList, fanouts, idj );
	  Vec_IntPushUnique( fanouts, id );
	  Vec_IntPushUnique( fanouts, idj );
	  eq = Abc_BddOr( p->pBdd, Abc_BddLitNot( fx ), gx );
	  Value = Abc_BddLitConst1();
	  Vec_IntForEachEntry( p->pis, idk, k ) 
	    if ( Abc_BddNandTryConnect( p, idk, new_id ) == 1 )
	      {
		if ( Abc_BddLitIsConst1( eq ) ) break;
		if ( Abc_BddLitIsInvalid( Value ) || Abc_BddLitIsInvalid( eq ) ) break;
		Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjValue( p, idk ) );
		eq = Abc_BddOr( p->pBdd, eq, Abc_BddLitNot( Value ) );
	      }
	  Vec_IntForEachEntry( targets, idk, k )
	    {
	      if ( Abc_BddNandIsEmptyOrDeadNode( p, idk ) ) continue;
	      if ( Vec_IntFind( fanouts, idj ) != -1 ) continue;
	      if ( Abc_BddNandTryConnect( p, idk, new_id ) == 1 )
		{
		  if ( Abc_BddLitIsConst1( eq ) ) break;
		  if ( Abc_BddLitIsInvalid( Value ) || Abc_BddLitIsInvalid( eq ) ) break;
		  Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjValue( p, idk ) );
		  eq = Abc_BddOr( p->pBdd, eq, Abc_BddLitNot( Value ) );
		}
	    }
	  if ( Vec_IntSize( p->faninList[new_id] ) == 0 )
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
	  Abc_BddNandObjValueWrite( p, new_id, Abc_BddLitNot( Value ) );
	  p->G[new_id] = Abc_BddAnd( p->pBdd, p->G[id] ,p->G[idj] );
	  if ( Abc_BddLitIsInvalid( p->G[new_id] ) )
	    {
	      Abc_BddNandRemoveNode( p, new_id );	  
	      continue;
	    }
	  Vec_IntForEachEntry( p->fanoutList[id], idk, k )
	    Abc_BddNandConnect( p, new_id, idk, 0 );
	  Vec_IntForEachEntry( p->fanoutList[idj], idk, k )
	    if ( Vec_IntFind( p->fanoutList[new_id], idk ) == -1 )
	      Abc_BddNandConnect( p, new_id, idk, 0 );
	  Abc_BddNandInsertLivingNode( p, new_id );
	  out = Abc_BddNandCspfC( p, new_id );
	  Abc_BddNandSortFanin( p, new_id );
	  out += Abc_BddNandCspfC( p, new_id );
	  wire = Vec_IntSize( p->faninList[id] ) + Vec_IntSize( p->faninList[idj] );
	  if ( out || Vec_IntSize( p->faninList[new_id] ) > wire - 1 )
	    {
	      Abc_BddNandRemoveNode( p, new_id );
	      continue;
	    }
	  // if inputs < inputs_before - 1, do the followings
	  // remove merged (replaced) nodes
	  Abc_BddNandRemoveNode( p, id );
	  Abc_BddNandRemoveNode( p, idj );
	  // calculate function of new node
	  Abc_BddNandBuildFanoutConeRefresh( p, new_id );
	  Abc_BddNandCspfRefresh( p );
	  while ( !Abc_BddNandIsEmptyNode( p, new_id ) )
	    {
	      new_id++;
	      assert( new_id < p->nObjs );
	    }
	  break;
	}
    }
  Vec_IntFree( targets );
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandG1multi( Abc_NandMan * p, int fWeak )
{
  int i, j; int id, idj;
  Vec_Int_t * targets = Vec_IntDup( p->livingNodes );
  Vec_Int_t * targets2;
  Vec_Int_t * fanouts;
  targets2 = Vec_IntAlloc( 1 );
  Vec_IntForEachEntryStart( p->pos, id, i, Vec_IntSize( p->pos ) / 2 )
    Abc_BddNandDescendantList_rec( p->faninList, targets2, id );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) continue;
      if ( p->nVerbose > 1 )
	printf( "G1-multi for %d in %d gates\n", i, Vec_IntSize(targets) );
      fanouts = Vec_IntAlloc( 1 );
      Abc_BddNandDescendantList_rec( p->fanoutList, fanouts, id );
      Vec_IntForEachEntry( p->pis, idj, j )
	{
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) break;
	  if ( Abc_BddNandTryConnectRefreshing( p, idj, id ) == 1 )
	    {
	      if ( fWeak ) Abc_BddNandG1WeakReduce( p, id, idj );	
	      else Abc_BddNandG1EagerReduce( p, id, idj );
	    }
	}
      Vec_IntForEachEntry( targets2, idj, j )
	{
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) break;
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, idj ) ) continue;
	  if ( id == idj ) continue;
	  if ( Vec_IntFind( fanouts, idj ) != -1 ) continue;
	  if ( Abc_BddNandTryConnectRefreshing( p, idj, id ) == 1 )
	    {
	      if ( fWeak ) Abc_BddNandG1WeakReduce( p, id, idj );
	      else Abc_BddNandG1EagerReduce( p, id, idj );
	    }
	}
      if ( fWeak )
	{
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) continue;
	  Abc_BddNandCspfCRefresh( p, id );
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) continue;
	  Abc_BddNandCspfFaninConeRefresh( p, id );
	  if ( Abc_BddNandIsEmptyOrDeadNode( p, id ) ) continue;
	  Abc_BddNandBuildAllRefresh( p );
	}
      Vec_IntFree( fanouts );
    }
  Vec_IntFree( targets );
  Vec_IntFree( targets2 );
}
static inline void Abc_BddNandDc( Abc_NandMan * p )
{
  // please be sure reset will destroy Dc set here and will cause segmentation fault
  int id, idj; int i;
  int nPos = Vec_IntSize( p->pos ) / 2;
  p->fDc = 1;
  for ( i = 0; i < nPos; i++ )
    {
      id = Vec_IntPop( p->pos );
      idj = Vec_IntEntry( p->faninList[id], 0 );
      Vec_IntRemove( p->fanoutList[idj], id );
      Vec_IntFree( p->faninList[id] );
      p->faninList[id] = 0;
      p->G[Vec_IntEntry( p->pos, nPos - i )] = Abc_BddNandObjValue( p, idj );
    }
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandPrintStats( Abc_NandMan * p, char * prefix, abctime clk0 )
{
  printf( "\r%-10s: gates = %5d, wires = %5d, AIG node = %5d", prefix, Vec_IntSize( p->livingNodes ), Abc_BddNandCountWire( p ), Abc_BddNandCountWire( p ) - Vec_IntSize( p->livingNodes ) );
  ABC_PRT( ", time ", Abc_Clock() - clk0 );
}
void Abc_BddNandGiaTest( Gia_Man_t * pGia, char * FileName, int nMem, int nType, int fRep, int fDc, int nVerbose )
{
  Abc_NandMan * p = Abc_BddNandManAlloc( pGia, FileName, nMem, fDc, nVerbose );
  Abc_BddNandGenNet( p, pGia );
  assert( ( 1u << p->nMem ) > Vec_IntSize( p->pis ) + 2 );
  abctime clk0 = Abc_Clock();
  p->pBdd = Abc_BddManAlloc( Vec_IntSize( p->pis ), 1 << p->nMem, (int)( nVerbose > 2 ) );
  assert( !Abc_BddNandBuildAll( p ) );
  if ( p->fDc ) Abc_BddNandDc( p );
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
  if ( nVerbose ) ABC_PRT( "total ", Abc_Clock() - clk0 );
  Abc_BddNandPrintNet( p );
  Abc_BddNandManFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

