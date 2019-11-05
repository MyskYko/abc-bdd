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
  int          nGiaObjs;
  int          nObjsAlloc;
  Vec_Int_t *  vPis;
  Vec_Int_t *  vPos;
  Vec_Int_t *  vObjs;
  Vec_Int_t ** pvFanins;
  Vec_Int_t ** pvFanouts;
  int *        pBddFuncs;
  int *        pRank;
  char *       pMark;
  unsigned *   pGFuncs;
  Vec_Int_t ** pvCFuncs;
  
  int          nMem;
  int          nVerbose;
  
  Abc_BddMan * pBdd;
  Gia_Man_t *  pGia;
  Vec_Int_t *  vPiCkts;
  Vec_Int_t *  vPiIdxs;
  Vec_Ptr_t *  vvDcGias;

  int          fRm;
  int          nMspf;
};

static inline int      Abc_BddNandConst0() { return 0; }  // = Gia_ObjId( pGia, Gia_ManConst0( pGia ) );

static inline int      Abc_BddNandObjIsPi( Abc_NandMan * p, int id ) { return (int)( p->pvFanins[id] == 0 ); }
static inline int      Abc_BddNandObjIsPo( Abc_NandMan * p, int id ) { return (int)( p->pvFanouts[id] == 0 ); }

static inline unsigned Abc_BddNandObjGetBddFunc( Abc_NandMan * p, int id ) { return p->pBddFuncs[id];            }
static inline void     Abc_BddNandObjSetBddFunc( Abc_NandMan * p, int id, unsigned Value ) { p->pBddFuncs[id] = Value; }

static inline int      Abc_BddNandObjIsEmpty( Abc_NandMan * p, int id ) { return (int)( p->pvFanins[id] == 0 && p->pvFanouts[id] == 0 ); }
static inline int      Abc_BddNandObjIsDead( Abc_NandMan * p, int id ) { return (int)( Vec_IntSize( p->pvFanouts[id] ) == 0 ); }
static inline int      Abc_BddNandObjIsEmptyOrDead( Abc_NandMan * p, int id ) { return ( Abc_BddNandObjIsEmpty( p, id ) || Abc_BddNandObjIsDead( p, id ) ); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
	      
/**Function*************************************************************

  Synopsis    []

  Description [print circuit for debug]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandPrintNet( Abc_NandMan * p, char * fName )
{
  int id, idj; int i, j, k;
  FILE *fp;
  fp = fopen( fName, "w" );
  fprintf( fp, ".model test\n" );
  fprintf( fp, ".inputs" );
  Vec_IntForEachEntry( p->vPis, id, i )
    fprintf( fp, " pi%d", id - 1 );
  fprintf( fp, "\n.outputs" );
  Vec_IntForEachEntry( p->vPos, id, i )
    fprintf( fp, " po%d", i );
  fprintf( fp, "\n" );
  fprintf( fp, ".names const0\n0\n" );
  Vec_IntForEachEntry( p->vObjs, id, i )
    {
      if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) continue;
      fprintf( fp,".names " );
      Vec_IntForEachEntry( p->pvFanins[id], idj, j )
	if ( idj == 0 )
	  fprintf( fp, "const0 " );	  
	else if ( idj <= Vec_IntSize( p->vPis ) ) // assuming (id of pi <= num pi)
	  fprintf( fp, "pi%d ", idj - 1 );
	else
	  fprintf( fp, "n%d ", idj );
      fprintf( fp, "n%d\n", id );
      for ( k = 0; k < Vec_IntSize( p->pvFanins[id] ); k++ ) 
	fprintf( fp, "1" );
      fprintf( fp, " 0\n" );
    }
  Vec_IntForEachEntry( p->vPos, id, i )
    {
      idj = Vec_IntEntry( p->pvFanins[id], 0 );
      fprintf( fp, ".names " );
      if ( idj == 0 )
	fprintf( fp, "const0 " );	  
      else if ( idj <= Vec_IntSize( p->vPis ) ) // assuming (id of pi <= num pi)
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
void Abc_BddNandMarkDescendant_rec( Abc_NandMan * p, Vec_Int_t ** children, int id )
{
  int j, idj;
  Vec_IntForEachEntry( children[id], idj, j )
    if ( !p->pMark[idj] && children[idj] ) // idj is not marked and not leaf
      {
	p->pMark[idj] = 1;
	Abc_BddNandMarkDescendant_rec( p, children, idj );
      }
}
static inline void Abc_BddNandMarkClear( Abc_NandMan * p )
{
  ABC_FREE( p->pMark );
  p->pMark = ABC_CALLOC( char, p->nObjsAlloc );
}
void Abc_BddNandDescendantList_rec( Abc_NandMan * p, Vec_Int_t ** children, Vec_Int_t * list, int id )
{
  int j, idj;
  Vec_IntForEachEntry( children[id], idj, j )
    if ( !(p->pMark[idj] >> 1) && children[idj] ) // idj is not marked and not leaf
      {
	p->pMark[idj] += 2;
	Vec_IntPush( list, idj );
	Abc_BddNandDescendantList_rec( p, children, list, idj );
      }
}
static inline void Abc_BddNandSortList( Abc_NandMan * p, Vec_Int_t * list )
{
  int i, id, index;
  Vec_Int_t * listOld = Vec_IntDup( list );
  Vec_IntClear( list );
  Vec_IntForEachEntry( p->vObjs, id, i )
    {
      index = Vec_IntFind( listOld, id );
      if ( index != -1 )
	{
	  Vec_IntDrop( listOld, index );      
	  Vec_IntPush( list, id );
	  if ( !Vec_IntSize( listOld ) ) break;
	}
    }
  Vec_IntFree( listOld );
}

static inline void Abc_BddNandDescendantSortedList( Abc_NandMan * p, Vec_Int_t ** children, Vec_Int_t * list, int id )
{
  int j, idj;
  Abc_BddNandDescendantList_rec( p, children, list, id );
  Vec_IntForEachEntry( list, idj, j )
    p->pMark[idj] -= 2;
  Abc_BddNandSortList( p, list );
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
static inline void Abc_BddNandGia2Net( Abc_NandMan * p )
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
  Gia_ManForEachCi( p->pGia, pObj, i )
    {
      id = Gia_ObjId( p->pGia, pObj );
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
  Gia_ManForEachAnd( p->pGia, pObj, i )
    {
      id = Gia_ObjId( p->pGia, pObj );
      p->pvFanins[id] = Vec_IntAlloc( 1 );
      p->pvFanouts[id] = Vec_IntAlloc( 1 );
      pObj0 = Gia_ObjFanin0( pObj );
      pObj1 = Gia_ObjFanin1( pObj );
      id0 = Gia_ObjId( p->pGia, pObj0 );
      id1 = Gia_ObjId( p->pGia, pObj1 );
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
  Gia_ManForEachCo( p->pGia, pObj, i )
    {
      id = Gia_ObjId( p->pGia, pObj );
      p->pvFanins[id] = Vec_IntAlloc( 1 );
      p->pvFanouts[id] = 0;
      pObj0 = Gia_ObjFanin0( pObj );
      id0 = Gia_ObjId( p->pGia, pObj0 );
      if ( (  ( id0 == Abc_BddNandConst0() || Gia_ObjIsCi( pObj0 ) ) &&  Gia_ObjFaninC0( pObj ) ) ||
	   ( !( id0 == Abc_BddNandConst0() || Gia_ObjIsCi( pObj0 ) ) && !Gia_ObjFaninC0( pObj ) ) )
	id0 += p->nGiaObjs;
      Abc_BddNandConnect( p, id0, id, 0 );
      Vec_IntPush( p->vPos, id );
    }
  // remove redundant nodes
  Vec_IntForEachEntryReverse( p->vObjs, id, i )
    if ( !Vec_IntSize( p->pvFanouts[id] ) )
      Abc_BddNandRemoveNode( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_NandMan * Abc_BddNandManAlloc( Gia_Man_t * pGia, int nMem, int fRm, int nMspf, int nVerbose )
{
  int i;
  Abc_NandMan * p = ABC_CALLOC( Abc_NandMan, 1 );
  p->nGiaObjs = pGia->nObjs;
  p->nObjsAlloc = pGia->nObjs + pGia->nObjs;
  p->vPis = Vec_IntAlloc( Gia_ManCiNum( pGia ) );
  p->vPos = Vec_IntAlloc( Gia_ManCoNum( pGia ) );
  p->vObjs = Vec_IntAlloc( 1 );
  p->pvFanins  = ABC_CALLOC( Vec_Int_t *, p->nObjsAlloc );
  p->pvFanouts = ABC_CALLOC( Vec_Int_t *, p->nObjsAlloc );
  p->pBddFuncs = ABC_CALLOC( int        , p->nObjsAlloc );
  p->pRank     = ABC_CALLOC( int        , p->nObjsAlloc );
  p->pMark     = ABC_CALLOC( char       , p->nObjsAlloc );
  p->pGFuncs   = ABC_CALLOC( unsigned   , p->nObjsAlloc );
  p->pvCFuncs  = ABC_CALLOC( Vec_Int_t *, p->nObjsAlloc );
  if ( !p->pvFanins || !p->pvFanouts || !p->pBddFuncs || !p->pRank || !p->pMark || !p->pGFuncs || !p->pvCFuncs )
    {
      printf("Error: Allocation failed\n");
      abort();
    }
  p->nMem = nMem;
  p->fRm = fRm;
  p->nMspf = nMspf;
  p->nVerbose = nVerbose;
  p->pGia = pGia;
  p->vPiCkts = Vec_IntAlloc( 1 );
  p->vPiIdxs = Vec_IntAlloc( 1 );
  p->vvDcGias = Vec_PtrAlloc( 1 );
  for ( i = 0; i < Gia_ManCoNum( pGia ); i++ )
    Vec_PtrPush( p->vvDcGias, Vec_PtrAlloc( 1 ) );
  Abc_BddNandGia2Net( p );
  return p;
}
static inline void Abc_BddNandManFree( Abc_NandMan * p )
{
  int i, j;
  Vec_Ptr_t * vDcGias;
  Gia_Man_t * pGia;
  Vec_IntFree( p->vPis );
  Vec_IntFree( p->vPos );
  Vec_IntFree( p->vObjs );
  Vec_IntFree( p->vPiCkts );
  Vec_IntFree( p->vPiIdxs );
  ABC_FREE( p->pBddFuncs );
  ABC_FREE( p->pRank );
  ABC_FREE( p->pMark );
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
  Gia_ManStop( p->pGia );
  Vec_PtrForEachEntry( Vec_Ptr_t *, p->vvDcGias, vDcGias, i )
    Vec_PtrForEachEntry( Gia_Man_t *, vDcGias, pGia, j )
      Gia_ManStop( pGia );
  Vec_PtrFree( p->vvDcGias );
  Abc_BddManFree( p->pBdd );
  ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandSetPoInfo( Gia_Man_t * pGia, Vec_Ptr_t * vNets, Vec_Ptr_t * vvPis, Vec_Ptr_t * vvPos, Vec_Int_t * vExternalPos, Vec_Int_t * vPoCkts, Vec_Int_t * vPoIdxs )
{
  int i, j, k, id;
  Gia_Obj_t * pObj;
  Vec_Int_t * vId, * vCkts, * vIdxs, * vPis, * vPos;
  Gia_Man_t * pConst0;
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
      // set external don't care to be 0
      p = Vec_PtrEntry( vNets, Vec_IntEntry( vCkts, k ) );
      pConst0 = Gia_ManStart( Vec_IntSize( p->vPis ) );
      Vec_IntForEachEntry( p->vPis, id, j )
	Gia_ManAppendCi( pConst0 );
      Gia_ManAppendCo( pConst0, Gia_ManConst0Lit() );
      Vec_PtrPush( Vec_PtrEntry( p->vvDcGias, Vec_IntEntry( vIdxs, k ) ), pConst0 );
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
static inline void Abc_BddNandGia2Nets( Gia_Man_t * pOld, Vec_Ptr_t * vNets, Vec_Int_t * vPoCkts, Vec_Int_t * vPoIdxs, Vec_Int_t * vExternalCs, int nMem, int fRm, int nWindowSize, int nMspf, int nVerbose )
{
  int i, id, lit, newId, part;
  int * pFanouts, * pParts;
  Vec_Int_t * vPis, * vPos, * vTempPos, * vNodes, * vExternalPos, * vCands;
  Vec_Ptr_t * vvPis, * vvPos;
  Gia_Man_t * pGia, * pNew;
  Gia_Obj_t * pObj, * pObj0, * pObj1;
  Abc_NandMan * p;
  pGia = Gia_ManDup ( pOld );
  pFanouts = ABC_CALLOC( int, pGia->nObjs );
  pParts = ABC_CALLOC( int, pGia->nObjs );
  if ( !pFanouts || !pParts )
    {
      printf("Error: Allocation failed\n");
      abort();
    }
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
		   !pFanouts[id] && !Abc_BddNandCountNewFanins( pGia, pObj, pParts, part ) )
		{ newId = id; Vec_IntDrop( vPis, i ); break; } }
	  if ( newId == Abc_BddNandConst0() )
	    Vec_IntForEachEntry( vPis, id, i )
	      { pObj = Gia_ManObj( pGia, id );
		if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) &&
		     !pFanouts[id] && Abc_BddNandCountNewFanins( pGia, pObj, pParts, part ) == 1 )
		  { newId = id; Vec_IntDrop( vPis, i ); break; } }
	  if ( newId == Abc_BddNandConst0() )
	    Vec_IntForEachEntry( vPis, id, i )
	      { pObj = Gia_ManObj( pGia, id );
		if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) && !pFanouts[id] )
		  { newId = id; Vec_IntDrop( vPis, i ); break; } }
	  if ( newId == Abc_BddNandConst0() )
	    Vec_IntForEachEntry( vCands, id, i )
	      { pObj = Gia_ManObj( pGia, id );
		if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) &&
		     !pFanouts[id] && !Abc_BddNandCountNewFanins( pGia, pObj, pParts, part ) )
		  { newId = id; break; } }
	  if ( newId == Abc_BddNandConst0() )
	    Vec_IntForEachEntry( vCands, id, i )
	      { pObj = Gia_ManObj( pGia, id );
		if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) &&
		     !pFanouts[id] && Abc_BddNandCountNewFanins( pGia, pObj, pParts, part ) == 1 )
		  { newId = id; break; } }
	  if ( newId == Abc_BddNandConst0() )
	    Vec_IntForEachEntry( vCands, id, i )
	      { pObj = Gia_ManObj( pGia, id );
		if ( !Gia_ObjIsConst0( pObj ) && !Gia_ObjIsCi( pObj ) && !pFanouts[id] )
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
      p = Abc_BddNandManAlloc( pNew, nMem, fRm, nMspf, (int)( nVerbose > 2 ) );
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
static inline int Abc_BddNandBuild( Abc_NandMan * p, int id )
{
  int j, idj;
  unsigned Value = Abc_BddLitConst1();
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjGetBddFunc( p, idj ) );
  if ( Abc_BddLitIsInvalid( Value ) ) return -1;
  Abc_BddNandObjSetBddFunc( p, id, Abc_BddLitNot( Value ) );
  return 0;
}
static inline int Abc_BddNandBuildAll( Abc_NandMan * p )
{
  int i, id;
  Vec_IntForEachEntry( p->vObjs, id, i )
    if ( Abc_BddNandBuild( p, id ) ) return -1;
  return 0;
}
static inline int Abc_BddNandBuildFanoutCone( Abc_NandMan * p, int startId )
{ // including startId itself
  int i, id;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  p->pMark[startId] += 2;
  Vec_IntPush( targets, startId );
  Abc_BddNandDescendantSortedList( p, p->pvFanouts, targets, startId );
  Vec_IntForEachEntry( targets, id, i )
    if ( Abc_BddNandBuild( p, id ) )
      {
	Vec_IntFree( targets );
	return -1;
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
	  printf( "Eq-check faild: different at %d %10u %10u\n", id, Abc_BddNandObjGetBddFunc( p, id ), Abc_BddLitNot( Value ) );
	  return -1;
	}
    }
  return 0;
}
static inline int Abc_BddNandBuildInverted( Abc_NandMan * p, int id, int startId )
{
  int j, idj;
  unsigned Value = Abc_BddLitConst1();
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    if ( idj == startId ) Value = Abc_BddAnd( p->pBdd, Value, Abc_BddLitNot( Abc_BddNandObjGetBddFunc( p, idj ) ) );
    else Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjGetBddFunc( p, idj ) );
  if ( Abc_BddLitIsInvalid( Value ) ) return -1;
  Abc_BddNandObjSetBddFunc( p, id, Abc_BddLitNot( Value ) );
  return 0;
}
static inline int Abc_BddNandBuildFanoutConeInverted( Abc_NandMan * p, int startId )
{ // insert inverters between startId and the fanout node
  int i, id;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  Abc_BddNandDescendantSortedList( p, p->pvFanouts, targets, startId );
  Vec_IntForEachEntry( targets, id, i )
    if ( Abc_BddNandBuildInverted( p, id, startId ) )
      {
	Vec_IntFree( targets );
	return -1;
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
static inline int Abc_BddNandDc( Abc_NandMan * p )
{
  int i, j;
  unsigned Value;
  Gia_Obj_t * pObj;
  Gia_Man_t * pGia;
  Vec_Ptr_t * vDcGias;
  Vec_PtrForEachEntry( Vec_Ptr_t *, p->vvDcGias, vDcGias, i )
    {
      if ( !Vec_PtrSize( vDcGias ) ) continue;
      Value = Abc_BddLitConst1();
      Vec_PtrForEachEntry( Gia_Man_t *, vDcGias, pGia, j )
	{
	  if ( Abc_BddGia( pGia, p->pBdd ) ) return -1;
	  pObj = Gia_ManCo( pGia, 0 );
	  Value = Abc_BddAnd( p->pBdd, Value, pObj->Value );
	  if ( Abc_BddLitIsInvalid( Value ) ) return -1;
	}
      p->pGFuncs[Vec_IntEntry( p->vPos, i )] = Value;
    }
  return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_BddNandGFunc( Abc_NandMan * p, int id )
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
  if ( Abc_BddLitIsInvalid( p->pGFuncs[id] ) ) return -1;
  return 0;
}
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandRank( Abc_NandMan * p, int id )
{
  if ( Abc_BddNandObjIsPi( p, id ) )
    {
      p->pRank[id] = 1 << 30; // assume this is the max
      return;
    }
  p->pRank[id] = Vec_IntSize( p->pvFanouts[id] );
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
static inline int Abc_BddNandRemoveRedundantFanin( Abc_NandMan * p, int id )
{
  int j, k, idj, idk;
  unsigned fanins, fj, c, dc1;
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      fanins = Abc_BddLitConst1();
      Vec_IntForEachEntry( p->pvFanins[id], idk, k )
	if ( k != j )
	  fanins = Abc_BddAnd( p->pBdd, fanins, Abc_BddNandObjGetBddFunc( p, idk ) );
      fj = Abc_BddNandObjGetBddFunc( p, idj );
      c = Abc_BddOr( p->pBdd, p->pGFuncs[id], Abc_BddLitNot( fanins ) );
      dc1 = Abc_BddOr( p->pBdd, fj, c );
      if ( Abc_BddLitIsInvalid( dc1 ) ) return -1;
      if ( Abc_BddLitIsConst1( dc1 ) )
	{
	  Abc_BddNandDisconnect( p, idj, id );
	  if ( !Vec_IntSize( p->pvFanins[id] ) )
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
    }
  return 0;
}
static inline int Abc_BddNandCFuncCspf( Abc_NandMan * p, int id )
{
  int j, k, idj, idk;
  unsigned fanins, fi, fj, already1, c, dc1;
  if ( p->fRm )
    if ( Abc_BddNandRemoveRedundantFanin( p, id ) ) return -1;
  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) return 0;
  if ( !p->pvCFuncs[id] ) p->pvCFuncs[id] = Vec_IntAlloc( Vec_IntSize( p->pvFanins[id] ) );
  Vec_IntClear( p->pvCFuncs[id] );
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      fanins = Abc_BddLitConst1();
      Vec_IntForEachEntryStart( p->pvFanins[id], idk, k, j + 1 )
	fanins = Abc_BddAnd( p->pBdd, fanins, Abc_BddNandObjGetBddFunc( p, idk ) );
      fi = Abc_BddNandObjGetBddFunc( p, id );
      fj = Abc_BddNandObjGetBddFunc( p, idj );
      already1 = Abc_BddAnd( p->pBdd, fi, fj );
      c = Abc_BddOr( p->pBdd, p->pGFuncs[id], Abc_BddLitNot( fanins ) );
      c = Abc_BddOr( p->pBdd, c, already1 );
      dc1 = Abc_BddOr( p->pBdd, fj, c );
      if ( Abc_BddLitIsInvalid( dc1 ) ) return -1;
      if ( Abc_BddLitIsConst1( dc1 ) )
	{
	  Abc_BddNandDisconnect( p, idj, id );
	  if ( !Vec_IntSize( p->pvFanins[id] ) )
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
      if ( Abc_BddNandObjIsDead( p, id ) )
	{
	  Abc_BddNandRemoveNode( p, id );
	  continue;
	}
      if ( Abc_BddNandGFunc( p, id ) ) return -1;
      if ( Abc_BddNandCFuncCspf( p, id ) ) return -1;
    }
  return Abc_BddNandBuildAll( p );
}
static inline int Abc_BddNandCspfFaninCone( Abc_NandMan * p, int startId )
{
  int i, id;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  if ( Abc_BddNandCFuncCspf( p, startId ) ) return -1;
  Abc_BddNandDescendantSortedList( p, p->pvFanins, targets, startId );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Abc_BddNandObjIsDead( p, id ) )
	{
	  Abc_BddNandRemoveNode( p, id );
	  continue;
	}
      if ( Abc_BddNandGFunc( p, id ) ) return -1;
      if ( Abc_BddNandCFuncCspf( p, id ) ) return -1;
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
int Abc_BddNandIsFanoutShared_rec( Abc_NandMan * p, int id, int stage )
{
  int j, idj, m;
  if ( Abc_BddNandObjIsPo( p, id ) ) return 0;
  m = p->pMark[id] >> 1;
  if ( m == stage ) return 0;
  if ( m ) return 1;
  p->pMark[id] += stage << 1;
  Vec_IntForEachEntry( p->pvFanouts[id], idj, j )
    if ( Abc_BddNandIsFanoutShared_rec( p, idj, stage ) )
      return 1;
  return 0;
}
static inline int Abc_BddNandIsFanoutShared( Abc_NandMan * p, int id )
{
  int i, j, idj, r;
  r = 0;
  Vec_IntForEachEntry( p->pvFanouts[id], idj, j )
    if ( Abc_BddNandIsFanoutShared_rec( p, idj, j + 1 ) )
      {
	r = 1;
	break;
      }
  for ( i = 0; i < p->nObjsAlloc; i++ )
    if ( p->pMark[i] % 2 ) p->pMark[i] = 1;
    else p->pMark[i] = 0;
  return r;
}
static inline int Abc_BddNandGFuncMspf( Abc_NandMan * p, int id )
{
  int j, idj, idk;
  unsigned Value, t;
  Vec_Int_t * posOld;
  if ( !Abc_BddNandIsFanoutShared( p, id ) ) return Abc_BddNandGFunc( p, id );
  posOld = Vec_IntAlloc( Vec_IntSize( p->vPos ) );
  Vec_IntForEachEntry( p->vPos, idj, j )
    {
      idk = Vec_IntEntry( p->pvFanins[idj], 0 );
      Vec_IntPush( posOld, Abc_BddNandObjGetBddFunc( p, idk ) );
    }
  if ( Abc_BddNandBuildFanoutConeInverted( p, id ) )
    {
      Vec_IntFree( posOld );
      return -1;
    }
  Value = Abc_BddLitConst1();
  Vec_IntForEachEntry( p->vPos, idj, j )
    {
      idk = Vec_IntEntry( p->pvFanins[idj], 0 );
      if ( id == idk )
	t = Abc_BddXnor( p->pBdd, Abc_BddLitNot( Abc_BddNandObjGetBddFunc( p, idk ) ), Vec_IntEntry( posOld, j ) );
      else
	t = Abc_BddXnor( p->pBdd, Abc_BddNandObjGetBddFunc( p, idk ), Vec_IntEntry( posOld, j ) );
      t = Abc_BddOr( p->pBdd, t, p->pGFuncs[idj] );
      Value = Abc_BddAnd( p->pBdd, Value, t );
      if ( Abc_BddLitIsInvalid( Value ) )
	{
	  Vec_IntFree( posOld );
	  return -1;
	}
    }
  p->pGFuncs[id] = Value;
  Abc_BddNandBuildFanoutCone( p, id );
  Vec_IntFree( posOld );
  return 0;
}
static inline int Abc_BddNandCFuncMspf( Abc_NandMan * p, int id )
{
  int j, k, idj, idk;
  unsigned fanins, fj, c, dc1;
  if ( !p->pvCFuncs[id] ) p->pvCFuncs[id] = Vec_IntAlloc( Vec_IntSize( p->pvFanins[id] ) );
  Vec_IntClear( p->pvCFuncs[id] );
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      fanins = Abc_BddLitConst1();
      Vec_IntForEachEntry( p->pvFanins[id], idk, k )
	if ( k != j )
	  fanins = Abc_BddAnd( p->pBdd, fanins, Abc_BddNandObjGetBddFunc( p, idk ) );
      c = Abc_BddOr( p->pBdd, p->pGFuncs[id], Abc_BddLitNot( fanins ) );
      fj = Abc_BddNandObjGetBddFunc( p, idj );
      dc1 = Abc_BddOr( p->pBdd, fj, c );
      if ( Abc_BddLitIsInvalid( dc1 ) ) return -1;
      if ( Abc_BddLitIsConst1( dc1 ) )
	{
	  Abc_BddNandDisconnect( p, idj, id );
	  if ( !Vec_IntSize( p->pvFanins[id] ) )
	    {
	      Vec_IntForEachEntry( p->pvFanouts[id], idk, k )
		if ( Vec_IntFind( p->pvFanins[idk], Abc_BddNandConst0() ) == -1 )
		  Abc_BddNandConnect( p, Abc_BddNandConst0(), idk, 0 );
	      Abc_BddNandRemoveNode( p, id );
	    }
	  return 1;
	}
      Vec_IntPush( p->pvCFuncs[id], c );
    }
  return 0;
}
static inline int Abc_BddNandMspf( Abc_NandMan * p )
{
  int i, c, id;
  Vec_IntForEachEntryReverse( p->vObjs, id, i )
    {
      if ( Abc_BddNandObjIsDead( p, id ) )
	{
	  Abc_BddNandRemoveNode( p, id );
	  continue;
	}
      if ( Abc_BddNandGFuncMspf( p, id ) ) return -1;
      c = Abc_BddNandCFuncMspf( p, id );
      if ( c == -1 ) return -1;
      if ( c == 1 )
	{
	  Abc_BddNandBuildAll( p );
	  i = Vec_IntSize( p->vObjs );
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
static inline int Abc_BddNandTryConnect( Abc_NandMan * p, int fanin, int fanout )
{
  if ( Vec_IntFind( p->pvFanins[fanout], fanin ) != -1 ) return 0; // already connected
  unsigned ffanin = Abc_BddNandObjGetBddFunc( p, fanin );
  unsigned ffanout = Abc_BddNandObjGetBddFunc( p, fanout );
  unsigned gfanout = p->pGFuncs[fanout];
  unsigned connectable = Abc_BddOr( p->pBdd, ffanout, gfanout );
  connectable = Abc_BddOr( p->pBdd, ffanin, connectable );
  if( Abc_BddLitIsInvalid( connectable ) ) return -1;
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
  while ( 1 )
    {
      Abc_BddManFree( p->pBdd );
      p->pBdd = Abc_BddManAlloc( Vec_IntSize( p->vPis ), 1 << p->nMem, (int)( p->nVerbose > 2 ) );
      int out = 0;
      out = Abc_BddNandDc( p );
      if ( !out ) out = Abc_BddNandBuildAll( p );
      if ( !out )
	{
	  if ( p->nMspf < 2 ) out = Abc_BddNandCspf( p );
	  else out = Abc_BddNandMspf( p );
	}
      if ( !out ) break;
      p->nMem++;
      if ( 1 << p->nMem == 0 )
	{
	  printf("Error: Refresh failed\n");
	  abort();
	}
    }
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
static inline void Abc_BddNandCspf_Refresh( Abc_NandMan * p ) { if ( Abc_BddNandCspf( p ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandCspfFaninCone_Refresh( Abc_NandMan * p, int startId ) { if ( Abc_BddNandCspfFaninCone( p, startId ) ) Abc_BddNandRefresh( p ); }
static inline void Abc_BddNandRemoveRedundantFanin_Refresh( Abc_NandMan * p, int id ) {
  if ( !Abc_BddNandRemoveRedundantFanin( p, id ) ) return;
  Abc_BddNandRefresh( p );
  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) return;
  while ( !Abc_BddNandRemoveRedundantFanin( p, id ) )
    {
      p->nMem++;
      if ( 1 << p->nMem == 0 )
	{
	  printf("Error: Refresh failed\n");
	  abort();
	}
      Abc_BddNandRefresh( p );
      if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) return;
    }
}
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
  while ( c == -1 )
    {
      p->nMem++;
      if ( 1 << p->nMem == 0 )
	{
	  printf("Error: Refresh failed\n");
	  abort();
	}
      Abc_BddNandRefresh( p );
      if ( Abc_BddNandObjIsEmptyOrDead( p, fanin ) ) return 0;
      if ( Abc_BddNandObjIsEmptyOrDead( p, fanout ) ) return 0;
      c = Abc_BddNandTryConnect( p, fanin, fanout );
    }
  return c;
}
static inline void Abc_BddNandMspf_Refresh( Abc_NandMan * p )
{
  if ( !Abc_BddNandMspf( p ) ) return;
  while ( 1 )
    {
      Abc_BddManFree( p->pBdd );
      p->pBdd = Abc_BddManAlloc( Vec_IntSize( p->vPis ), 1 << p->nMem, (int)( p->nVerbose > 2 ) );
      int out = 0;
      out = Abc_BddNandDc( p );
      if ( !out ) out = Abc_BddNandBuildAll( p );
      if ( !out ) out = Abc_BddNandMspf( p );
      if ( !out ) break;
      p->nMem++;
      if ( 1 << p->nMem == 0 )
	{
	  printf("Error: Refresh failed\n");
	  abort();
	}
    }
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
  if ( p->nMspf ) Abc_BddNandMspf_Refresh( p );
  if ( p->nMspf < 2 ) Abc_BddNandCspfEager( p );
}
static inline void Abc_BddNandG1WeakReduce( Abc_NandMan * p, int id, int idj )
{
  int wire = Abc_BddNandCountWire( p );
  Abc_BddNandRemoveRedundantFanin_Refresh( p, id );
  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ||
       Abc_BddNandObjIsEmptyOrDead( p, idj ) )
    return; // If this, we don't need to do below.
  if ( wire == Abc_BddNandCountWire( p ) ) 
      Abc_BddNandDisconnect( p, idj, id );
  Abc_BddNandBuild_Refresh( p, id );
}
static inline void Abc_BddNandG1MspfReduce( Abc_NandMan * p, int id, int idj )
{
  Abc_BddNandBuildFanoutCone_Refresh( p, id );
  Abc_BddNandMspf_Refresh( p );
}
static inline void Abc_BddNandG1( Abc_NandMan * p, int fWeak, int fHalf )
{
  int i, j, id, idj;
  Vec_Int_t * targets, * targets2;
  targets = Vec_IntDup( p->vObjs );
  if ( fHalf )
    {
      targets2 = Vec_IntAlloc( 1 );
      Abc_BddNandMarkClear( p );  
      Vec_IntForEachEntryStart( p->vPos, id, i, Vec_IntSize( p->vPos ) / 2 )
	Abc_BddNandDescendantList_rec( p, p->pvFanins, targets2, id );
      Abc_BddNandSortList( p, targets2 );
    }
  else targets2 = Vec_IntDup( p->vObjs );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) continue;
      if ( p->nVerbose > 1 )
	printf( "G1 for %d in %d gates\n", i, Vec_IntSize(targets) );
      Abc_BddNandMarkClear( p );
      p->pMark[id] = 1;
      Abc_BddNandMarkDescendant_rec( p, p->pvFanouts, id );
      // try connecting each pi if possible
      Vec_IntForEachEntry( p->vPis, idj, j )
	{
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) break;
	  if ( Abc_BddNandTryConnect_Refresh( p, idj, id ) )
	    {
	      if ( fWeak ) Abc_BddNandG1WeakReduce( p, id, idj );	
	      else if ( p->nMspf > 1 ) Abc_BddNandG1MspfReduce( p, id, idj );	
	      else Abc_BddNandG1EagerReduce( p, id, idj );
	    }
	}
      // try connecting each candidate if possible
      Vec_IntForEachEntry( targets2, idj, j )
	{
	  if ( Abc_BddNandObjIsEmptyOrDead( p, id ) ) break;
	  if ( Abc_BddNandObjIsEmptyOrDead( p, idj ) ) continue;
	  if ( p->pMark[idj] ) continue;
	  if ( Abc_BddNandTryConnect_Refresh( p, idj, id ) )
	    {
	      if ( fWeak ) Abc_BddNandG1WeakReduce( p, id, idj );
	      else if ( p->nMspf > 1 ) Abc_BddNandG1MspfReduce( p, id, idj );
	      else Abc_BddNandG1EagerReduce( p, id, idj );
	    }
	}
      // recalculate fanouts for weak method
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
  Vec_Int_t * targets;
  new_id = Vec_IntSize( p->vPis ) + 1;
  while ( !Abc_BddNandObjIsEmpty( p, new_id ) )
    {
      new_id++;
      if ( new_id >= p->nObjsAlloc )
	{
	  printf("Error: Too many new merged nodes\n");
	  abort();
	}
    }
  targets = Vec_IntDup( p->vObjs );
  Abc_BddNandCspf_Refresh( p );
  // optimize
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( !i ) break;
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
	  a = Abc_BddOr( p->pBdd, f1, f0 );
	  b = Abc_BddOr( p->pBdd, gi, gj );
	  mergible = Abc_BddOr( p->pBdd, a, b );
	  if ( !Abc_BddLitIsConst1( mergible ) ) continue;
	  // create BDD of intersection. both F and G.
	  figj = Abc_BddAnd( p->pBdd, fi, gj );
	  fjgi = Abc_BddAnd( p->pBdd, fj, gi );
	  fx = Abc_BddOr( p->pBdd, figj, fjgi );
	  fx = Abc_BddOr( p->pBdd, fx, f1 );
	  gx = Abc_BddAnd( p->pBdd, gi, gj );
	  if ( Abc_BddLitIsInvalid( fx ) ) continue;
	  if ( Abc_BddLitIsInvalid( gx ) ) continue;
	  Abc_BddNandObjSetBddFunc( p, new_id, fx );
	  p->pGFuncs[new_id] = gx;
	  p->pvFanins[new_id] = Vec_IntAlloc( 1 );
	  p->pvFanouts[new_id] = Vec_IntAlloc( 1 );
	  // for all living nodes, if it is not included in fanouts of i and j, and i and j themselves, try connect it to new node.
	  Abc_BddNandMarkClear( p );
	  p->pMark[id] = 1;
	  p->pMark[idj] = 1;
	  Abc_BddNandMarkDescendant_rec( p, p->pvFanouts, id );
	  Abc_BddNandMarkDescendant_rec( p, p->pvFanouts, idj );
	  eq = Abc_BddOr( p->pBdd, Abc_BddLitNot( fx ), gx );
	  Value = Abc_BddLitConst1();
	  Vec_IntForEachEntry( p->vPis, idk, k ) 
	    if ( Abc_BddNandTryConnect( p, idk, new_id ) )
	      {
		if ( Abc_BddLitIsConst1( eq ) ) break;
		if ( Abc_BddLitIsInvalid( Value ) || Abc_BddLitIsInvalid( eq ) ) break;
		Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjGetBddFunc( p, idk ) );
		eq = Abc_BddOr( p->pBdd, eq, Abc_BddLitNot( Value ) );
	      }
	  Vec_IntForEachEntry( targets, idk, k )
	    {
	      if ( Abc_BddNandObjIsEmptyOrDead( p, idk ) ) continue;
	      if ( p->pMark[idj] ) continue;
	      if ( Abc_BddNandTryConnect( p, idk, new_id ) )
		{
		  if ( Abc_BddLitIsConst1( eq ) ) break;
		  if ( Abc_BddLitIsInvalid( Value ) || Abc_BddLitIsInvalid( eq ) ) break;
		  Value = Abc_BddAnd( p->pBdd, Value, Abc_BddNandObjGetBddFunc( p, idk ) );
		  eq = Abc_BddOr( p->pBdd, eq, Abc_BddLitNot( Value ) );
		}
	    }
	  if ( !Vec_IntSize( p->pvFanins[new_id] ) )
	    {
	      Abc_BddNandRemoveNode( p, new_id );
	      continue;
	    }
	  //assert( !Abc_BddNandCheck( p ) );
	  //assert( Abc_BddOr( p->pBdd, Abc_BddOr( p->pBdd, fx, gx ), Value ) == 1 );
	  // check the F of new node satisfies F and G.
	  if ( !Abc_BddLitIsConst1( eq ) )
	    {
	      Abc_BddNandRemoveNode( p, new_id );
	      continue;
	    }
	  //assert( Abc_BddOr( p->pBdd, Abc_BddOr( p->pBdd, fx^1, gx ), Value^1 ) == 1 );
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
	  out = Abc_BddNandRemoveRedundantFanin( p, new_id );
	  if ( Abc_BddNandObjIsEmptyOrDead( p, new_id ) ) continue;
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
}

/**Function*************************************************************
   
  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

p***********************************************************************/
static inline Gia_Man_t * Abc_BddNandNets2Gia( Vec_Ptr_t * vNets, Vec_Int_t * vPoCkts, Vec_Int_t * vPoIdxs, Vec_Int_t * vExternalCs, int fDc, Gia_Man_t * pOld )
{
  int i, j, k, id, idj, id0, id1, Value, cond, nPos;
  int * Values;
  int ** vvPoValues;
  Vec_Ptr_t * vDcGias;
  Gia_Obj_t * pObj;
  Gia_Man_t * pNew, * pTemp;
  Gia_Man_t ** pDcGias;
  Abc_NandMan * p;
  vvPoValues = ABC_CALLOC( int *, Vec_PtrSize( vNets ) + 1 );
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
      Values[id] = Gia_ManConst0Lit( pNew );
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
  pNew = Gia_ManCleanup( pTemp = pNew );
  Gia_ManStop( pTemp );
  if ( fDc )
    {
      nPos = Gia_ManCoNum( pOld ) / 2;
      pDcGias = ABC_CALLOC( Gia_Man_t *, nPos );
      p = Vec_PtrEntry( vNets, 0 );
      Vec_PtrForEachEntry( Vec_Ptr_t *, p->vvDcGias, vDcGias, i )
	pDcGias[i] = Vec_PtrEntry( vDcGias, 0 );
      pTemp = pNew;
      pNew = Gia_ManDupAppendCones( pNew, pDcGias, nPos, 0 );
      Gia_ManStop( pTemp );
      ABC_FREE( pDcGias );
    }
  for ( i = 0; i < Vec_PtrSize( vNets ) + 1; i++ )
    ABC_FREE( vvPoValues[i] );
  ABC_FREE( vvPoValues );
  return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_BddNandPropagateDc( Vec_Ptr_t * vNets, int from )
{
  int i, j, k, id, idj, pi, pij, index, best_i, best_pi;
  unsigned Value, c;
  Vec_Int_t ** pvPis;
  Vec_Int_t * vVars, * vNodes;
  Abc_NandMan * pFrom, * pTo;
  Gia_Man_t * pDc, * pTemp;
  vVars = Vec_IntAlloc( 1 );
  vNodes = Vec_IntAlloc( 1 );
  pFrom = Vec_PtrEntry( vNets, from );
  pvPis = ABC_CALLOC( Vec_Int_t *, Vec_PtrSize( vNets ) );
  for ( i = 0; i < Vec_PtrSize( vNets ); i++ )
    pvPis[i] = Vec_IntAlloc( 1 );
  Vec_IntForEachEntry( pFrom->vPis, id, pi )
    if ( Vec_IntEntry( pFrom->vPiCkts, pi ) != -1 )
      Vec_IntPush( pvPis[Vec_IntEntry( pFrom->vPiCkts, pi )], pi );
  Vec_PtrForEachEntry( Abc_NandMan *, vNets, pTo, k )
    {
      if ( !Vec_IntSize( pvPis[k] ) ) continue;
      Vec_IntForEachEntry( pvPis[k], pi, i )
	{
	  best_i = i;
	  best_pi = pi;
	  Vec_IntForEachEntryStart( pvPis[k], pij, j, i + 1 )
	    if ( Vec_IntEntry( pFrom->vPiIdxs, best_pi ) > Vec_IntEntry( pFrom->vPiIdxs, pij ) )
	      {
		best_i = j;
		best_pi = pij;
	      }
	  Vec_IntWriteEntry( pvPis[k], i, best_pi );
	  Vec_IntWriteEntry( pvPis[k], best_i, pi );
	}
      Vec_IntForEachEntry( pvPis[k], pi, i )
	{
	  id = Vec_IntEntry( pFrom->vPis, pi );
	  Value = Abc_BddLitConst1();
	  // calculate AND of G of fanouts
	  Vec_IntForEachEntry( pFrom->pvFanouts[id], idj, j )
	    {
	      if ( Abc_BddNandObjIsPo( pFrom, idj ) )
		Value = Abc_BddAnd( pFrom->pBdd, Value, pFrom->pGFuncs[idj] );
	      else
		{
		  index = Vec_IntFind( pFrom->pvFanins[idj], id );
		  c = (unsigned)Vec_IntEntry( pFrom->pvCFuncs[idj], index );
		  Value = Abc_BddAnd( pFrom->pBdd, Value, c );
		}
	    }
	  // universify the inputs of Value other than those in pvPis[i]
	  Vec_IntClear( vVars );
	  for ( pij = 0; pij < Vec_IntSize( pFrom->vPis ); pij++ )
	    if ( Vec_IntFind( pvPis[k], pij ) == -1 )
	      Vec_IntPush( vVars, pij );
	  Value = Abc_BddUnivAbstract( pFrom->pBdd, Value, vVars );
	  while ( Abc_BddLitIsInvalid( Value ) )
	    {
	      Abc_BddNandRefresh( pFrom );
	      Value = Abc_BddLitConst1();
	      Vec_IntForEachEntry( pFrom->pvFanouts[id], idj, j )
		{
		  if ( Abc_BddNandObjIsPo( pFrom, idj ) )
		    Value = Abc_BddAnd( pFrom->pBdd, Value, pFrom->pGFuncs[idj] );
		  else
		    {
		      index = Vec_IntFind( pFrom->pvFanins[idj], id );
		      c = (unsigned)Vec_IntEntry( pFrom->pvCFuncs[idj], index );
		      Value = Abc_BddAnd( pFrom->pBdd, Value, c );
		    }
		}
	      Value = Abc_BddUnivAbstract( pFrom->pBdd, Value, vVars );
	      pFrom->nMem++;
	      if ( 1 << pFrom->nMem == 0 )
		{
		  printf("Error: Calculating propagation of DC failed due to shortage of nodes\n");
		  abort();
		}
	    }
	  // gia on top of it
	  Vec_IntClear( vNodes );
	  Vec_IntPush( vNodes, Value );
	  pDc = Abc_Bdd2Gia( pFrom->pBdd, vNodes );
	  while( Gia_ManCiNum( pDc ) < Vec_IntSize( pTo->vPos ) )
	    {
	      Vec_IntPush( vVars, Gia_ManCiNum( pDc ) );
	      Gia_ManAppendCi( pDc );
	    }
	  Vec_IntForEachEntry( pvPis[k], pij, j )
	    Vec_IntInsert( vVars, Vec_IntEntry( pFrom->vPiIdxs, pij ), pij );
	  pTemp = pDc;
	  pDc = Gia_ManDupPerm( pDc, vVars );
	  Gia_ManStop( pTemp );
	  pTemp = pDc;
	  pDc = Gia_ManDupRemovePis( pDc, Gia_ManCiNum( pDc ) - Vec_IntSize( pTo->vPos ) );
	  Gia_ManStop( pTemp );
	  pTemp = pDc;
	  pDc = Gia_ManDupOntop( pTo->pGia, pDc );
	  Gia_ManStop( pTemp );
	  // push it to pTo->vvDcGias[pFrom->vPiIdxs[pi]]
	  Vec_PtrPush( Vec_PtrEntry( pTo->vvDcGias, Vec_IntEntry( pFrom->vPiIdxs, pi ) ), pDc );
	}
    }
  Vec_IntFree( vVars );
  Vec_IntFree( vNodes );
  for ( i = 0; i < Vec_PtrSize( vNets ); i++ )
    Vec_IntFree( pvPis[i] );
  ABC_FREE( pvPis );
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
Gia_Man_t * Abc_BddNandGiaTest( Gia_Man_t * pGia, int nMem, int nType, int fRm, int fRep, int fDc, int fSpec, int nWindowSize,int fDcPropagate, int nMspf, int nVerbose )
{
  int i, id, nPos;
  int * pPos;
  Abc_NandMan * p;
  Gia_Obj_t * pObj;
  Gia_Man_t * pNew;
  Vec_Ptr_t * vNets, * vDcGias;
  Vec_Int_t * vPoCkts, * vPoIdxs, * vExternalCs;
  vNets = Vec_PtrAlloc( 1 );
  vPoCkts = Vec_IntAlloc( 1 );
  vPoIdxs = Vec_IntAlloc( 1 );
  vExternalCs = Vec_IntAlloc( 1 );
  nPos = Gia_ManCoNum( pGia ) / 2;
  if ( !nWindowSize )
    {
      if ( fDc )
	{
	  pPos = ABC_CALLOC( int, nPos );
	  for ( i = 0; i < nPos; i++ )
	    pPos[i] = i;
	  pNew = Gia_ManDupCones( pGia, pPos, nPos, 0 );
	  ABC_FREE( pPos );
	}
      else
	pNew = Gia_ManDup( pGia );
      p = Abc_BddNandManAlloc( pNew, nMem, fRm, nMspf, nVerbose );
      Vec_IntForEachEntry( p->vPis, id, i )
	{
	  Vec_IntPush( p->vPiCkts, -1 );
	  Vec_IntPush( p->vPiIdxs, i );
	}
      Vec_PtrPush( vNets, p );
      Gia_ManForEachCo( pNew, pObj, i )
	{
	  Vec_IntPush( vExternalCs, 0 );
	  Vec_IntPush( vPoCkts, 0 );
	  Vec_IntPush( vPoIdxs, i );
	}
      if ( fDc )
	for ( i = nPos; i < nPos * 2; i++ )
	  {
	    vDcGias = Vec_PtrEntry( p->vvDcGias, i - nPos );
	    pNew = Gia_ManDupCones( pGia, &i, 1, 0 );
	    Vec_PtrPush( vDcGias, pNew );
	  }
    }
  else
    Abc_BddNandGia2Nets( pGia, vNets, vPoCkts, vPoIdxs, vExternalCs, nMem, fRm, nWindowSize, nMspf, nVerbose );
  // optimize
  abctime clk0 = Abc_Clock();
  Vec_PtrForEachEntry( Abc_NandMan *, vNets, p, i )
    {
      while ( ( 1 << p->nMem ) <= Vec_IntSize( p->vPis ) + 2 )
	{
	  p->nMem++;
	  if ( 1 << p->nMem == 0 )
	    {
	      printf("Error: Number of inputs is too large\n");
	      abort();
	    }
	}
      p->pBdd = Abc_BddManAlloc( Vec_IntSize( p->vPis ), 1 << p->nMem, (int)( nVerbose > 2 ) );
      while ( Abc_BddNandDc( p ) || Abc_BddNandBuildAll( p ) )
	{
	  p->nMem++;
	  if ( 1 << p->nMem == 0 )
	    {
	      printf("Error: Building Bdd failed\n");
	      abort();
	    }
	  Abc_BddManFree( p->pBdd );
	  p->pBdd = Abc_BddManAlloc( Vec_IntSize( p->vPis ), 1 << p->nMem, (int)( nVerbose > 2 ) );
	}
      if ( nVerbose ) Abc_BddNandPrintStats( p, "initial", clk0 );
      if ( p->nMspf ) Abc_BddNandMspf_Refresh( p );
      if ( p->nMspf < 2 ) Abc_BddNandCspfEager( p );
      if ( nVerbose ) Abc_BddNandPrintStats( p, "pf", clk0 );
      int wire = 0;
      while ( wire != Abc_BddNandCountWire( p ) )
	{
	  wire = Abc_BddNandCountWire( p );
	  switch ( nType ) {
	  case 0:
	    break;
	  case 1:
	    Abc_BddNandG1( p, 0, fSpec );
	    if ( nVerbose ) Abc_BddNandPrintStats( p, "g1", clk0 );
	    break;
	  case 2:
	    Abc_BddNandG1( p, 1, fSpec );
	    if ( nVerbose ) Abc_BddNandPrintStats( p, "g1-weak", clk0 );
	    break;
	  case 3:
	    Abc_BddNandG3( p );
	    if ( nVerbose ) Abc_BddNandPrintStats( p, "g3", clk0 );
	    break;
	  default:
	    printf( "Error: Invalid optimization type %d\n", nType );
	    abort();
	  }
	  if ( p->nMspf ) Abc_BddNandMspf_Refresh( p );
	  if ( p->nMspf < 2 ) Abc_BddNandCspfEager( p );
	  if ( !fRep ) break;
	}
      if ( fDcPropagate ) Abc_BddNandPropagateDc( vNets, i );
    }
  if ( nVerbose ) ABC_PRT( "total ", Abc_Clock() - clk0 );
  pNew = Abc_BddNandNets2Gia( vNets, vPoCkts, vPoIdxs, vExternalCs, fDc, pGia );
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

