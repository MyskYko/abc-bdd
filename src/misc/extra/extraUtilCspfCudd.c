/**CFile****************************************************************

  FileName    [extraUtilCspfCudd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [CSPF using CUDD]

  Author      [Yukio Miyasaka]
  
  Affiliation [The University of Tokyo]

  Date        []

  Revision    []

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "misc/vec/vec.h"
#include "aig/gia/gia.h"
#include "bdd/cudd/cuddInt.h"
#include "bdd/cudd/cudd.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline DdNode * Abc_DdAnd( DdManager * p, DdNode * a, DdNode * b, int nBddSizeMax )
{
  if ( Cudd_ReadKeys(p) - Cudd_ReadDead(p) > nBddSizeMax )
    {
      printf("Error: The number of nodes exceeds the limit\n");
      abort();
    }
  DdNode * r = Cudd_bddAndLimit( p, a, b, nBddSizeMax );
  if ( !r )
    {
      printf("Error: The number of nodes exceeds the limit\n");
      abort();
    }
  return r;
}
static inline DdNode * Abc_DdOr( DdManager * p, DdNode * a, DdNode * b, int nBddSizeMax )
{
  DdNode * c = Abc_DdAnd( p, Cudd_Not( a ), Cudd_Not( b ), nBddSizeMax );
  return Cudd_Not( c );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
typedef struct Abc_DdNandMan_ Abc_DdNandMan;
struct Abc_DdNandMan_ 
{
  int nGiaObjs;
  int nObjsAlloc;
  Vec_Int_t * vPis;
  Vec_Int_t * vPos;
  Vec_Int_t * vObjs;
  Vec_Int_t ** pvFanins;
  Vec_Int_t ** pvFanouts;
  DdNode ** pBddFuncs;
  
  int * pRanks;
  DdNode ** pGFuncs;
  Vec_Ptr_t ** pvCFuncs;

  DdManager * pDd;

  int nVerbose;

  int fDvr;
  int nBddSizeMax;
};

static inline int      Abc_DdNandCompl( Abc_DdNandMan * p, int id )    { return id + p->nGiaObjs;               }
static inline int      Abc_DdNandIsPiNode( Abc_DdNandMan * p, int id ) { return (int)( p->pvFanins[id] == 0 );  }
static inline int      Abc_DdNandIsPoNode( Abc_DdNandMan * p, int id ) { return (int)( p->pvFanouts[id] == 0 ); }
static inline DdNode * Abc_DdNandObjValue( Abc_DdNandMan * p, int id ) { return p->pBddFuncs[id];            }
static inline void     Abc_DdNandObjValueWrite( Abc_DdNandMan * p, int id, DdNode * Value ) { p->pBddFuncs[id] = Value; }

static inline int Abc_DdNandIsEmptyNode( Abc_DdNandMan * p, int id ) { return (int)( p->pvFanins[id] == 0 && p->pvFanouts[id] == 0 ); }
static inline int Abc_DdNandIsDeadNode( Abc_DdNandMan * p, int id )  { return (int)( Vec_IntSize( p->pvFanouts[id] ) == 0 );           }
static inline int Abc_DdNandIsEmptyOrDeadNode( Abc_DdNandMan * p, int id ) { return ( Abc_DdNandIsEmptyNode( p, id ) || Abc_DdNandIsDeadNode( p, id ) ); }

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_DdNandDescendantList_rec( Vec_Int_t ** children, Vec_Int_t * list, int id )
{
  int idj;
  int j, k;
  Vec_IntForEachEntry( children[id], idj, j )
    {
      k = Vec_IntFind( list, idj );
      if ( k == -1 && children[idj] != 0 )
	{ // idj is not in list and is not leaf
	  Vec_IntPush( list, idj );
	  Abc_DdNandDescendantList_rec( children, list, idj );
	}
    }
}
static inline void Abc_DdNandDescendantSortedList( Abc_DdNandMan * p, Vec_Int_t ** children, Vec_Int_t * sortedList, int parent )
{
  int id;
  int i;
  Vec_Int_t * list = Vec_IntAlloc( 1 );
  Abc_DdNandDescendantList_rec( children, list, parent );
  Vec_IntForEachEntry( p->vObjs, id, i )
    {
      int index = Vec_IntFind( list, id );
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
void Abc_DdNandInsertLivingNode( Abc_DdNandMan * p, int id )
{
  int index = Vec_IntSize( p->vObjs );
  int idj;
  int j;
  Vec_IntForEachEntry( p->pvFanouts[id], idj, j )
    {
      int index_ = Vec_IntFind( p->vObjs, idj );
      if ( index_ != -1 && index_ < index ) index = index_;
    }
  Vec_IntInsert( p->vObjs, index, id );
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      int index_ = Vec_IntFind( p->vObjs, idj );
      if ( index_ > index )
	{
	  Vec_IntDrop( p->vObjs, index_ );
	  Abc_DdNandInsertLivingNode( p, idj );
	  index = Vec_IntFind( p->vObjs, id );
	}
    }
}
static inline void Abc_DdNandConnect( Abc_DdNandMan * p, int fanin, int fanout, int fSort )
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
	  Abc_DdNandInsertLivingNode( p, fanin );
	}
    }
}
static inline void Abc_DdNandDisconnect( Abc_DdNandMan * p, int fanin, int fanout )
{
  Vec_IntRemove( p->pvFanins[fanout], fanin );    
  Vec_IntRemove( p->pvFanouts[fanin], fanout );
}
static inline void Abc_DdNandRemoveNode( Abc_DdNandMan * p, int id )
{
  int j, idj;
  DdNode * x;
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    Vec_IntRemove( p->pvFanouts[idj], id );
  Vec_IntForEachEntry( p->pvFanouts[id], idj, j )
    Vec_IntRemove( p->pvFanins[idj], id );
  Vec_IntFree( p->pvFanins[id] );
  Vec_IntFree( p->pvFanouts[id] );
  p->pvFanins[id] = 0;
  p->pvFanouts[id] = 0;
  if( p->pBddFuncs[id] )
    {
      Cudd_RecursiveDeref( p->pDd, p->pBddFuncs[id] );
      p->pBddFuncs[id] = NULL;
    }
  // TODO deref G and C
  if ( p->pGFuncs[id] )
    Cudd_RecursiveDeref( p->pDd, p->pGFuncs[id] );
  if ( p->pvCFuncs[id] )
    {
      Vec_PtrForEachEntry( DdNode *, p->pvCFuncs[id], x, j )
	Cudd_RecursiveDeref( p->pDd, x );
      Vec_PtrClear( p->pvCFuncs[id] );
    }
  Vec_IntRemove( p->vObjs, id );
}
static inline int Abc_DdNandCountWire( Abc_DdNandMan * p )
{
  int i, id, count = 0;
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
static inline void Abc_DdNandGenNet( Abc_DdNandMan * p, Gia_Man_t * pGia )
{
  int i, id, idj, id0, id1;
  Gia_Obj_t * pObj, * pObj0, * pObj1;
  // constant
  id = 0;
  p->pvFanins[id] = 0;
  p->pvFanouts[id] = Vec_IntAlloc( 1 );
  idj = Abc_DdNandCompl( p, id );
  p->pvFanins[idj] = 0;
  p->pvFanouts[idj] = Vec_IntAlloc( 1 );
  // pi
  Gia_ManForEachCi( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      p->pvFanins[id] = 0;
      p->pvFanouts[id] = Vec_IntAlloc( 1 );
      Vec_IntPush( p->vPis, id );
      idj = Abc_DdNandCompl( p, id );
      p->pvFanins[idj] = Vec_IntAlloc( 1 );
      p->pvFanouts[idj] = Vec_IntAlloc( 1 );
      Abc_DdNandConnect( p, id, idj, 0 );
      Vec_IntPush( p->vObjs, idj );
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
	id0 = Abc_DdNandCompl( p, id0 );
      Abc_DdNandConnect( p, id0, id, 0 );
      if ( (  Gia_ObjIsCi( pObj1 ) &&  Gia_ObjFaninC1( pObj ) ) ||
	   ( !Gia_ObjIsCi( pObj1 ) && !Gia_ObjFaninC1( pObj ) ) )  
	id1 = Abc_DdNandCompl( p, id1 );
      Abc_DdNandConnect( p, id1, id, 0 );
      Vec_IntPush( p->vObjs, id );
      idj = Abc_DdNandCompl( p, id );
      p->pvFanins[idj] = Vec_IntAlloc( 1 );
      p->pvFanouts[idj] = Vec_IntAlloc( 1 );
      Abc_DdNandConnect( p, id, idj, 0 );
      Vec_IntPush( p->vObjs, idj );    
    }
  // po
  Gia_ManForEachCo( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      p->pvFanins[id] = Vec_IntAlloc( 1 );
      p->pvFanouts[id] = 0;
      pObj0 = Gia_ObjFanin0( pObj );
      id0 = Gia_ObjId( pGia, pObj0 );
      if ( (  ( id0 == 0 || Gia_ObjIsCi( pObj0 ) ) &&  Gia_ObjFaninC0( pObj ) ) ||
	   ( !( id0 == 0 || Gia_ObjIsCi( pObj0 ) ) && !Gia_ObjFaninC0( pObj ) ) )
	id0 = Abc_DdNandCompl( p, id0 );
      Abc_DdNandConnect( p, id0, id, 0 );
      Vec_IntPush( p->vPos, id );
    }
  // remove redundant nodes
  Vec_IntForEachEntry( p->vObjs, id, i )
    if ( Abc_DdNandIsDeadNode( p, id ) )
      Abc_DdNandRemoveNode( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_DdNandMan * Abc_DdNandManAlloc( Gia_Man_t * pGia, int fDvr, int nVerbose )
{
  Abc_DdNandMan * p = ABC_CALLOC( Abc_DdNandMan, 1 );
  p->nGiaObjs = pGia->nObjs;
  p->nObjsAlloc = pGia->nObjs + pGia->nObjs;
  p->vPis = Vec_IntAlloc( Gia_ManCiNum( pGia ) );
  p->vPos = Vec_IntAlloc( Gia_ManCoNum( pGia ) );
  p->pvFanins = ABC_CALLOC( Vec_Int_t *, p->nObjsAlloc );
  p->pvFanouts = ABC_CALLOC( Vec_Int_t *, p->nObjsAlloc );
  p->pBddFuncs = ABC_CALLOC( DdNode *, p->nObjsAlloc );
  p->vObjs = Vec_IntAlloc( 1 );
  p->pRanks = ABC_CALLOC( int, p->nObjsAlloc );
  p->pGFuncs = ABC_CALLOC( DdNode *, p->nObjsAlloc );
  p->pvCFuncs = ABC_CALLOC( Vec_Ptr_t *, p->nObjsAlloc );
  p->nVerbose = nVerbose;
  p->fDvr = fDvr;
  p->nBddSizeMax = 0x7fffffff;
  return p;
}
static inline void Abc_DdManAlloc( Abc_DdNandMan * p )
{
  int i, id, idj;
  p->pDd = Cudd_Init( Vec_IntSize( p->vPis ), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
  if ( !p->pDd )
    {
      printf("Error: Allocation failed\n");
      abort();
    }
  if ( p->fDvr ) Cudd_AutodynEnable( p->pDd, CUDD_REORDER_SYMM_SIFT );
  id = 0;
  Abc_DdNandObjValueWrite( p, id, Cudd_Not( p->pDd->one ) );
  idj = Abc_DdNandCompl( p, id );
  Abc_DdNandObjValueWrite( p, idj, p->pDd->one );
  // pi
  Vec_IntForEachEntry( p->vPis, id, i )
    Abc_DdNandObjValueWrite( p, id, p->pDd->vars[i] );
}
static inline void Abc_DdNandManFree( Abc_DdNandMan * p )
{
  int i;
  Cudd_Quit( p->pDd );
  Vec_IntFree( p->vPis );
  Vec_IntFree( p->vPos );
  for ( i = 0; i < p->nObjsAlloc; i++ )
    {
      if ( p->pvFanins[i] )
	Vec_IntFree( p->pvFanins[i] );
      if ( p->pvFanouts[i] )
	Vec_IntFree( p->pvFanouts[i] );
    }
  ABC_FREE( p->pvFanins );
  ABC_FREE( p->pvFanouts );
  ABC_FREE( p->pBddFuncs );
  Vec_IntFree( p->vObjs );
  ABC_FREE( p->pRanks );
  ABC_FREE( p->pGFuncs );
  for ( i = 0; i < p->nObjsAlloc; i++ )
    if ( p->pvCFuncs[i] )
      Vec_PtrFree( p->pvCFuncs[i] );
  ABC_FREE( p->pvCFuncs );
  ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_DdNandPrintNet( Abc_DdNandMan * p )
{
  int i, j, k;
  int id, idj;
  FILE *fp;
  fp = fopen( "test.blif", "w" );
  fprintf( fp, ".model test\n" );
  fprintf( fp, ".inputs" );
  Vec_IntForEachEntry( p->vPis, id, i )
    fprintf( fp, " pi%d", id - 1 );
  fprintf( fp, "\n.outputs" );
  Vec_IntForEachEntry( p->vPos, id, i )
    fprintf( fp, " po%d", i );
  fprintf( fp, "\n" );
  fprintf( fp, ".names const0\n0\n" );
  fprintf( fp, ".names const1\n1\n" );
  Vec_IntForEachEntry( p->vObjs, id, i )
    if ( p->pvFanins[id]                 != 0 &&
	 p->pvFanouts[id]                != 0 &&
	 Vec_IntSize( p->pvFanins[id] )  != 0 &&
	 Vec_IntSize( p->pvFanouts[id] ) != 0 )
      {
	fprintf( fp,".names " );
	Vec_IntForEachEntry( p->pvFanins[id], idj, j )
	  if ( idj == 0 )
	    fprintf( fp, "const0 " );	  
	  else if ( idj == Abc_DdNandCompl( p, 0 ) )
	    fprintf( fp, "const1 " );
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
      else if ( idj == Abc_DdNandCompl( p, 0 ) )
	fprintf( fp, "const1 " );
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
static inline void Abc_DdNandRank( Abc_DdNandMan * p, int id )
{
  if ( Abc_DdNandIsPiNode( p, id ) )
    {
      p->pRanks[id] = 1 << 30; // assume this is max
      return;
    }
  p->pRanks[id] = Vec_IntSize( p->pvFanouts[id] );
  assert( p->pRanks[id] >= 0 );
}
static inline void Abc_DdNandRankAll( Abc_DdNandMan * p )
{
  int i, id;
  Vec_IntForEachEntry( p->vPis, id, i ) 
    Abc_DdNandRank( p, id );
  Vec_IntForEachEntry( p->vObjs, id, i )
    Abc_DdNandRank( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_DdNandSortFanin( Abc_DdNandMan * p, int id )
{
  int j, k, idj, idk, best_j, best_idj;
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      best_j = j;
      best_idj = idj;
      Vec_IntForEachEntryStart( p->pvFanins[id], idk, k, j+1 )
	if ( p->pRanks[idj] > p->pRanks[idk] )
	  {
	    best_j = k;
	    best_idj = idk;
	  }
      Vec_IntWriteEntry( p->pvFanins[id], j, best_idj );
      Vec_IntWriteEntry( p->pvFanins[id], best_j, idj );
    }
}
static inline void Abc_DdNandSortFaninAll( Abc_DdNandMan * p )
{
  int i, id;
  Vec_IntForEachEntry( p->vObjs, id, i )
    Abc_DdNandSortFanin( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_DdNandBuild( Abc_DdNandMan * p, int id )
{
  int j, idj;
  DdNode * Value, * Value_;
  if ( Abc_DdNandObjValue( p, id ) )
    Cudd_RecursiveDeref( p->pDd, Abc_DdNandObjValue( p, id ) );
  Value_ = p->pDd->one;
  Cudd_Ref( Value_ );
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      Value = Abc_DdAnd( p->pDd, Value_, Abc_DdNandObjValue( p, idj ), p->nBddSizeMax );
      Cudd_Ref( Value );
      Cudd_RecursiveDeref( p->pDd, Value_ );
      Value_ = Value;
    }
  Abc_DdNandObjValueWrite( p, id, Cudd_Not( Value_ ) );
}
static inline void Abc_DdNandBuildAll( Abc_DdNandMan * p )
{
  int i, id;
  Vec_IntForEachEntry( p->vObjs, id, i )
    Abc_DdNandBuild( p, id );
}
static inline void Abc_DdNandBuildFanoutCone( Abc_DdNandMan * p, int startId )
{
  int i, id;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  Vec_IntPush( targets, startId );
  Abc_DdNandDescendantSortedList( p, p->pvFanouts, targets, startId );
  Vec_IntForEachEntry( targets, id, i )
    Abc_DdNandBuild( p, id );
  Vec_IntFree( targets );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_DdNandCspfG( Abc_DdNandMan * p, int id )
{
  int j, idj, index;
  DdNode * Value, * c;
  if ( p->pGFuncs[id] )
    Cudd_RecursiveDeref( p->pDd, p->pGFuncs[id] );
  p->pGFuncs[id] = p->pDd->one;
  Cudd_Ref( p->pGFuncs[id] );
  Vec_IntForEachEntry( p->pvFanouts[id], idj, j )
    {
      if ( Abc_DdNandIsPoNode( p, idj ) )
	{// G[idj] will be 0 unless po dont care is given.
	  if ( !p->pGFuncs[idj] )
	    Value = Cudd_Not( p->pDd->one );
	  else
	    Value = Abc_DdAnd( p->pDd, p->pGFuncs[id], p->pGFuncs[idj], p->nBddSizeMax );
	}
      else
	{
	  index = Vec_IntFind( p->pvFanins[idj], id );
	  assert( index >= 0 );
	  //	  assert( Vec_IntSize( p->pvFanins[idj] ) == Vec_IntSize( p->C[idj] ) );
	  c = Vec_PtrEntry( p->pvCFuncs[idj], index );
	  Value = Abc_DdAnd( p->pDd, p->pGFuncs[id], c, p->nBddSizeMax );
	}
      Cudd_Ref( Value );
      Cudd_RecursiveDeref( p->pDd, p->pGFuncs[id] );
      p->pGFuncs[id] = Value;
    }
}
static inline void Abc_DdNandCspfC( Abc_DdNandMan * p, int id ) {
  int i, j, k, idj, idk;
  DdNode * x, * fanins, * fk, * Value, * fi, * fj, * already1, * c, * DC1;
  if ( !p->pvCFuncs[id] ) p->pvCFuncs[id] = Vec_PtrAlloc( 1 );
  Vec_PtrForEachEntry( DdNode *, p->pvCFuncs[id], x, i )
    Cudd_RecursiveDeref( p->pDd, x );
  Vec_PtrClear( p->pvCFuncs[id] );
  Vec_IntForEachEntry( p->pvFanins[id], idj, j )
    {
      fanins = p->pDd->one;
      Cudd_Ref( fanins );
      Vec_IntForEachEntryStart( p->pvFanins[id], idk, k, j+1 )
	{
	  fk = Abc_DdNandObjValue( p, idk );
	  Value = Abc_DdAnd( p->pDd, fanins, fk, p->nBddSizeMax );
	  Cudd_Ref( Value );
	  Cudd_RecursiveDeref( p->pDd, fanins );
	  fanins = Value;
	}
      fi = Abc_DdNandObjValue( p, id );
      fj = Abc_DdNandObjValue( p, idj );
      already1 = Abc_DdAnd( p->pDd, fi, fj, p->nBddSizeMax );
      Cudd_Ref( already1 );
      c = Abc_DdOr( p->pDd, p->pGFuncs[id], Cudd_Not( fanins ), p->nBddSizeMax );
      Cudd_Ref( c );
      Cudd_RecursiveDeref( p->pDd, fanins );
      Value = Abc_DdOr( p->pDd, c, already1, p->nBddSizeMax );
      Cudd_Ref( Value );
      Cudd_RecursiveDeref( p->pDd, already1 );
      Cudd_RecursiveDeref( p->pDd, c );
      DC1 = Abc_DdOr( p->pDd, fj, Value, p->nBddSizeMax );
      Cudd_Ref( DC1 );
      if ( DC1 == p->pDd->one )
	{
	  Cudd_RecursiveDeref( p->pDd, Value );
	  Cudd_RecursiveDeref( p->pDd, DC1 );
	  Abc_DdNandDisconnect( p, idj, id );
	  if ( Vec_IntSize( p->pvFanins[id] ) == 0 )
	    {
	      Vec_IntForEachEntry( p->pvFanouts[id], idk, k )
		if ( Vec_IntFind( p->pvFanins[idk], 0 ) == -1 )
		  Abc_DdNandConnect( p, 0, idk, 0 );
	      Abc_DdNandRemoveNode( p, id );
	      return;
	    }
	  j--;
	  continue;
	}
      Cudd_RecursiveDeref( p->pDd, DC1 );
      Vec_PtrPush( p->pvCFuncs[id], Value );
    }
}
static inline void Abc_DdNandCspf( Abc_DdNandMan * p )
{
  int i, id;
  Vec_IntForEachEntryReverse( p->vObjs, id, i )
    {
      if ( Abc_DdNandIsDeadNode( p, id ) )
	{ // remove the node
	  Abc_DdNandRemoveNode( p, id );
	  continue;
	}
      Abc_DdNandCspfG( p, id );
      Abc_DdNandCspfC( p, id );
    }
  return Abc_DdNandBuildAll( p );
}
static inline void Abc_DdNandCspfFaninCone( Abc_DdNandMan * p, int startId )
{
  int i, id;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  Abc_DdNandDescendantSortedList( p, p->pvFanins, targets, startId );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Abc_DdNandIsDeadNode( p, id ) )
	{ // remove the node
	  Abc_DdNandRemoveNode( p, id );
	  continue;
	}
      Abc_DdNandCspfG( p, id );
      Abc_DdNandCspfC( p, id );
    }
  Vec_IntFree( targets );
  Abc_DdNandBuildAll( p );
}

/**Function*************************************************************
   
  Synopsis    [minimization methods]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_DdNandCspfEager( Abc_DdNandMan * p )
{
  int wires = 0;
  while ( wires != Abc_DdNandCountWire( p ) )
    {
      wires = Abc_DdNandCountWire( p );
      Abc_DdNandRankAll( p );
      Abc_DdNandSortFaninAll( p );
      Abc_DdNandCspf( p );
    }
}

/**Function*************************************************************
   
  Synopsis    [minimization methods]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_DdNandTryConnect( Abc_DdNandMan * p, int fanin, int fanout )
{
  if ( Vec_IntFind( p->pvFanins[fanout], fanin ) != -1 ) return 0; // already connected
  DdNode * ffanin = Abc_DdNandObjValue( p, fanin );
  DdNode * ffanout = Abc_DdNandObjValue( p, fanout );
  DdNode * gfanout = p->pGFuncs[fanout];
  DdNode * connectable = Abc_DdOr( p->pDd, ffanout, gfanout, p->nBddSizeMax );
  Cudd_Ref( connectable );
  DdNode * Value = Abc_DdOr( p->pDd, ffanin, connectable, p->nBddSizeMax );
  Cudd_Ref( Value );
  Cudd_RecursiveDeref( p->pDd, connectable );
  connectable = Value;
  if ( connectable == p->pDd->one )
    {
      Abc_DdNandConnect( p, fanin, fanout, 1 );
      Cudd_RecursiveDeref( p->pDd, connectable );
      return 1;
    }
  Cudd_RecursiveDeref( p->pDd, connectable );
  return 0;
}
/**Function*************************************************************
   
  Synopsis    [minimization methods]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_DdNandG1EagerReduce( Abc_DdNandMan * p, int id, int idj )
{
  int wire =  Abc_DdNandCountWire( p );
  Abc_DdNandCspfC( p, id );
  if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) return;
  Abc_DdNandCspfFaninCone( p, id );
  if ( wire == Abc_DdNandCountWire( p ) )
    {
      Abc_DdNandDisconnect( p, idj, id );
      Abc_DdNandBuildFanoutCone( p, id );
      Abc_DdNandCspfC( p, id );
      if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) return;
      Abc_DdNandCspfFaninCone( p, id );
      return;
    }
  Abc_DdNandBuildAll( p );
  Abc_DdNandCspfEager( p );
}
static inline void Abc_DdNandG1( Abc_DdNandMan * p )
{
  int i, j, id, idj;
  Vec_Int_t * targets = Vec_IntDup( p->vObjs );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) continue;
      if ( p->nVerbose >= 2 )
	{
	  printf( "\rG1 for %d in %d gates", i, Vec_IntSize(targets) );
	  fflush( stdout );
	}
      Vec_Int_t * fanouts = Vec_IntAlloc( 1 );
      Abc_DdNandDescendantList_rec( p->pvFanouts, fanouts, id );
      // try connecting pi
      Vec_IntForEachEntry( p->vPis, idj, j )
	{
	  if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) break;
	  if ( Abc_DdNandTryConnect( p, idj, id ) )
	    Abc_DdNandG1EagerReduce( p, id, idj );
	}
      // try connecting candidate
      Vec_IntForEachEntry( targets, idj, j )
	{
	  if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) break;
	  if ( Abc_DdNandIsEmptyOrDeadNode( p, idj ) ) continue;
	  if ( id == idj ) continue;
	  if ( Vec_IntFind( fanouts, idj ) != -1 ) continue;
	  if ( Abc_DdNandTryConnect( p, idj, id ) )
	    Abc_DdNandG1EagerReduce( p, id, idj );
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
static inline void Abc_DdNandPrintStats( Abc_DdNandMan * p, char * prefix, abctime clk0 )
{
  printf( "\r%-10s: gates = %5d, wires = %5d, AIG node = %5d", prefix, Vec_IntSize( p->vObjs ), Abc_DdNandCountWire( p ), Abc_DdNandCountWire( p ) - Vec_IntSize( p->vObjs ) );
  ABC_PRT( ", time ", Abc_Clock() - clk0 );
}
void Abc_DdNandGiaTest( Gia_Man_t * pGia, int nType, int fDvr, int fRep, int nVerbose )
{
  int wire;
  Abc_DdNandMan * p = Abc_DdNandManAlloc( pGia, fDvr, nVerbose );
  Abc_DdNandGenNet( p, pGia );
  Abc_DdManAlloc( p );
  //  printf( "%d\n", Cudd_ReadKeys(p->pDd) - Cudd_ReadDead(p->pDd) );
  abctime clk0 = Abc_Clock();
  Abc_DdNandBuildAll( p );
  if ( nVerbose ) Abc_DdNandPrintStats( p, "initial", clk0 );
  Abc_DdNandCspfEager( p );
  if ( nVerbose ) Abc_DdNandPrintStats( p, "cspf", clk0 );  
  wire = 0;
  while ( wire != Abc_DdNandCountWire( p ) )
    {
      wire = Abc_DdNandCountWire( p );
      switch ( nType )
	{
	case 1:
	  Abc_DdNandG1( p );
	  if ( nVerbose ) Abc_DdNandPrintStats( p, "g1", clk0 );
	  break;
	default:
	  break;
	}
      Abc_DdNandCspfEager( p );
      if ( !fRep )
	break;
    }
  if ( nVerbose ) ABC_PRT( "total ", Abc_Clock() - clk0 );
  Abc_DdNandPrintNet( p );
  /*  
  int i, j, id;
  Vec_IntForEachEntry( p->vObjs, id, i )
    {
      Abc_DdNandRemoveNode( p, id );
      i--;
    }
  printf( "%d\n", Cudd_ReadKeys(p->pDd) - Cudd_ReadDead(p->pDd) );
  */
  Abc_DdNandManFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
