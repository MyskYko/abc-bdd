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
  if ( a == NULL || b == NULL ) return NULL;
  if ( Cudd_ReadKeys(p) - Cudd_ReadDead(p) > nBddSizeMax ) return NULL;
  return Cudd_bddAndLimit( p, a, b, nBddSizeMax );
}
static inline DdNode * Abc_DdOr( DdManager * p, DdNode * a, DdNode * b, int nBddSizeMax )
{
  if ( a == NULL || b == NULL ) return NULL;
  DdNode * c = Abc_DdAnd( p, Cudd_Not( a ), Cudd_Not( b ), nBddSizeMax );
  if( c == NULL ) return NULL;
  return Cudd_Not( c );
}
static inline void Abc_DdRef( DdNode * a, char * where ) { Cudd_Ref( a ); }
static inline void Abc_DdDeref( DdManager * p, DdNode * a, char * where ) { Cudd_RecursiveDeref( p, a ); }
int Abc_DdCount0s( DdManager * p, DdNode* a, int depth )
{
  if ( Cudd_ReadSize( p ) - depth < 0 ) return 0;
  DdNode * node = Cudd_Regular(a);
  if ( cuddIsConstant( node ) )
    return (int)Cudd_IsComplement(a) << (Cudd_ReadSize( p ) - depth);
  if ( Cudd_IsComplement( a ) )
    return Abc_DdCount0s( p, Cudd_Not( cuddE( node ) ), depth + 1 ) + Abc_DdCount0s( p, Cudd_Not( cuddT( node ) ), depth + 1 );
  return Abc_DdCount0s( p, cuddE( node ), depth + 1 ) + Abc_DdCount0s( p, cuddT( node ), depth + 1 );
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
  Vec_Int_t * pis;
  Vec_Int_t * pos;
  Vec_Int_t ** faninList;
  Vec_Int_t ** fanoutList;
  DdNode ** newNodeValues;
  Vec_Int_t * livingNodes;
  int * rank;
  DdNode ** G;
  DdNode *** C;
  int * Csize;
  int nMemMax;
  int nBddSizeMax;
  DdManager * pDd;
  char * filename;
  int nVerbose;
  int nOpt;
  int fDvr;
};

static inline int      Abc_DdNandCompl( Abc_DdNandMan * p, int id )    { return id + p->nGiaObjs;                }
static inline int      Abc_DdNandIsPiNode( Abc_DdNandMan * p, int id ) { return (int)( p->faninList[id] == 0 );  }
static inline int      Abc_DdNandIsPoNode( Abc_DdNandMan * p, int id ) { return (int)( p->fanoutList[id] == 0 ); }
static inline DdNode * Abc_DdNandObjValue( Abc_DdNandMan * p, int id ) { return p->newNodeValues[id];            }
static inline void     Abc_DdNandObjValueWrite( Abc_DdNandMan * p, int id, DdNode * Value ) { p->newNodeValues[id] = Value; }
static inline int      Abc_DdNandCount0s( Abc_DdNandMan * p, int id, int nOverflow ) { return Abc_DdCount0s( p->pDd, Abc_DdNandObjValue( p, id ), nOverflow ); }

static inline int Abc_DdNandIsEmptyNode( Abc_DdNandMan * p, int id ) { return (int)( p->faninList[id] == 0 && p->fanoutList[id] == 0 ); }
static inline int Abc_DdNandIsDeadNode( Abc_DdNandMan * p, int id )  { return (int)( Vec_IntSize( p->fanoutList[id] ) == 0 );           }
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
  Vec_IntForEachEntry( p->livingNodes, id, i )
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
  int index = Vec_IntSize( p->livingNodes );
  int idj;
  int j;
  Vec_IntForEachEntry( p->fanoutList[id], idj, j )
    {
      int index_ = Vec_IntFind( p->livingNodes, idj );
      if ( index_ != -1 && index_ < index ) index = index_;
    }
  Vec_IntInsert( p->livingNodes, index, id );
  Vec_IntForEachEntry( p->faninList[id], idj, j )
    {
      int index_ = Vec_IntFind( p->livingNodes, idj );
      if ( index_ > index )
	{
	  Vec_IntDrop( p->livingNodes, index_ );
	  Abc_DdNandInsertLivingNode( p, idj );
	  index = Vec_IntFind( p->livingNodes, id );
	}
    }
}
static inline void Abc_DdNandConnect( Abc_DdNandMan * p, int fanin, int fanout, int fSort )
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
	  Abc_DdNandInsertLivingNode( p, fanin );
	}
    }
}
static inline void Abc_DdNandDisconnect( Abc_DdNandMan * p, int fanin, int fanout )
{
  Vec_IntRemove( p->faninList[fanout], fanin );    
  Vec_IntRemove( p->fanoutList[fanin], fanout );
}
static inline void Abc_DdNandRemoveNode( Abc_DdNandMan * p, int id )
{
  int j;
  int idj;
  Vec_IntForEachEntry( p->faninList[id], idj, j )
    Vec_IntRemove( p->fanoutList[idj], id );
  Vec_IntForEachEntry( p->fanoutList[id], idj, j )
    Vec_IntRemove( p->faninList[idj], id );
  Vec_IntFree( p->faninList[id] );
  Vec_IntFree( p->fanoutList[id] );
  p->faninList[id] = 0;
  p->fanoutList[id] = 0;
  if( p->newNodeValues[id] != NULL )
    {
      Abc_DdDeref( p->pDd, p->newNodeValues[id], "rmnode" );
      p->newNodeValues[id] = NULL;
    }
  Vec_IntRemove( p->livingNodes, id );
}
static inline int Abc_DdNandCountWire( Abc_DdNandMan * p )
{
  int i;
  int id;
  int count = 0;
  Vec_IntForEachEntry( p->livingNodes, id, i )
    count += Vec_IntSize( p->faninList[id] );
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
  Gia_Obj_t * pObj;
  int i;
  int id, idj;
  // constant
  id = 0;
  p->faninList[id] = 0;
  p->fanoutList[id] = Vec_IntAlloc( 1 );
  idj = Abc_DdNandCompl( p, id );
  p->faninList[idj] = 0;
  p->fanoutList[idj] = Vec_IntAlloc( 1 );
  // pi
  Gia_ManForEachCi( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      p->faninList[id] = 0;
      p->fanoutList[id] = Vec_IntAlloc( 1 );
      Vec_IntPush( p->pis, id );
      idj = Abc_DdNandCompl( p, id );
      p->faninList[idj] = Vec_IntAlloc( 1 );
      p->fanoutList[idj] = Vec_IntAlloc( 1 );
      Abc_DdNandConnect( p, id, idj, 0 );
      Vec_IntPush( p->livingNodes, idj );
    }
  // gate
  Gia_ManForEachAnd( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      p->faninList[id] = Vec_IntAlloc( 1 );
      p->fanoutList[id] = Vec_IntAlloc( 1 );
      Gia_Obj_t * pObj0 = Gia_ObjFanin0( pObj );
      Gia_Obj_t * pObj1 = Gia_ObjFanin1( pObj );
      int id0 = Gia_ObjId( pGia, pObj0 );
      int id1 = Gia_ObjId( pGia, pObj1 );
      if ( (  Gia_ObjIsCi( pObj0 ) &&  Gia_ObjFaninC0( pObj ) ) ||
	   ( !Gia_ObjIsCi( pObj0 ) && !Gia_ObjFaninC0( pObj ) ) )
	id0 = Abc_DdNandCompl( p, id0 );
      Abc_DdNandConnect( p, id0, id, 0 );
      if ( (  Gia_ObjIsCi( pObj1 ) &&  Gia_ObjFaninC1( pObj ) ) ||
	   ( !Gia_ObjIsCi( pObj1 ) && !Gia_ObjFaninC1( pObj ) ) )  
	id1 = Abc_DdNandCompl( p, id1 );
      Abc_DdNandConnect( p, id1, id, 0 );
      Vec_IntPush( p->livingNodes, id );
      idj = Abc_DdNandCompl( p, id );
      p->faninList[idj] = Vec_IntAlloc( 1 );
      p->fanoutList[idj] = Vec_IntAlloc( 1 );
      Abc_DdNandConnect( p, id, idj, 0 );
      Vec_IntPush( p->livingNodes, idj );    
    }
  // po
  Gia_ManForEachCo( pGia, pObj, i )
    {
      id = Gia_ObjId( pGia, pObj );
      p->faninList[id] = Vec_IntAlloc( 1 );
      p->fanoutList[id] = 0;
      Gia_Obj_t * pObj0 = Gia_ObjFanin0( pObj );
      int id0 = Gia_ObjId( pGia, pObj0 );
      if ( (  ( id0 == 0 || Gia_ObjIsCi( pObj0 ) ) &&  Gia_ObjFaninC0( pObj ) ) ||
	   ( !( id0 == 0 || Gia_ObjIsCi( pObj0 ) ) && !Gia_ObjFaninC0( pObj ) ) )
	id0 = Abc_DdNandCompl( p, id0 );
      Abc_DdNandConnect( p, id0, id, 0 );
      Vec_IntPush( p->pos, id );
    }
  // remove redundant nodes
  Vec_IntForEachEntry( p->livingNodes, id, i )
    if ( Vec_IntSize( p->fanoutList[id] ) == 0 )
      Abc_DdNandRemoveNode( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Abc_DdNandMan * Abc_DdNandManAlloc( Gia_Man_t * pGia, char * Filename, int nMem, int nMemMax, int nOpt, int fDvr, int nVerbose )
{
  Abc_DdNandMan * p = ABC_CALLOC( Abc_DdNandMan, 1 );
  p->nGiaObjs = pGia->nObjs;
  p->pis = Vec_IntAlloc( Gia_ManCiNum( pGia ) );
  p->pos = Vec_IntAlloc( Gia_ManCoNum( pGia ) );
  p->faninList = ABC_CALLOC( Vec_Int_t *, p->nGiaObjs + p->nGiaObjs );
  p->fanoutList = ABC_CALLOC( Vec_Int_t *, p->nGiaObjs + p->nGiaObjs );
  p->newNodeValues = ABC_CALLOC( DdNode *, p->nGiaObjs + p->nGiaObjs );
  p->livingNodes = Vec_IntAlloc( 1 );
  p->rank = ABC_CALLOC( int, p->nGiaObjs + p->nGiaObjs );
  p->G = ABC_CALLOC( DdNode *, p->nGiaObjs + p->nGiaObjs );
  p->C = ABC_CALLOC( DdNode **, p->nGiaObjs + p->nGiaObjs );
  p->Csize = ABC_CALLOC( int, p->nGiaObjs + p->nGiaObjs );
  p->nMemMax = nMemMax;
  p->nBddSizeMax = 1 << nMemMax;
  p->filename = Filename;
  p->nOpt = nOpt;
  p->nVerbose = nVerbose;
  p->fDvr = fDvr;
  return p;
}
static inline void Abc_DdManAlloc( Abc_DdNandMan * p )
{
  int i;
  int id, idj;
  p->pDd = Cudd_Init( Vec_IntSize( p->pis ), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
  assert( p->pDd != NULL );
  if ( p->fDvr ) Cudd_AutodynEnable( p->pDd, CUDD_REORDER_SYMM_SIFT );
  id = 0;
  Abc_DdNandObjValueWrite( p, id, Cudd_Not( p->pDd->one ) );
  idj = Abc_DdNandCompl( p, id );
  Abc_DdNandObjValueWrite( p, idj, p->pDd->one );
  // pi
  Vec_IntForEachEntry( p->pis, id, i )
    Abc_DdNandObjValueWrite( p, id, p->pDd->vars[i] );
}
static inline void Abc_DdManFree( Abc_DdNandMan * p )
{
  ABC_FREE( p->newNodeValues );
  p->newNodeValues = ABC_CALLOC( DdNode *, p->nGiaObjs + p->nGiaObjs );
  ABC_FREE( p->G );
  for ( int i = 0; i < p->nGiaObjs + p->nGiaObjs; i++ )
    if ( p->C[i] != NULL )
      ABC_FREE( p->C[i] );
  ABC_FREE( p->C );
  p->G = ABC_CALLOC( DdNode *, p->nGiaObjs + p->nGiaObjs );
  p->C = ABC_CALLOC( DdNode **, p->nGiaObjs + p->nGiaObjs );
  ABC_FREE( p->Csize );
  p->Csize = ABC_CALLOC( int, p->nGiaObjs + p->nGiaObjs );    
  Cudd_Quit( p->pDd );
}
static inline void Abc_DdNandManFree( Abc_DdNandMan * p )
{
  Abc_DdManFree( p );
  Vec_IntFree( p->pis );
  Vec_IntFree( p->pos );
  for ( int i = 0; i < p->nGiaObjs + p->nGiaObjs; i++ )
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
  for ( int i = 0; i < p->nGiaObjs + p->nGiaObjs; i++ )
    if ( p->C[i] != NULL )
      ABC_FREE( p->C[i] );
  ABC_FREE( p->C );
  ABC_FREE( p->Csize );
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
	  else if ( idj == Abc_DdNandCompl( p, 0 ) )
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
      else if ( idj == Abc_DdNandCompl( p, 0 ) )
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
static inline void Abc_DdNandRank( Abc_DdNandMan * p, int id )
{
  if ( Abc_DdNandIsPiNode( p, id ) )
    p->rank[id] = 1 << 30; // assume this is max
  else
    {
      if ( Vec_IntSize( p->pis ) <= 20 )
	{
	  p->rank[id] = Vec_IntSize( p->fanoutList[id] ) << Vec_IntSize( p->pis );
	  p->rank[id] += Abc_DdNandCount0s( p, id, 0 );
	}
      else
	{
	  int nOverflow = Vec_IntSize( p->pis ) - 20;
	  p->rank[id] = Vec_IntSize( p->fanoutList[id] ) << 20;
	  p->rank[id] += Abc_DdNandCount0s( p, id, nOverflow );
	}
    }
  assert( p->rank[id] >= 0 );
}
static inline void Abc_DdNandRankAll( Abc_DdNandMan * p )
{
  int id;
  int i;
  Vec_IntForEachEntry( p->pis, id, i ) 
    Abc_DdNandRank( p, id );
  Vec_IntForEachEntry( p->livingNodes, id, i )
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
  int idj, idk;
  int j, k;
  Vec_IntForEachEntry( p->faninList[id], idj, j )
    {
      int best_j = j;
      int best_idj = idj;
      Vec_IntForEachEntryStart( p->faninList[id], idk, k, j+1 )
	if ( p->rank[idj] > p->rank[idk] )
	  {
	    best_j = k;
	    best_idj = idk;
	  }
      Vec_IntWriteEntry( p->faninList[id], j, best_idj );
      Vec_IntWriteEntry( p->faninList[id], best_j, idj );
    }
}
static inline void Abc_DdNandSortFaninAll( Abc_DdNandMan * p )
{
  int id;
  int i;
  Vec_IntForEachEntry( p->livingNodes, id, i )
    Abc_DdNandSortFanin( p, id );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_DdNandBuild( Abc_DdNandMan * p, int id )
{
  int idj;
  int j;
  if ( Abc_DdNandObjValue( p, id ) != NULL )
    Abc_DdDeref( p->pDd, Abc_DdNandObjValue( p, id ), "build before" );
  DdNode * Value_ = p->pDd->one;
  Abc_DdRef( Value_, "+build init" );
  Vec_IntForEachEntry( p->faninList[id], idj, j )
    {
      DdNode * Value = Abc_DdAnd( p->pDd, Value_, Abc_DdNandObjValue( p, idj ), p->nBddSizeMax );
      if ( Value == NULL )
	{
	  Abc_DdDeref( p->pDd, Value_, "build null" );
	  return 1;
	}
      Abc_DdRef( Value, "+build rec" );
      Abc_DdDeref( p->pDd, Value_, "build rec" );
      Value_ = Value;
    }
  Abc_DdNandObjValueWrite( p, id, Cudd_Not( Value_ ) );
  return 0;
}
static inline int Abc_DdNandBuildAll( Abc_DdNandMan * p )
{
  int id;
  int i;
  Vec_IntForEachEntry( p->livingNodes, id, i )
    if ( Abc_DdNandBuild( p, id ) ) return 1;
  return 0;
}
static inline int Abc_DdNandBuildFanoutCone( Abc_DdNandMan * p, int startId )
{
  int id;
  int i;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  Vec_IntPush( targets, startId );
  Abc_DdNandDescendantSortedList( p, p->fanoutList, targets, startId );
  Vec_IntForEachEntry( targets, id, i )
    if ( Abc_DdNandBuild( p, id ) )
      {
	Vec_IntFree( targets );
	return 1;
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
static inline int Abc_DdNandCspfG( Abc_DdNandMan * p, int id )
{
  int j;
  int idj;
  if ( p->G[id] != NULL )
    Abc_DdDeref( p->pDd, p->G[id], "cspfg before" );
  p->G[id] = p->pDd->one;
  Abc_DdRef( p->G[id], "+cspfg init" );
  Vec_IntForEachEntry( p->fanoutList[id], idj, j )
    {
      DdNode * Value = NULL;
      if ( Abc_DdNandIsPoNode( p, idj ) ) // G[idj] will be 0 unless po dont care is given.
	if ( p->G[idj] == NULL ) Value = Cudd_Not( p->pDd->one );
	else Value = Abc_DdAnd( p->pDd, p->G[id], p->G[idj], p->nBddSizeMax );
      else
	{
	  int index = Vec_IntFind( p->faninList[idj], id );
	  assert( index >= 0 );
	  //	  assert( Vec_IntSize( p->faninList[idj] ) == Vec_IntSize( p->C[idj] ) );
	  DdNode * c = p->C[idj][index];
	  Value = Abc_DdAnd( p->pDd, p->G[id], c, p->nBddSizeMax );
	}
      if ( Value == NULL )
	{
	  Abc_DdDeref( p->pDd, p->G[id], "cspfg null" );
	  return 1;
	}
      Abc_DdRef( Value, "+cspfg rec" );
      Abc_DdDeref( p->pDd, p->G[id], "cspfg rec" );
      p->G[id] = Value;
    }
  if ( p->G[id] == NULL ) return 1;
  return 0;
}
static inline int Abc_DdNandCspfC( Abc_DdNandMan * p, int id ) {
  int j, k;
  int idj, idk;
  if ( p->Csize[id] != 0 ) 
    for ( int i = 0; i < p->Csize[id]; i++ ) 
      if( p->C[id][i] != NULL )
	Abc_DdDeref( p->pDd, p->C[id][i], "cspfc before" );
  ABC_FREE( p->C[id] );
  p->Csize[id] = Vec_IntSize( p->faninList[id] );
  p->C[id] = ABC_CALLOC( DdNode *, p->Csize[id] );
  Vec_IntForEachEntry( p->faninList[id], idj, j )
    {
      DdNode * fanins = p->pDd->one;
      Abc_DdRef( fanins, "+cspfc init" );
      Vec_IntForEachEntryStart( p->faninList[id], idk, k, j+1 )
	{
	  DdNode * fk = Abc_DdNandObjValue( p, idk );
	  DdNode * Value = Abc_DdAnd( p->pDd, fanins, fk, p->nBddSizeMax );
	  if ( Value == NULL )
	    {
	      Abc_DdDeref( p->pDd, fanins, "cspfc null" );
	      return 1;
	    }
	  Abc_DdRef( Value, "+cspfc rec" );
	  Abc_DdDeref( p->pDd, fanins, "cspfc rec" );
	  fanins = Value;
	}
      DdNode * fi = Abc_DdNandObjValue( p, id );
      DdNode * fj = Abc_DdNandObjValue( p, idj );
      DdNode * already1 = Abc_DdAnd( p->pDd, fi, fj, p->nBddSizeMax );
      if ( already1 == NULL )
	{
	  Abc_DdDeref( p->pDd, fanins, "cspfc null2" );
	  return 1;
	}
      Abc_DdRef( already1, "+cspfc already1" );
      DdNode * c = Abc_DdOr( p->pDd, p->G[id], Cudd_Not( fanins ), p->nBddSizeMax );
      if ( c == NULL )
	{
	  Abc_DdDeref( p->pDd, fanins, "cspfc null3" );
	  Abc_DdDeref( p->pDd, already1, "cspfc null4" );
	  return 1;
	}
      Abc_DdRef( c, "+cspfc c" );
      Abc_DdDeref( p->pDd, fanins, "cspfs c done" );
      DdNode * Value = Abc_DdOr( p->pDd, c, already1, p->nBddSizeMax );
      if ( Value == NULL )
	{
	  Abc_DdDeref( p->pDd, already1, "cspfc null5" );
	  Abc_DdDeref( p->pDd, c, "cspfc null6" );
	  return 1;
	}
      Abc_DdRef( Value, "+cspfc value" );
      Abc_DdDeref( p->pDd, already1, "cspfc value done" );
      Abc_DdDeref( p->pDd, c, "cspfc value done2" );
      DdNode * DC1 = Abc_DdOr( p->pDd, fj, Value, p->nBddSizeMax );
      if ( DC1 == NULL )
	{
	  Abc_DdDeref( p->pDd, Value, "cspfc null7" );
	  return 1;
	}
      Abc_DdRef( DC1, "+cspfc DC1" );
      if ( DC1 == p->pDd->one )
	{
	  Abc_DdDeref( p->pDd, DC1, "cspfc found" );
	  Abc_DdNandDisconnect( p, idj, id );
	  if ( Vec_IntSize( p->faninList[id] ) == 0 )
	    {
	      Vec_IntForEachEntry( p->fanoutList[id], idk, k )
		Abc_DdNandConnect( p, 0, idk, 0 ); // duplication of const0 inputs may happen
	      Abc_DdNandRemoveNode( p, id );
	      return 0;
	    }
	  j--;
	  continue;
	}
      Abc_DdDeref( p->pDd, DC1, "cspfc end" );
      p->C[id][j] = Value;
    }
  return 0;
}
static inline int Abc_DdNandCspf( Abc_DdNandMan * p )
{
  int id;
  int i;
  Vec_IntForEachEntryReverse( p->livingNodes, id, i )
    {
      if ( Vec_IntSize( p->fanoutList[id] ) == 0 )
	{ // remove the node
	  Abc_DdNandRemoveNode( p, id );
	  continue;
	}
      if ( Abc_DdNandCspfG( p, id ) ) return 1;
      if ( Abc_DdNandCspfC( p, id ) ) return 1;
    }
  return Abc_DdNandBuildAll( p );
}
static inline int Abc_DdNandCspfFaninCone( Abc_DdNandMan * p, int startId )
{
  int id;
  int i;
  Vec_Int_t * targets = Vec_IntAlloc( 1 );
  Abc_DdNandDescendantSortedList( p, p->faninList, targets, startId );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Vec_IntSize( p->fanoutList[id] ) == 0 )
	{ // remove the node
	  Abc_DdNandRemoveNode( p, id );
	  continue;
	}
      if ( Abc_DdNandCspfG( p, id ) ) return 1;
      if ( Abc_DdNandCspfC( p, id ) ) return 1;
    }
  Vec_IntFree( targets );
  return Abc_DdNandBuildAll( p );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Abc_DdNandRefresh( Abc_DdNandMan * p )
{
  if ( p->nVerbose >= 2 ) printf( "\nrefreshing");
  Abc_DdManFree( p );
  Abc_DdManAlloc( p );
  abctime clk0 = Abc_Clock();
  int out = Abc_DdNandBuildAll( p );
  out += Abc_DdNandCspf( p );
  if ( out )
    {
      printf( "\rexceeded even after refresh\n" );
      Abc_DdNandPrintNet( p );      
      assert(0);
    }
  if ( p->nVerbose >= 2 ) ABC_PRT( "\rrefresh took", Abc_Clock() - clk0 );
}
static inline void Abc_DdNandRefreshIfNeeded( Abc_DdNandMan * p )
{
  if ( Cudd_ReadKeys( p->pDd ) - Cudd_ReadDead( p->pDd ) > p->nBddSizeMax )
    Abc_DdNandRefresh( p );
}
static inline void Abc_DdNandBuildRefresh( Abc_DdNandMan * p, int id ) { if ( Abc_DdNandBuild( p, id ) ) Abc_DdNandRefresh( p ); }
static inline void Abc_DdNandBuildAllRefresh( Abc_DdNandMan * p ) { if ( Abc_DdNandBuildAll( p ) ) Abc_DdNandRefresh( p ); }
static inline void Abc_DdNandBuildFanoutConeRefresh( Abc_DdNandMan * p, int startId ) { if ( Abc_DdNandBuildFanoutCone( p, startId ) ) Abc_DdNandRefresh( p ); }
static inline void Abc_DdNandCspfCRefresh( Abc_DdNandMan * p, int id ) { if ( Abc_DdNandCspfC( p, id ) ) Abc_DdNandRefresh( p ); }
static inline void Abc_DdNandCspfRefresh( Abc_DdNandMan * p ) { if ( Abc_DdNandCspf( p ) ) Abc_DdNandRefresh( p ); }
static inline void Abc_DdNandCspfFaninConeRefresh( Abc_DdNandMan * p, int startId ) { if ( Abc_DdNandCspfFaninCone( p, startId ) ) Abc_DdNandRefresh( p ); }

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
      Abc_DdNandCspfRefresh( p );
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
  if ( Vec_IntFind( p->faninList[fanout], fanin ) != -1 ) return 0; // already connected
  DdNode * ffanin = Abc_DdNandObjValue( p, fanin );
  DdNode * ffanout = Abc_DdNandObjValue( p, fanout );
  DdNode * gfanout = p->G[fanout];
  DdNode * connectable = Abc_DdOr( p->pDd, ffanout, gfanout, p->nBddSizeMax );
  if( connectable == NULL ) return -1;
  Abc_DdRef( connectable, "+connect connectable" );
  DdNode * Value = Abc_DdOr( p->pDd, ffanin, connectable, p->nBddSizeMax );
  if( Value == NULL )
    {
      Abc_DdDeref( p->pDd, connectable, "connect null" );
      return -1;
    }
  Abc_DdRef( Value, "+connect value" );
  Abc_DdDeref( p->pDd, connectable, "connect value done" );
  connectable = Value;
  if ( connectable == p->pDd->one )
    {
      Abc_DdNandConnect( p, fanin, fanout, 1 );
      return 1;
    }
  return 0;
}
static inline int Abc_DdNandTryConnectRefreshing( Abc_DdNandMan * p, int fanin, int fanout )
{
  int c = Abc_DdNandTryConnect( p, fanin, fanout );
  if ( c == -1 )
    {
      Abc_DdNandRefresh( p );
      if ( Abc_DdNandIsEmptyOrDeadNode( p, fanin ) ) return 0;
      if ( Abc_DdNandIsEmptyOrDeadNode( p, fanout ) ) return 0;
      c = Abc_DdNandTryConnect( p, fanin, fanout );
    }
  return c;
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
  Abc_DdNandCspfCRefresh( p, id );
  if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) return;
  Abc_DdNandCspfFaninConeRefresh( p, id );
  if ( wire == Abc_DdNandCountWire( p ) )
    {
      Abc_DdNandDisconnect( p, idj, id );
      Abc_DdNandBuildFanoutConeRefresh( p, id );
      if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) return;
      Abc_DdNandCspfCRefresh( p, id );
      if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) return;
      Abc_DdNandCspfFaninConeRefresh( p, id );
    }
  else
    {
      Abc_DdNandBuildAllRefresh( p );
      Abc_DdNandCspfEager( p );
    }
}
static inline void Abc_DdNandG1WeakReduce( Abc_DdNandMan * p, int id, int idj )
{
  int wire =  Abc_DdNandCountWire( p );
  Abc_DdNandCspfCRefresh( p, id );
  if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) return;
  if ( Abc_DdNandIsEmptyOrDeadNode( p, idj ) ) return;
  if ( wire == Abc_DdNandCountWire( p ) )
    Abc_DdNandDisconnect( p, idj, id );
  Abc_DdNandBuildRefresh( p, id );
}
static inline void Abc_DdNandG1( Abc_DdNandMan * p )
{
  int i, j;
  int id, idj;
  Vec_Int_t * targets = Vec_IntDup( p->livingNodes );
  Vec_IntForEachEntryReverse( targets, id, i )
    {
      if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) continue;
      if ( p->nVerbose >= 2 )
	{
	  printf( "\rG1 for %d in %d gates", i, Vec_IntSize(targets) );
	  fflush( stdout );
	}
      Vec_Int_t * fanouts = Vec_IntAlloc( 1 );
      Abc_DdNandDescendantList_rec( p->fanoutList, fanouts, id );
      // try connecting candidate
      Vec_IntForEachEntry( targets, idj, j )
	{
	  if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) break;
	  if ( Abc_DdNandIsEmptyOrDeadNode( p, idj ) ) continue;
	  if ( id == idj ) continue;
	  if ( Vec_IntFind( fanouts, idj ) != -1 ) continue;
	  if ( Abc_DdNandTryConnectRefreshing( p, idj, id ) == 1 )
	    {
	      if ( p->nOpt ) Abc_DdNandG1WeakReduce( p, id, idj );
	      else Abc_DdNandG1EagerReduce( p, id, idj );
	    }
	}
      // try connecting pi
      Vec_IntForEachEntry( p->pis, idj, j )
	{
	  if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) break;
	  if ( Abc_DdNandTryConnectRefreshing( p, idj, id ) == 1 )
	    {
	      if ( p->nOpt ) Abc_DdNandG1WeakReduce( p, id, idj );	
	      else Abc_DdNandG1EagerReduce( p, id, idj );
	    }
	}
      // recalculate fanouts for option
      if ( p->nOpt )
	{
	  if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) continue;
	  Abc_DdNandCspfCRefresh( p, id );
	  if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) continue;
	  Abc_DdNandCspfFaninConeRefresh( p, id );
	  if ( Abc_DdNandIsEmptyOrDeadNode( p, id ) ) continue;
	  Abc_DdNandBuildAllRefresh( p );
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
  printf( "\r%-10s: gates = %5d, wires = %5d, AIG node = %5d", prefix, Vec_IntSize( p->livingNodes ), Abc_DdNandCountWire( p ), Abc_DdNandCountWire( p ) - Vec_IntSize( p->livingNodes ) );
  ABC_PRT( ", time ", Abc_Clock() - clk0 );
}
void Abc_DdNandGiaTest( Gia_Man_t * pGia, char * Filename, int nMem, int nMemMax, int nType, int nIte, int nOpt, int fDvr, int nVerbose )
{
  Abc_DdNandMan * p = Abc_DdNandManAlloc( pGia, Filename, nMem, nMemMax, nOpt, fDvr, nVerbose );
  Abc_DdNandGenNet( p, pGia );
  Abc_DdManAlloc( p );
  abctime clk0 = Abc_Clock();
  if ( Abc_DdNandBuildAll( p ) )
    {
      Abc_DdNandManFree( p );
      printf("The number of nodes exceeds the limit before cspf.\n");
      return;
    }
  if ( nVerbose ) Abc_DdNandPrintStats( p, "initial", clk0 );
  Abc_DdNandCspfEager( p );
  if ( nVerbose ) Abc_DdNandPrintStats( p, "cspf", clk0 );
  int wire = 0;
  int t = 0;
  while ( wire != Abc_DdNandCountWire( p ) )
    {
      wire = Abc_DdNandCountWire( p );
      switch ( nType )
	{
	case 1:
	  Abc_DdNandG1( p );
	  if ( nVerbose ) Abc_DdNandPrintStats( p, "g1", clk0 );
	  break;
	case 2:
	  printf( "g2 is not availabe now\n" );
	  break;
	case 3:
	  printf( "g3 is not availabe now\n" );
	  break;
	case 4:
	  printf( "g4 is not availabe now\n" );
	  break;
	case 5:
	  printf( "g5 is not availabe now\n" );
	  break;
	default:
	  break;
	}
      Abc_DdNandCspfEager( p );
      t++;
      if ( t == nIte ) break;
    }    
  if ( nVerbose ) ABC_PRT( "total ", Abc_Clock() - clk0 );
  Abc_DdNandPrintNet( p );
  Abc_DdNandManFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
