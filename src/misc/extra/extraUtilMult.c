/**CFile****************************************************************

   FileName    [extraUtilMult.c]

   SystemName  [ABC: Logic synthesis and verification system.]

   PackageName [extra]

   Synopsis    [Simple BDD package.]

   Author      [Alan Mishchenko]
  
   Affiliation [UC Berkeley]

   Date        [Ver. 1.0. Started - May 23, 2018.]

   Revision    [$Id: extraUtilMult.c,v 1.0 2018/05/23 00:00:00 alanmi Exp $]

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

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************
   
   Synopsis    [Creating new node.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline unsigned Abc_BddUniqueCreateInt( Abc_BddMan * p, int Var, unsigned Then, unsigned Else )
{
  int * q = p->pUnique + ( Abc_BddHash( Var, Then, Else ) & p->nUniqueMask );
  for ( ; *q; q = p->pNexts + *q )
    if ( Abc_BddVarOfBvar( p, *q ) == Var &&
	 Abc_BddThenOfBvar( p, *q ) == Then &&
	 Abc_BddElseOfBvar( p, *q ) == Else )
      return Abc_BddBvar2Lit( *q, 0 );
  q = p->pUnique + ( Abc_BddHash( Var, Then, Else ) & p->nUniqueMask );
  int headBvar = *q;
  if ( Abc_BddIsLimit( p ) )
    {
      for ( ; p->nMinRemoved < p->nObjs; p->nMinRemoved++ )
	if ( Abc_BddBvarIsRemoved( p, p->nMinRemoved ) ) break;
      if ( p->nMinRemoved == p->nObjs ) return Abc_BddLitInvalid();
      *q = p->nMinRemoved++;
      p->nRemoved--;
    }
  else *q = p->nObjs++;
  Abc_BddSetVarOfBvar( p, *q, Var );
  Abc_BddSetThenOfBvar( p, *q, Then );
  Abc_BddSetElseOfBvar( p, *q, Else );
  Abc_BddSetNextOfBvar( p, *q, headBvar );
  if ( p->nVerbose > 2 )
    printf( "\rAdded node %10d: Var = %3d  Then = %10u  Else = %10u  Removed = %10u", *q, Var, Then, Else, p->nRemoved );
  return Abc_BddBvar2Lit( *q, 0 );
}
unsigned Abc_BddUniqueCreate( Abc_BddMan * p, int Var, unsigned Then, unsigned Else )
{
  if ( Var < 0 || Var >= p->nVars )   return Abc_BddLitInvalid();
  if ( Var >= Abc_BddVar( p, Then ) ) return Abc_BddLitInvalid();
  if ( Var >= Abc_BddVar( p, Else ) ) return Abc_BddLitInvalid();
  if ( Abc_BddLitIsEq( Then, Else ) ) return Else;
  if ( !Abc_BddLitIsCompl( Else ) ) return Abc_BddUniqueCreateInt( p, Var, Then, Else );
  unsigned r = Abc_BddUniqueCreateInt( p, Var, Abc_BddLitNot( Then ), Abc_BddLitNot( Else ) );
  return Abc_BddLitIsInvalid( r ) ? Abc_BddLitInvalid() : Abc_BddLitNot( r );
}

/**Function*************************************************************

   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline unsigned Abc_BddCacheLookup( Abc_BddMan * p, unsigned Arg1, unsigned Arg2 )
{
  unsigned * pEnt = p->pCache + 3*(long long)( Abc_BddHash( 0, Arg1, Arg2 ) & p->nCacheMask );
  p->nCacheLookups++;
  return ( pEnt[0] == Arg1 && pEnt[1] == Arg2 ) ? pEnt[2] : Abc_BddLitInvalid();
}
static inline unsigned Abc_BddCacheInsert( Abc_BddMan * p, unsigned Arg1, unsigned Arg2, unsigned Res )
{
  unsigned * pEnt = p->pCache + 3*(long long)( Abc_BddHash( 0, Arg1, Arg2 ) & p->nCacheMask );
  pEnt[0] = Arg1; pEnt[1] = Arg2; pEnt[2] = Res;
  p->nCacheMisses++;
  return Res;
}
static inline void Abc_BddCacheRemove( Abc_BddMan * p ) {
  ABC_FREE( p->pCache );
  p->pCache = ABC_CALLOC( unsigned, 3 * (long long)( p->nCacheMask + 1 ) );
  if ( p->nVerbose > 2 )
    printf( "\t\tCache: Hit = %u  Miss = %u\n", p->nCacheLookups - p->nCacheMisses, p->nCacheMisses );
}

/**Function*************************************************************

   Synopsis    [Count fanout of gates.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline void Abc_BddGiaCountFanout( Gia_Man_t * pGia, int * pFanouts )
{
  Gia_Obj_t * pObj; int i;
  Gia_ManStaticFanoutStart( pGia );
  Gia_ManForEachAnd( pGia, pObj, i )
    pFanouts[Gia_ObjId( pGia, pObj )] = Gia_ObjFanoutNum( pGia, pObj );
  Gia_ManStaticFanoutStop( pGia );
}

/**Function*************************************************************
 
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
Abc_BddMan * Abc_BddManAlloc( int nVars, unsigned nObjs, int nVerbose )
{
  if ( nVerbose ) printf( "Allocate nodes by 2^%d\n", Abc_Base2Log( nObjs ) );
  Abc_BddMan * p; int i;
  p = ABC_CALLOC( Abc_BddMan, 1 );
  p->nVars       = nVars;
  assert( nVars <= (int)Abc_BddVarConst() );
  p->nObjsAlloc  = nObjs;
  p->nUniqueMask = ( 1 << Abc_Base2Log( nObjs ) ) - 1;
  p->nCacheMask  = ( 1 << Abc_Base2Log( nObjs ) ) - 1;
  p->nMinRemoved = nObjs - 1;
  p->nRemoved    = 0;
  p->nVerbose    = nVerbose;
  p->pUnique     = ABC_CALLOC( int, p->nUniqueMask + 1 );
  p->pNexts      = ABC_CALLOC( int, p->nUniqueMask + 1 );
  p->pCache      = ABC_CALLOC( unsigned, 3 * (long long)( p->nCacheMask + 1 ) );
  p->pObjs       = ABC_CALLOC( unsigned, 2 * (long long)p->nObjsAlloc );
  p->pMark       = ABC_CALLOC( unsigned char, p->nObjsAlloc );
  p->pVars       = ABC_CALLOC( unsigned char, p->nObjsAlloc );
  assert( p->pUnique );
  assert( p->pNexts );
  assert( p->pCache );
  assert( p->pObjs );
  assert( p->pMark );
  assert( p->pVars );
  p->pVars[0]    = Abc_BddVarConst();
  p->nObjs       = 1;
  for ( i = 0; i < nVars; i++ ) Abc_BddUniqueCreate( p, i, 1, 0 );
  assert( p->nObjs == nVars + 1 );
  p->nMemory = sizeof(Abc_BddMan) + 
    ( p->nUniqueMask + 1 ) * sizeof(int) + 
    (long long)( p->nCacheMask + 1 ) * 3 * sizeof(int) + 
    (long long)p->nObjsAlloc * 2 * sizeof(int) +
    (long long)p->nObjsAlloc * 3 * sizeof(char);
  p->fRealloc = 0;
  p->fGC = 0;
  p->ReorderThreshold = 0;
  p->pFanouts = NULL;
  p->pFrontiers = NULL;
  p->pEdges = NULL;
  p->liveBvars = NULL;
  return p;
}
void Abc_BddRefreshConfig( Abc_BddMan * p, Gia_Man_t * pGia, int fRealloc, int fGC, int nReorderThreshold )
{
  p->fRealloc = fRealloc;
  p->fGC = fGC;
  p->ReorderThreshold = 0.01 * nReorderThreshold;
  if ( fGC || p->ReorderThreshold != 0 )
    {
      p->pFanouts = ABC_CALLOC( int, pGia->nObjs );
      assert( p->pFanouts );
      p->pFrontiers = Vec_IntAlloc( 1 );
      Abc_BddGiaCountFanout( pGia, p->pFanouts );
    }
  if ( p->ReorderThreshold != 0 )
    {
      p->pEdges = ABC_CALLOC( unsigned, p->nObjsAlloc );
      assert( p->pEdges );
      int i;
      p->liveBvars = ABC_ALLOC( Vec_Int_t *, p->nVars + 2);
      for ( i = 0; i < p->nVars + 2; i++ )
	p->liveBvars[i] = Vec_IntAlloc( p->nObjsAlloc / p->nVars );
    }
}
void Abc_BddManFree( Abc_BddMan * p )
{
  if ( p->nVerbose > 2 )
    {
      printf( "BDD stats: Var = %u  Obj = %u  Alloc = %u  Hit = %u  Miss = %u  ", p->nVars, p->nObjs, p->nObjsAlloc - 1, p->nCacheLookups - p->nCacheMisses, p->nCacheMisses );
      printf( "Mem = %.2lld MB\n", (long long)( p->nMemory / ( 1 << 20 ) ) );
    }
  ABC_FREE( p->pUnique );
  ABC_FREE( p->pNexts );
  ABC_FREE( p->pCache );
  ABC_FREE( p->pObjs );
  ABC_FREE( p->pVars );
  if ( p->pFanouts != NULL )
    ABC_FREE( p->pFanouts );
  if ( p->pFrontiers != NULL) 
    Vec_IntFree( p->pFrontiers );
  if ( p->pEdges != NULL)
    ABC_FREE( p->pEdges );
  if ( p->liveBvars != NULL)
    {
      int i;
      for ( i = 0; i < p->nVars + 2; i++ )
	Vec_IntFree( p->liveBvars[i] );
      ABC_FREE( p->liveBvars );
    }
  ABC_FREE( p );
}
static inline void Abc_BddRehash( Abc_BddMan * p )
{
  unsigned i, hash;
  int * q, * tail, * tail1, * tail2;
  unsigned nObjsAllocOld = p->nObjsAlloc >> 1; // assuming nObjsAlloc has been doubled.
  for ( i = 0; i < nObjsAllocOld; i++ )
    {
      q = p->pUnique + i;
      tail1 = q;
      tail2 = q + nObjsAllocOld;
      while ( *q )
	{
	  hash = Abc_BddHash( Abc_BddVarOfBvar( p, *q ), Abc_BddThenOfBvar( p, *q ), Abc_BddElseOfBvar( p, *q ) ) & p->nUniqueMask;
	  assert( hash == i || hash == i + nObjsAllocOld );
	  if ( hash == i ) tail = tail1;
	  else tail = tail2;
	  if ( tail != q )
	    {
	      *tail = *q;
	      *q = 0;
	    }
	  q = p->pNexts + *tail;
	  if ( tail == tail1 ) tail1 = q;
	  else tail2 = q;
	}
    }
}
int Abc_BddManRealloc( Abc_BddMan * p )
{
  unsigned nObjsAllocOld = p->nObjsAlloc;
  p->nObjsAlloc  = p->nObjsAlloc + p->nObjsAlloc;
  assert( p->nObjsAlloc != 0 );
  if ( p->nVerbose ) printf( "\tReallocate nodes by 2^%d\n", Abc_Base2Log( p->nObjsAlloc ) );
  int nUniqueMaskOld = p->nUniqueMask;
  p->nUniqueMask = ( 1 << Abc_Base2Log( p->nObjsAlloc ) ) - 1;
  p->nCacheMask  = ( 1 << Abc_Base2Log( p->nObjsAlloc ) ) - 1;
  p->pUnique     = ABC_REALLOC( int, p->pUnique, p->nUniqueMask + 1 );
  p->pNexts      = ABC_REALLOC( int, p->pNexts, p->nUniqueMask + 1 );
  p->pObjs       = ABC_REALLOC( unsigned, p->pObjs, 2 * (long long)p->nObjsAlloc );
  p->pMark       = ABC_REALLOC( unsigned char, p->pMark, p->nObjsAlloc );
  p->pVars       = ABC_REALLOC( unsigned char, p->pVars, p->nObjsAlloc );
  if ( !p->pUnique ) return -1;
  if ( !p->pNexts  ) return -1;
  if ( !p->pObjs   ) return -1;
  if ( !p->pMark   ) return -1;
  if ( !p->pVars   ) return -1;
  memset( p->pUnique + ( nUniqueMaskOld + 1 ), 0, sizeof(int) * ( nUniqueMaskOld + 1 ) );
  memset( p->pNexts + ( nUniqueMaskOld + 1 ), 0, sizeof(int) * ( nUniqueMaskOld + 1 ) );
  memset( p->pObjs + 2 * (long long)nObjsAllocOld, 0, sizeof(unsigned) * 2 * (long long)nObjsAllocOld );
  memset( p->pMark + nObjsAllocOld, 0, sizeof(unsigned char) * nObjsAllocOld );
  memset( p->pVars + nObjsAllocOld, 0, sizeof(unsigned char) * nObjsAllocOld );
  Abc_BddCacheRemove( p );
  p->nMemory = sizeof(Abc_BddMan) + 
    ( p->nUniqueMask + 1 ) * sizeof(int) + 
    (long long)( p->nCacheMask + 1 ) * 3 * sizeof(int) + 
    (long long)p->nObjsAlloc * 2 * sizeof(int) +
    (long long)p->nObjsAlloc * 3 * sizeof(char);
  Abc_BddRehash( p );
  if ( p->pEdges != NULL )
    {
      p->pEdges      = ABC_REALLOC( unsigned, p->pEdges, p->nObjsAlloc );
      if ( !p->pEdges ) return -1;
      memset ( p->pEdges + nObjsAllocOld, 0, sizeof(unsigned) * nObjsAllocOld );
    }
  return 0;
}

/**Function*************************************************************
   
   Synopsis    [Boolean AND.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
unsigned Abc_BddAnd( Abc_BddMan * p, unsigned a, unsigned b )
{
  if ( Abc_BddLitIsInvalid( a ) || Abc_BddLitIsInvalid( b ) ) return Abc_BddLitInvalid();
  if ( Abc_BddLitIsConst0( a ) ) return a;
  if ( Abc_BddLitIsConst0( b ) ) return b;
  if ( Abc_BddLitIsConst1( a ) ) return b;
  if ( Abc_BddLitIsConst1( b ) ) return a;
  if ( Abc_BddLitIsEq( a, b ) ) return a;
  if ( a > b )  return Abc_BddAnd( p, b, a );
  unsigned r0, r1, r;
  unsigned s0, s1, t0, t1;
  r = Abc_BddCacheLookup( p, a, b );
  if ( !Abc_BddLitIsInvalid( r ) ) return r;
  if ( Abc_BddVar( p, a ) < Abc_BddVar( p, b ) )
    s0 = Abc_BddElse( p, a ), t0 = b, s1 = Abc_BddThen( p, a ), t1 = b;
  else if ( Abc_BddVar( p, a ) > Abc_BddVar( p, b ) )
    s0 = a, t0 = Abc_BddElse( p, b ), s1 = a, t1 = Abc_BddThen( p, b );
  else // if ( Abc_BddVar( p, a ) == Abc_BddVar( p, b ) )
    s0 = Abc_BddElse( p, a ), t0 = Abc_BddElse( p, b ), s1 = Abc_BddThen( p, a ), t1 = Abc_BddThen( p, b );
  r0 = Abc_BddAnd( p, s0, t0 );
  if ( Abc_BddLitIsInvalid( r0 ) ) return Abc_BddLitInvalid();
  r1 = Abc_BddAnd( p, s1, t1 );
  if ( Abc_BddLitIsInvalid( r1 ) ) return Abc_BddLitInvalid();
  r = Abc_BddUniqueCreate( p, Abc_MinInt( Abc_BddVar( p, a ), Abc_BddVar( p, b ) ), r1, r0 );
  if ( Abc_BddLitIsInvalid( r ) ) return Abc_BddLitInvalid();
  return Abc_BddCacheInsert( p, a, b, r );
}
unsigned Abc_BddOr( Abc_BddMan * p, unsigned a, unsigned b )
{
  unsigned r = Abc_BddAnd( p, Abc_BddLitNot( a ), Abc_BddLitNot( b ) );
  return Abc_BddLitIsInvalid( r ) ? Abc_BddLitInvalid() : Abc_BddLitNot( r );
}

/**Function*************************************************************
   
   Synopsis    [Counting nodes.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
int Abc_BddCount_rec( Abc_BddMan * p, unsigned i )
{
  if ( Abc_BddLitIsConst( i ) ) return 0;
  if ( Abc_BddMark( p, i ) ) return 0;
  Abc_BddSetMark( p, i, 1 );
  return 1 + Abc_BddCount_rec( p, Abc_BddElse( p, i ) ) + Abc_BddCount_rec( p, Abc_BddThen( p, i ) );
}
void Abc_BddMark_rec( Abc_BddMan * p, unsigned i )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  if ( Abc_BddMark( p, i ) ) return;
  Abc_BddSetMark( p, i, 1 );
  Abc_BddMark_rec( p, Abc_BddElse( p, i ) );
  Abc_BddMark_rec( p, Abc_BddThen( p, i ) );
}
void Abc_BddUnmark_rec( Abc_BddMan * p, unsigned i )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  if ( !Abc_BddMark( p, i ) ) return;
  Abc_BddSetMark( p, i, 0 );
  Abc_BddUnmark_rec( p, Abc_BddElse( p, i ) );
  Abc_BddUnmark_rec( p, Abc_BddThen( p, i ) );
}
static inline int Abc_BddCountNodes( Abc_BddMan * p, unsigned i )
{
  int Count = Abc_BddCount_rec( p, i );
  Abc_BddUnmark_rec( p, i );
  return Count;
}
int Abc_BddCountNodesArrayShared( Abc_BddMan * p, Vec_Int_t * vNodes )
{
  int i, a, Count = 0;
  Vec_IntForEachEntry( vNodes, a, i )
    Count += Abc_BddCount_rec( p, (unsigned)a );
  for ( i = 0; i < p->nVars; i++ )
    Count += Abc_BddCount_rec( p, Abc_BddLitIthVar( i ) );
  Vec_IntForEachEntry( vNodes, a, i )
    Abc_BddUnmark_rec( p, (unsigned)a );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddUnmark_rec( p, Abc_BddLitIthVar( i ) );
  //  return Count;
  return Count + 4; // add 4 to make the number comparable to command "collapse -v"
}
int Abc_BddCountNodesArrayIndependent( Abc_BddMan * p, Vec_Int_t * vNodes )
{
  int i, a, Count = 0;
  Vec_IntForEachEntry( vNodes, a, i )
    {
      // exclude variables to make the number comparable to command "print_stats" after "collapse"
      if ( Abc_BddLitRegular( a ) <= Abc_BddLitIthVar( p->nVars - 1 ) )
	continue; 
      Count += Abc_BddCount_rec( p, (unsigned)a );
      Abc_BddUnmark_rec( p, (unsigned)a );
    }
  return Count;
}

/**Function*************************************************************

   Synopsis    [Printing BDD.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddPrint_rec( Abc_BddMan * p, unsigned a, int * pPath, int offset, FILE * f )
{
  if ( Abc_BddLitIsConst0( a ) ) return;
  if ( Abc_BddLitIsConst1( a ) )
    { 
      int i;
      for ( i = 0; i < p->nVars; i++ )
	if ( pPath[i] == 0 || pPath[i] == 1 )
	  fprintf( f, "%c%d", pPath[i] ? '+' : '-', i - offset );
      fprintf( f, "\n" );
      return; 
    }
  pPath[Abc_BddVar( p, a )] =  0;
  Abc_BddPrint_rec( p, Abc_BddElse( p, a ), pPath, offset, f );
  pPath[Abc_BddVar( p, a )] =  1;
  Abc_BddPrint_rec( p, Abc_BddThen( p, a ), pPath, offset, f );
  pPath[Abc_BddVar( p, a )] = -1;
}
void Abc_BddPrint( Abc_BddMan * p, unsigned a, int offset, FILE * f )
{
  int * pPath = ABC_FALLOC( int, p->nVars );
  fprintf( f, "BDD %u =\n", a );
  Abc_BddPrint_rec( p, a, pPath, offset, f );
  ABC_FREE( pPath );
}

/**Function*************************************************************

   Synopsis    [Printing BDD.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddWriteBlif_rec( Abc_BddMan * p, int x, FILE * f )
{
  unsigned i = Abc_BddBvar2Lit( x, 0 );
  if ( Abc_BddLitIsConst( i ) ) return;
  if ( Abc_BddMark( p, i ) ) return;
  Abc_BddSetMark( p, i, 1 );
  Abc_BddWriteBlif_rec( p, Abc_BddLit2Bvar( Abc_BddElse( p, i ) ), f );
  Abc_BddWriteBlif_rec( p, Abc_BddLit2Bvar( Abc_BddThen( p, i ) ), f );
  fprintf( f, ".subckt mux" );
  fprintf( f, " sel=v%d", Abc_BddVar( p, i ) );
  fprintf( f, " in1=n%d", Abc_BddLit2Bvar( Abc_BddThen( p, i ) ) );
  fprintf( f, " else=n%d", Abc_BddLit2Bvar( Abc_BddElse( p, i ) ) );
  if ( Abc_BddLitIsCompl( Abc_BddThen( p, i ) ) ) fprintf( f, " comp1=one" );
  else fprintf( f, " comp1=zero" );
  fprintf( f, " out=n%d\n", x );  
}
void Abc_BddWriteBlif( Abc_BddMan * p, Vec_Int_t * vNodes, char * pFileName )
{
  int i, j;
  unsigned x;
  FILE * f = fopen( pFileName, "w" );
  fprintf( f, ".model top\n" );
  fprintf( f, ".inputs" );
  for ( i = 0; i < p->nVars; i++ )
    {
      for ( j = 0; j < p->nVars; j++ )
	if ( Abc_BddVar( p, Abc_BddLitIthVar( j ) ) == i ) break;
      if ( p->nVars <= 10 ) fprintf( f, " pi%d", j );
      else if ( p->nVars <= 100 ) fprintf( f, " pi%02d", j );
      else fprintf( f, " pi%03d", j );
    }
  printf( "\n" );
  /*
  for ( i = 0; i < p->nVars; i++ )
    if ( p->nVars <= 10 ) fprintf( f, " pi%d ", i );
    else if ( p->nVars <= 100 ) fprintf( f, " pi%02d ", i );
    else fprintf( f, " pi%03d ", i );
  */
  fprintf( f, "\n.outputs" );
  for ( i = 0; i < Vec_IntSize( vNodes ); i++ )
    if ( p->nVars <= 10 ) fprintf( f, " po%d ", i );
    else if ( p->nVars <= 100 ) fprintf( f, " po%02d ", i );
    else fprintf( f, " po%03d ", i );
  fprintf( f, "\n" );
  fprintf( f, ".names zero\n" );
  fprintf( f, ".names n0\n" );
  fprintf( f, ".names one\n1\n" );
  for ( i = 0; i < p->nVars; i++ )
    {
      fprintf( f, ".names" );
      if ( p->nVars <= 10 ) fprintf( f, " pi%d ", i );
      else if ( p->nVars <= 100 ) fprintf( f, " pi%02d ", i );
      else fprintf( f, " pi%03d ", i );
      fprintf( f, " v%d", Abc_BddVar( p, Abc_BddLitIthVar( i ) ) );
      fprintf( f, "\n1 1\n" );      
    }
  Vec_IntForEachEntry( vNodes, x, i )
    {
      fprintf( f, ".names" );
      fprintf( f, " n%d", Abc_BddLit2Bvar( x ) );
      if ( p->nVars <= 10 ) fprintf( f, " po%d ", i );
      else if ( p->nVars <= 100 ) fprintf( f, " po%02d ", i );
      else fprintf( f, " po%03d ", i );
      if ( Abc_BddLitIsCompl( x ) ) fprintf( f, "\n0 1\n" );
      else fprintf( f, "\n1 1\n" );      
      Abc_BddWriteBlif_rec( p, Abc_BddLit2Bvar( x ), f );
    }
  Vec_IntForEachEntry( vNodes, x, i )
      Abc_BddUnmark_rec( p, x );
    fprintf( f, ".end\n" );
  fprintf( f, ".model mux\n" );
  fprintf( f, ".inputs sel in1 else comp1\n" );
  fprintf( f, ".outputs out\n" );
  fprintf( f, ".names in1 comp1 then\n01 1\n10 1\n" );
  fprintf( f, ".names sel then else out\n" );
  fprintf( f, "0-1 1\n11- 1\n" );
  fprintf( f, ".end\n" );
  fclose( f );
}

/**Function*************************************************************

   Synopsis    [Remove unnecessary BDD nodes.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddRemoveNodeByBvar( Abc_BddMan * p, int i )
{
  int * q = p->pUnique + ( Abc_BddHash( Abc_BddVarOfBvar( p, i ), Abc_BddThenOfBvar( p, i ), Abc_BddElseOfBvar( p, i ) ) & p->nUniqueMask );
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == i ) break;
  int * q_next = p->pNexts + *q;
  *q = *q_next;
  *q_next = 0;
  Abc_BddSetBvarRemoved( p, i );
  if ( p->nMinRemoved > i ) p->nMinRemoved = i;
  p->nRemoved++;
}
void Abc_BddGarbageCollect( Abc_BddMan * p, Vec_Int_t * pFrontiers )
{
  if ( p->nVerbose ) printf("\tGarbage collect\n");
  int i;
  unsigned x;
  Vec_IntForEachEntry( pFrontiers, x, i )
    Abc_BddMark_rec( p, x );
  for ( i = p->nVars + 1; i < p->nObjs; i++ )
    if ( !Abc_BddMarkOfBvar( p, i ) && !Abc_BddBvarIsRemoved( p, i ) )
      Abc_BddRemoveNodeByBvar( p, i );
  Vec_IntForEachEntry( pFrontiers, x, i )
    Abc_BddUnmark_rec( p, x );
  Abc_BddCacheRemove( p );
}

/**Function*************************************************************

   Synopsis    [Refresh]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline int Abc_BddRefresh( Abc_BddMan * p, int * nRefresh )
{
  *nRefresh += 1;
  if ( p->nVerbose > 1 ) printf( "\n" );
  if ( p->nVerbose ) printf( "Refresh %d\n", *nRefresh );
  if ( p->fGC ) Abc_BddGarbageCollect( p, p->pFrontiers );
  if ( *nRefresh <= 1 ) return 0;
  if ( p->ReorderThreshold != 0 && p->nObjsAlloc > 4000 && *nRefresh <= 2 )
    {
      if ( p->nVerbose ) printf("\tReordering\n");
      if ( Abc_BddReorder( p, p->pFrontiers, p->nVerbose - 1 ) )
	return -1;
      Abc_BddGarbageCollect( p, p->pFrontiers );
      return 0;
    }
  if ( !p->fRealloc || p->nObjsAlloc >= 1 << 31 )
    {
      printf( "The number of nodes exceeds the limit %u\n", p->nObjsAlloc );
      return -1;
    }
  if ( Abc_BddManRealloc( p ) )
    {
      printf( "Reallocation failed\n" );
      return -1;
    }
  return 0;
}
int Abc_BddGia( Gia_Man_t * pGia, Abc_BddMan * p )
{
  Gia_Obj_t * pObj, * pObj0, *pObj1;
  int i, nRefresh = 0;
  unsigned Cof0, Cof1;
  Gia_ManFillValue( pGia );
  Gia_ManConst0( pGia )->Value = Abc_BddLitConst0();
  Gia_ManForEachCi( pGia, pObj, i ) pObj->Value = Abc_BddLitIthVar( i );
  Gia_ManForEachAnd( pGia, pObj, i )
    {
      pObj0 = Gia_ObjFanin0( pObj );
      pObj1 = Gia_ObjFanin1( pObj );
      Cof0 = Abc_BddLitNotCond( pObj0->Value, Gia_ObjFaninC0( pObj ) );
      Cof1 = Abc_BddLitNotCond( pObj1->Value, Gia_ObjFaninC1( pObj ) );
      pObj->Value = Abc_BddAnd( p, Cof0, Cof1 );
      if ( Abc_BddLitIsInvalid( pObj->Value ) )
	{
	  if ( Abc_BddRefresh( p, &nRefresh ) )
	    return -1;
	  i--;
	  continue;
	}
      if ( p->pFrontiers != NULL )
	{
	  nRefresh = 0;
	  Vec_IntPush( p->pFrontiers, pObj->Value );
	  p->pFanouts[Gia_ObjId( pGia, pObj0 )] -= 1;
	  if ( p->pFanouts[Gia_ObjId( pGia, pObj0 )] == 0 ) Vec_IntRemove( p->pFrontiers, pObj0->Value );
	  p->pFanouts[Gia_ObjId( pGia, pObj1 )] -= 1;
	  if ( p->pFanouts[Gia_ObjId( pGia, pObj1 )] == 0 ) Vec_IntRemove( p->pFrontiers, pObj1->Value );
	}
    }
  Gia_ManForEachCo( pGia, pObj, i )
    pObj->Value = Abc_BddLitNotCond( Gia_ObjFanin0( pObj )->Value, Gia_ObjFaninC0( pObj ) );
  return 0;
}
void Abc_BddGiaTest( Gia_Man_t * pGia, int nVerbose, int nMem, char * pFileName, int fRealloc, int fGC, int nReorderThreshold, int nFinalReorder )
{
  abctime clk, clk2;
  Abc_BddMan * p;
  Vec_Int_t * vNodes;
  Gia_Obj_t * pObj;
  int i, j;
  unsigned nObjsAllocInit = 1 << nMem;
  while ( nObjsAllocInit < Gia_ManCiNum( pGia ) + 1 )
    {
      nObjsAllocInit = nObjsAllocInit << 1;
      assert( nObjsAllocInit != 0 );
    }
  clk = Abc_Clock();
  p = Abc_BddManAlloc( Gia_ManCiNum( pGia ), nObjsAllocInit, nVerbose );
  Abc_BddRefreshConfig( p, pGia, fRealloc, fGC, nReorderThreshold );
  if ( Abc_BddGia( pGia, p ) ) return;
  clk2 = Abc_Clock();
  vNodes = Vec_IntAlloc( Gia_ManCoNum( pGia ) );
  Gia_ManForEachCo( pGia, pObj, i ) Vec_IntPush( vNodes, pObj->Value );
  if ( nVerbose > 1 ) printf("\n");
  printf( "Shared BDD size = %6d nodes.", Abc_BddCountNodesArrayShared( p, vNodes ) );
  ABC_PRT( "  BDD construction time", clk2 - clk );
  printf( "Sum of BDD nodes for each BDD = %d", Abc_BddCountNodesArrayIndependent( p, vNodes ) );
  printf( "  Used nodes = %d  Allocated nodes = %u\n", p->nObjs, ( p->nObjsAlloc == 1 << 31 ) ? p->nObjsAlloc - 1 : p->nObjsAlloc );
  if ( nFinalReorder )
    {
      p->ReorderThreshold = 0.01 * nFinalReorder;
      int prev = Abc_BddCountNodesArrayShared( p, vNodes );
      clk = Abc_Clock();
      Abc_BddReorder( p, vNodes, nVerbose );
      clk2 = Abc_Clock();
      int now = Abc_BddCountNodesArrayShared( p, vNodes );
      printf( "Gain %d -> %d (%d)\n", prev, now, now - prev );
      printf( "Shared BDD size = %6d nodes.", Abc_BddCountNodesArrayShared( p, vNodes ) );
      ABC_PRT( "  Final reordering time", clk2 - clk );
      printf( "Sum of BDD nodes for each BDD = %d", Abc_BddCountNodesArrayIndependent( p, vNodes ) );
      printf( "  Used nodes = %d  Allocated nodes = %u\n", p->nObjs, ( p->nObjsAlloc == 1 << 31 ) ? p->nObjsAlloc - 1 : p->nObjsAlloc );
    }
  if ( p->ReorderThreshold != 0 )
    {
      printf( "Ordering:\n" );
      for ( i = 0; i < p->nVars; i++ )
	{
	  for ( j = 0; j < p->nVars; j++ )
	    if ( Abc_BddVar( p, Abc_BddLitIthVar( j ) ) == i ) break;
	  if ( p->nVars <= 10 ) printf( "pi%d ", j );
	  else if ( p->nVars <= 100 ) printf( "pi%02d ", j );
	  else printf( "pi%03d ", j );
	}
      printf( "\n" );
    }
  if ( pFileName != NULL ) Abc_BddWriteBlif( p, vNodes, pFileName );
  Vec_IntFree( vNodes );
  Abc_BddManFree( p );
}

/**Function*************************************************************

   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
int Abc_BddCount0s( Abc_BddMan * p, unsigned a, int depth )
{
  if ( p->nVars - depth < 0 ) return 0;
  if ( Abc_BddLitIsConst0( a ) ) return 1 << ( p->nVars - depth );
  if ( Abc_BddLitIsConst1( a ) ) return 0;
  return Abc_BddCount0s( p, Abc_BddElse( p, a ), depth + 1 ) + Abc_BddCount0s( p, Abc_BddThen( p, a ), depth + 1 );
}
int Abc_BddCount1s( Abc_BddMan * p, unsigned a, int depth )
{
  if ( p->nVars - depth < 0 ) return 0;
  if ( Abc_BddLitIsConst0( a ) ) return 0;
  if ( Abc_BddLitIsConst1( a ) ) return 1 << ( p->nVars - depth );
  return Abc_BddCount1s( p, Abc_BddElse( p, a ), depth + 1 ) + Abc_BddCount1s( p, Abc_BddThen( p, a ), depth + 1 );
}
unsigned __int128 Abc_BddCount1s128( Abc_BddMan * p, unsigned a, int depth )
{
  if ( p->nVars - depth < 0 ) return 0;
  if ( Abc_BddLitIsConst0( a ) ) return 0;
  if ( Abc_BddLitIsConst1( a ) )
    {
      unsigned __int128 i = 1;
      return i << ( p->nVars - depth );
    }
  return Abc_BddCount1s128( p, Abc_BddElse( p, a ), depth + 1 ) + Abc_BddCount1s128( p, Abc_BddThen( p, a ), depth + 1 );
}
unsigned __int128 Abc_BddCount0s128( Abc_BddMan * p, unsigned a, int depth )
{
  if ( p->nVars - depth < 0 ) return 0;
  if ( Abc_BddLitIsConst1( a ) ) return 0;
  if ( Abc_BddLitIsConst0( a ) )
    {
      unsigned __int128 i = 1;
      return i << ( p->nVars - depth );
    }
  return Abc_BddCount0s128( p, Abc_BddElse( p, a ), depth + 1 ) + Abc_BddCount0s128( p, Abc_BddThen( p, a ), depth + 1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

