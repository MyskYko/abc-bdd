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
  int headBvar;
  int * q;
  q = p->pUnique + ( Abc_BddHash( Var, Then, Else ) & p->nUniqueMask );
  for ( ; *q; q = p->pNexts + *q )
    if ( Abc_BddVarOfBvar( p, *q ) == Var &&
	 Abc_BddThenOfBvar( p, *q ) == Then &&
	 Abc_BddElseOfBvar( p, *q ) == Else )
      return Abc_BddBvar2Lit( *q, 0 );
  q = p->pUnique + ( Abc_BddHash( Var, Then, Else ) & p->nUniqueMask );
  headBvar = *q;
  if ( Abc_BddIsLimit( p ) )
    {
      for ( ; p->nMinRemoved < p->nObjs; p->nMinRemoved++ )
	if ( Abc_BddBvarIsRemoved( p, p->nMinRemoved ) ) break;
      if ( p->nMinRemoved == p->nObjs ) return Abc_BddLitInvalid();
      *q = p->nMinRemoved++;
    }
  else *q = p->nObjs++;
  Abc_BddSetVarOfBvar( p, *q, Var );
  Abc_BddSetThenOfBvar( p, *q, Then );
  Abc_BddSetElseOfBvar( p, *q, Else );
  Abc_BddSetNextOfBvar( p, *q, headBvar );
  if ( p->nVerbose > 2 )
    printf( "\rAdded node %10d: Var = %3d  Then = %10u  Else = %10u  MinRemoved = %10u", *q, Var, Then, Else, p->nMinRemoved );
  return Abc_BddBvar2Lit( *q, 0 );
}
unsigned Abc_BddUniqueCreate( Abc_BddMan * p, int Var, unsigned Then, unsigned Else )
{
  if ( Abc_BddLitIsEq( Then, Else ) ) return Else;
  if ( !Abc_BddLitIsCompl( Else ) )   return Abc_BddUniqueCreateInt( p, Var, Then, Else );
  return Abc_BddLitNot( Abc_BddUniqueCreateInt( p, Var, Abc_BddLitNot( Then ), Abc_BddLitNot( Else ) ) );
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
  return ( pEnt[0] == Arg1 && pEnt[1] == Arg2 ) ? pEnt[2] : Abc_BddLitInvalid();
}
static inline unsigned Abc_BddCacheInsert( Abc_BddMan * p, unsigned Arg1, unsigned Arg2, unsigned Res )
{
  unsigned * pEnt = p->pCache + 3*(long long)( Abc_BddHash( 0, Arg1, Arg2 ) & p->nCacheMask );
  pEnt[0] = Arg1; pEnt[1] = Arg2; pEnt[2] = Res;
  return Res;
}
static inline void Abc_BddCacheRemove( Abc_BddMan * p ) {
  ABC_FREE( p->pCache );
  p->pCache = ABC_CALLOC( unsigned, 3 * (long long)( p->nCacheMask + 1 ) );
}

/**Function*************************************************************

   Synopsis    [Count fanout of gates.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddGiaCountFanout( Gia_Man_t * pGia, int * pFanouts )
{
  int i;
  Gia_Obj_t * pObj;
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
  int i;
  Abc_BddMan * p;
  if ( nVerbose ) printf( "Allocate nodes by 2^%d\n", Abc_Base2Log( nObjs ) );
  p = ABC_CALLOC( Abc_BddMan, 1 );
  p->nVars       = nVars;
  p->nObjsAlloc  = nObjs;
  p->nUniqueMask = ( 1 << Abc_Base2Log( nObjs ) ) - 1;
  p->nCacheMask  = ( 1 << Abc_Base2Log( nObjs ) ) - 1;
  p->nMinRemoved = nObjs - 1;
  p->nVerbose    = nVerbose;
  p->pUnique     = ABC_CALLOC( int, p->nUniqueMask + 1 );
  p->pNexts      = ABC_CALLOC( int, p->nUniqueMask + 1 );
  p->pCache      = ABC_CALLOC( unsigned, 3 * (long long)( p->nCacheMask + 1 ) );
  p->pObjs       = ABC_CALLOC( unsigned, 2 * (long long)p->nObjsAlloc );
  p->pMark       = ABC_CALLOC( unsigned char, p->nObjsAlloc );
  p->fRealloc    = 0;
  p->fGC         = 0;
  p->ReoThold    = 0;
  p->pFrontiers  = NULL;
  p->pEdges      = NULL;
  p->liveBvars   = NULL;
  if ( nVars < 0xff )
    p->pVars     = ABC_CALLOC( unsigned char, p->nObjsAlloc ),
      p->pSVars = NULL;
  else
    p->pSVars    = ABC_CALLOC( unsigned short, p->nObjsAlloc ),
      p->pVars = NULL;
  if ( p->nVars > (int)Abc_BddVarConst( p ) )
    {
      printf("Error: Number of variables is too many\n");
      return NULL;
    }
  if ( !p->pUnique || !p->pNexts || !p->pCache || !p->pObjs || !p->pMark || (!p->pVars && !p->pSVars) )
    {
      printf("Error: Allocation failed\n");
      return NULL;
    }
  Abc_BddSetVarOfBvar( p, Abc_BddBvarConst(), Abc_BddVarConst( p ) );
  p->nObjs = 1;
  for ( i = 0; i < nVars; i++ ) Abc_BddUniqueCreate( p, i, Abc_BddLitConst1(), Abc_BddLitConst0() );
  return p;
}
int Abc_BddRefreshConfig( Abc_BddMan * p,  int fRealloc, int fGC, int nReorderThreshold )
{
  int i;
  p->fRealloc = fRealloc;
  p->fGC = fGC;
  p->ReoThold = 0.01 * nReorderThreshold;
  if ( fGC || p->ReoThold != 0 )
    p->pFrontiers = Vec_IntAlloc( 1 );
  if ( p->ReoThold != 0 )
    {
      p->pEdges = ABC_CALLOC( unsigned, p->nObjsAlloc );
      if ( !p->pEdges )
	{
	  printf("Error: Allocation failed\n");
	  return -1;
	}
      p->liveBvars = ABC_ALLOC( Vec_Int_t *, p->nVars + 2 );
      for ( i = 0; i < p->nVars + 2; i++ )
	p->liveBvars[i] = Vec_IntAlloc( 1 );
    }
  return 0;
}
void Abc_BddManFree( Abc_BddMan * p )
{
  int i;
  if ( p->nVerbose > 2 )
    printf( "Free BDD nodes: Var = %u  Obj = %u  Alloc = %u\n", p->nVars, p->nObjs, p->nObjsAlloc - 1 );
  ABC_FREE( p->pUnique );
  ABC_FREE( p->pNexts );
  ABC_FREE( p->pCache );
  ABC_FREE( p->pObjs );
  if ( p->pVars ) ABC_FREE( p->pVars );
  if ( p->pSVars ) ABC_FREE( p->pSVars );
  if ( p->pFrontiers != NULL ) Vec_IntFree( p->pFrontiers );
  if ( p->pEdges != NULL) ABC_FREE( p->pEdges );
  if ( p->liveBvars != NULL)
    {
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
  int nUniqueMaskOld = p->nUniqueMask;
  unsigned nObjsAllocOld = p->nObjsAlloc;
  p->nObjsAlloc  = p->nObjsAlloc + p->nObjsAlloc;
  if ( p->nObjsAlloc == 0 )
    {
      printf("Error: Reallocation failed\n");
      return -1;
    }
  if ( p->nVerbose ) printf( "\tReallocate nodes by 2^%d\n", Abc_Base2Log( p->nObjsAlloc ) );
  p->nUniqueMask = ( 1 << Abc_Base2Log( p->nObjsAlloc ) ) - 1;
  p->nCacheMask  = ( 1 << Abc_Base2Log( p->nObjsAlloc ) ) - 1;
  p->pUnique     = ABC_REALLOC( int, p->pUnique, p->nUniqueMask + 1 );
  p->pNexts      = ABC_REALLOC( int, p->pNexts, p->nUniqueMask + 1 );
  p->pObjs       = ABC_REALLOC( unsigned, p->pObjs, 2 * (long long)p->nObjsAlloc );
  p->pMark       = ABC_REALLOC( unsigned char, p->pMark, p->nObjsAlloc );
  if ( p->pVars )
    p->pVars     = ABC_REALLOC( unsigned char, p->pVars, p->nObjsAlloc );
  else
    p->pSVars    = ABC_REALLOC( unsigned short, p->pSVars, p->nObjsAlloc );
  if ( !p->pUnique || !p->pNexts || !p->pObjs || !p->pMark || (!p->pVars && !p->pSVars) )
    {
      printf("Error: Reallocation failed\n");
      return -1;
    }
  memset( p->pUnique + ( nUniqueMaskOld + 1 ), 0, sizeof(int) * ( nUniqueMaskOld + 1 ) );
  memset( p->pNexts + ( nUniqueMaskOld + 1 ), 0, sizeof(int) * ( nUniqueMaskOld + 1 ) );
  memset( p->pObjs + 2 * (long long)nObjsAllocOld, 0, sizeof(unsigned) * 2 * (long long)nObjsAllocOld );
  memset( p->pMark + nObjsAllocOld, 0, sizeof(unsigned char) * nObjsAllocOld );
  if ( p->pVars )
    memset( p->pVars + nObjsAllocOld, 0, sizeof(unsigned char) * nObjsAllocOld );
  else
    memset( p->pSVars + nObjsAllocOld, 0, sizeof(unsigned short) * nObjsAllocOld );
  Abc_BddCacheRemove( p );
  Abc_BddRehash( p );
  if ( p->pEdges != NULL )
    {
      p->pEdges = ABC_REALLOC( unsigned, p->pEdges, p->nObjsAlloc );
      if ( !p->pEdges )
	{
	  printf("Error: Reallocation failed\n");
	  return -1;
	}
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
unsigned Abc_BddAnd_rec( Abc_BddMan * p, unsigned a, unsigned b )
{
  unsigned r0, r1, r;
  unsigned s0, s1, t0, t1;
  if ( Abc_BddLitIsConst0( a ) ) return a;
  if ( Abc_BddLitIsConst0( b ) ) return b;
  if ( Abc_BddLitIsConst1( a ) ) return b;
  if ( Abc_BddLitIsConst1( b ) ) return a;
  if ( Abc_BddLitIsEq( a, b ) ) return a;
  if ( a > b )  return Abc_BddAnd( p, b, a );
  r = Abc_BddCacheLookup( p, a, b );
  if ( !Abc_BddLitIsInvalid( r ) ) return r;
  if ( Abc_BddVar( p, a ) < Abc_BddVar( p, b ) )
    s0 = Abc_BddElse( p, a ), t0 = b, s1 = Abc_BddThen( p, a ), t1 = b;
  else if ( Abc_BddVar( p, a ) > Abc_BddVar( p, b ) )
    s0 = a, t0 = Abc_BddElse( p, b ), s1 = a, t1 = Abc_BddThen( p, b );
  else // if ( Abc_BddVar( p, a ) == Abc_BddVar( p, b ) )
    s0 = Abc_BddElse( p, a ), t0 = Abc_BddElse( p, b ), s1 = Abc_BddThen( p, a ), t1 = Abc_BddThen( p, b );
  r0 = Abc_BddAnd( p, s0, t0 );
  if ( Abc_BddLitIsInvalid( r0 ) ) return r0;
  r1 = Abc_BddAnd( p, s1, t1 );
  if ( Abc_BddLitIsInvalid( r1 ) ) return r1;
  r = Abc_BddUniqueCreate( p, Abc_MinInt( Abc_BddVar( p, a ), Abc_BddVar( p, b ) ), r1, r0 );
  if ( Abc_BddLitIsInvalid( r ) ) return r;
  return Abc_BddCacheInsert( p, a, b, r );
}
unsigned Abc_BddAnd( Abc_BddMan * p, unsigned a, unsigned b )
{
  if ( Abc_BddLitIsInvalid( a ) ) return a;
  if ( Abc_BddLitIsInvalid( b ) ) return b;
  return Abc_BddAnd_rec( p, a, b );
}
unsigned Abc_BddOr( Abc_BddMan * p, unsigned a, unsigned b )
{
  if ( Abc_BddLitIsInvalid( a ) ) return a;
  if ( Abc_BddLitIsInvalid( b ) ) return b;
  return Abc_BddLitNot( Abc_BddAnd_rec( p, Abc_BddLitNot( a ), Abc_BddLitNot( b ) ) );
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

   Synopsis    [write blif]

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
void Abc_BddWriteBlif( Abc_BddMan * p, Vec_Int_t * vNodes, char * pFileName, int fName )
{
  int i, j;
  unsigned x;
  FILE * f = fopen( pFileName, "w" );
  fprintf( f, ".model top\n" );
  fprintf( f, ".inputs" );
  if ( fName )
    for ( i = 0; i < p->nVars; i++ )
      {
	for ( j = 0; j < p->nVars; j++ )
	  if ( Abc_BddVar( p, Abc_BddLitIthVar( j ) ) == i ) break;
	if ( p->nVars <= 10 ) fprintf( f, " pi%d", j );
	else if ( p->nVars <= 100 ) fprintf( f, " pi%02d", j );
	else fprintf( f, " pi%03d", j );
      }
  else
    for ( i = 0; i < p->nVars; i++ )
      if ( p->nVars <= 10 ) fprintf( f, " pi%d ", i );
      else if ( p->nVars <= 100 ) fprintf( f, " pi%02d ", i );
      else fprintf( f, " pi%03d ", i );
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

   Synopsis    [Generate Gia from BDD.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_Bdd2Gia_rec( Abc_BddMan * p, int x, int * Values, Gia_Man_t * pGia )
{
  int VarBvar, ThenBvar, ElseBvar, compl;
  unsigned i;
  i = Abc_BddBvar2Lit( x, 0 );
  if ( Abc_BddLitIsConst( i ) ) return;
  if ( Abc_BddMark( p, i ) ) return;
  Abc_BddSetMark( p, i, 1 );
  VarBvar = Abc_BddBvarIthVar( Abc_BddVar( p, i ) );
  ThenBvar = Abc_BddLit2Bvar( Abc_BddThen( p, i ) );
  ElseBvar = Abc_BddLit2Bvar( Abc_BddElse( p, i ) );
  compl = Abc_BddLitIsCompl( Abc_BddThen( p, i ) );
  Abc_Bdd2Gia_rec( p, ThenBvar, Values, pGia );
  Abc_Bdd2Gia_rec( p, ElseBvar, Values, pGia );
  Values[x] = Gia_ManHashMux( pGia, Values[VarBvar], Abc_LitNotCond( Values[ThenBvar], compl ), Values[ElseBvar] ); 
}
Gia_Man_t * Abc_Bdd2Gia( Abc_BddMan * p, Vec_Int_t * vNodes )
{
  int i, j;
  int * Values;
  unsigned x;
  Gia_Man_t * pGia, * pTemp;
  pGia = Gia_ManStart( p->nObjs );
  Gia_ManHashAlloc( pGia );
  Values = ABC_CALLOC( int, p->nObjsAlloc );
  Values[Abc_BddLit2Bvar( Abc_BddLitConst0() ) ] = Gia_ManConst0Lit( pGia );
  for ( i = 0; i < p->nVars; i++ )
    Values[Abc_BddBvarIthVar( Abc_BddVar( p, Abc_BddLitIthVar( i ) ) )] = Gia_ManAppendCi( pGia );
  Vec_IntForEachEntry( vNodes, x, i )
    {
      j = Abc_BddLit2Bvar( x );
      Abc_Bdd2Gia_rec( p, j, Values, pGia );
      Gia_ManAppendCo( pGia, Abc_LitNotCond( Values[j], Abc_BddLitIsCompl( x ) ) );
    }
  Vec_IntForEachEntry( vNodes, x, i )
    Abc_BddUnmark_rec( p, x );
  pGia = Gia_ManCleanup( pTemp = pGia );
  Gia_ManStop( pTemp );
  return pGia;
}

/**Function*************************************************************

   Synopsis    [Remove unnecessary BDD nodes.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddRemoveNodeByBvar( Abc_BddMan * p, int i )
{
  int * q, *q_next;
  q = p->pUnique + ( Abc_BddHash( Abc_BddVarOfBvar( p, i ), Abc_BddThenOfBvar( p, i ), Abc_BddElseOfBvar( p, i ) ) & p->nUniqueMask );
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == i ) break;
  q_next = p->pNexts + *q;
  *q = *q_next;
  *q_next = 0;
  Abc_BddSetBvarRemoved( p, i );
  if ( p->nMinRemoved > i ) p->nMinRemoved = i;
}
void Abc_BddGarbageCollect( Abc_BddMan * p, Vec_Int_t * pFrontiers )
{
  int i;
  unsigned x;
  if ( p->nVerbose ) printf("\tGarbage collect\n");
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
int Abc_BddRefresh( Abc_BddMan * p, int * nRefresh )
{
  *nRefresh += 1;
  if ( p->nVerbose > 1 ) printf( "\n" );
  if ( p->nVerbose ) printf( "Refresh %d\n", *nRefresh );
  if ( *nRefresh <= 1 && p->fGC )
    {
      Abc_BddGarbageCollect( p, p->pFrontiers );
      return 0;
    }
  if ( *nRefresh <= 2 && p->ReoThold != 0 && p->nObjsAlloc > 4000 )
    {
      if ( p->nVerbose ) printf("\tReordering\n");
      if ( Abc_BddReorder( p, p->pFrontiers, p->nVerbose - 1 ) ) return -1;
      Abc_BddGarbageCollect( p, p->pFrontiers );
      return 0;
    }
  if ( p->fRealloc && p->nObjsAlloc < 1 << 31 )
    {
      if ( Abc_BddManRealloc( p ) ) return -1;
      return 0;
    }
  printf( "The number of nodes exceeds the limit %u\n", p->nObjsAlloc );
  return -1;
}
int Abc_BddGia( Gia_Man_t * pGia, Abc_BddMan * p )
{
  int i, nRefresh = 0;
  int * pFanouts = NULL;
  unsigned Cof0, Cof1;
  Gia_Obj_t * pObj, * pObj0, *pObj1;
  if ( p->pFrontiers != NULL )
    {
      pFanouts = ABC_CALLOC( int, pGia->nObjs );
      if ( !pFanouts ) return -1;
      Abc_BddGiaCountFanout( pGia, pFanouts );
    }
  Gia_ManFillValue( pGia );
  Gia_ManConst0( pGia )->Value = Abc_BddLitConst0();
  Gia_ManForEachCi( pGia, pObj, i ) pObj->Value = Abc_BddLitIthVar( i );
  Gia_ManForEachAnd( pGia, pObj, i )
    {
      pObj0 = Gia_ObjFanin0( pObj );
      pObj1 = Gia_ObjFanin1( pObj );
      Cof0 = Abc_BddLitNotCond( pObj0->Value, Gia_ObjFaninC0( pObj ) );
      Cof1 = Abc_BddLitNotCond( pObj1->Value, Gia_ObjFaninC1( pObj ) );
      pObj->Value = Abc_BddAnd_rec( p, Cof0, Cof1 );
      if ( Abc_BddLitIsInvalid( pObj->Value ) )
	{
	  if ( Abc_BddRefresh( p, &nRefresh ) ) return -1;
	  i--;
	  continue;
	}
      nRefresh = 0;
      if ( p->pFrontiers != NULL )
	{
	  Vec_IntPush( p->pFrontiers, pObj->Value );
	  pFanouts[Gia_ObjId( pGia, pObj0 )] -= 1;
	  if ( pFanouts[Gia_ObjId( pGia, pObj0 )] == 0 ) Vec_IntRemove( p->pFrontiers, pObj0->Value );
	  pFanouts[Gia_ObjId( pGia, pObj1 )] -= 1;
	  if ( pFanouts[Gia_ObjId( pGia, pObj1 )] == 0 ) Vec_IntRemove( p->pFrontiers, pObj1->Value );
	}
    }
  Gia_ManForEachCo( pGia, pObj, i )
    pObj->Value = Abc_BddLitNotCond( Gia_ObjFanin0( pObj )->Value, Gia_ObjFaninC0( pObj ) );
  if ( p->pFrontiers != NULL ) ABC_FREE( pFanouts );
  return 0;
}
void Abc_BddGiaTest( Gia_Man_t * pGia, int nVerbose, int nMem, char * pFileName, int fName, int fRealloc, int fGC, int nReorderThreshold, int nFinalReorder )
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
      if ( nObjsAllocInit == 0 )
	{
	  printf("Error: Number of inputs is too large\n");
	  return;
	}
    }
  clk = Abc_Clock();
  p = Abc_BddManAlloc( Gia_ManCiNum( pGia ), nObjsAllocInit, nVerbose );
  if ( !p ) return;
  if ( Abc_BddRefreshConfig( p, fRealloc, fGC, nReorderThreshold ) ) return;
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
      p->ReoThold = 0.01 * nFinalReorder;
      i = Abc_BddCountNodesArrayShared( p, vNodes );
      clk = Abc_Clock();
      Abc_BddReorder( p, vNodes, nVerbose );
      clk2 = Abc_Clock();
      j = Abc_BddCountNodesArrayShared( p, vNodes );
      printf( "Gain %d -> %d (%d)\n", i, j, j - i );
      printf( "Shared BDD size = %6d nodes.", Abc_BddCountNodesArrayShared( p, vNodes ) );
      ABC_PRT( "  Final reordering time", clk2 - clk );
      printf( "Sum of BDD nodes for each BDD = %d", Abc_BddCountNodesArrayIndependent( p, vNodes ) );
      printf( "  Used nodes = %d  Allocated nodes = %u\n", p->nObjs, ( p->nObjsAlloc == 1 << 31 ) ? p->nObjsAlloc - 1 : p->nObjsAlloc );
    }
  if ( p->ReoThold != 0 )
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
  if ( pFileName != NULL ) Abc_BddWriteBlif( p, vNodes, pFileName, fName );
  Vec_IntFree( vNodes );
  Abc_BddManFree( p );
}

/**Function*************************************************************

   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
unsigned Abc_BddUnivAbstract_rec( Abc_BddMan * p, unsigned x, Vec_Int_t * vVars )
{
  int Var;
  unsigned Then, Else;
  if ( Abc_BddLitIsConst( x ) ) return x;
  Then = Abc_BddUnivAbstract_rec( p, Abc_BddThen( p, x ), vVars );
  if ( Abc_BddLitIsInvalid( Then ) ) return Then;
  Else = Abc_BddUnivAbstract_rec( p, Abc_BddElse( p, x ), vVars );
  if ( Abc_BddLitIsInvalid( Else ) ) return Else;
  Var = Abc_BddVar( p, x );
  if ( Vec_IntFind( vVars, Var ) != -1 )
    return Abc_BddAnd_rec( p, Then, Else );
  return Abc_BddUniqueCreate( p, Var, Then, Else );
}
unsigned Abc_BddUnivAbstract( Abc_BddMan * p, unsigned x, Vec_Int_t * vVars )
{
  if ( Abc_BddLitIsInvalid( x ) ) return x;
  Abc_BddUnivAbstract_rec( p, x, vVars );
}

/**Function*************************************************************

   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
int Abc_BddCount0s( Abc_BddMan * p, unsigned a, int depth )
{
  if ( p->nVars < depth ) return 0;
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

