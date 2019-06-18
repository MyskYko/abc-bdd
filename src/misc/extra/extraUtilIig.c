/**CFile****************************************************************

  FileName    [extraUtilVc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [vector compose and its application using the simple BDD pakcage]

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

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_BddTraverse( Abc_BddMan * p, unsigned x, Vec_Int_t * vec, Vec_Int_t * vIndex, int fConst )
{
  if ( x == 0 || x == 1 )
    {
      if ( fConst ) Vec_IntPush( vec, x );
      return;
    }
  if ( Vec_IntFind( vIndex, Abc_BddVar( p, x ) ) != -1 )
    {
      Vec_IntPush( vec, x );
      return;
    }
  Abc_BddTraverse( p, Abc_BddThen( p, x ), vec, vIndex, fConst );
  Abc_BddTraverse( p, Abc_BddElse( p, x ), vec, vIndex, fConst );
}
unsigned Abc_BddTraverseAnd( Abc_BddMan * p, unsigned x, Vec_Int_t * vIndex, int fConst )
{
  unsigned y;
  int i;
  Vec_Int_t * vec = Vec_IntAlloc( 1 );
  Abc_BddTraverse( p, x, vec, vIndex, fConst );
  unsigned Value = 1;
  Vec_IntForEachEntry( vec, y, i )
    {
      Value = Abc_BddAnd( p, y, Value );
      if ( Abc_BddLitIsInvalid( Value ) )
	{
	  Vec_IntFree( vec );
	  return Abc_BddInvalidLit();
	}
    }
  Vec_IntFree( vec );
  return Value;
}
unsigned Abc_BddTraverseOr( Abc_BddMan * p, unsigned x, Vec_Int_t * vIndex, int fConst )
{
  unsigned y;
  int i;
  Vec_Int_t * vec = Vec_IntAlloc( 1 );
  Abc_BddTraverse( p, x, vec, vIndex, fConst );
  unsigned Value = 0;
  Vec_IntForEachEntry( vec, y, i )
    {
      Value = Abc_BddOr( p, y, Value );
      if ( Abc_BddLitIsInvalid( Value ) )
	{
	  Vec_IntFree( vec );
	  return Abc_BddInvalidLit();
	}
    }
  Vec_IntFree( vec );
  return Value;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_BddGiaIig( Gia_Man_t * pGia, int nVerbose, int nMem, int nJump, int nLatch )
{
  abctime clk = Abc_Clock();
  Abc_BddMan * p;
  Gia_Obj_t * pObj;
  int i;
  int nIte = 0;
  int nInit = 0;
  unsigned X, Y, Z, K;
  unsigned * cache;
  Vec_Int_t * vars;
  Vec_Int_t * vLatchVars;
  srand( time(NULL) );
  unsigned nObjsAllocInit = 1 << nMem;
  while ( nObjsAllocInit < Gia_ManCiNum( pGia ) + 2 )
    {
      nObjsAllocInit = nObjsAllocInit << 1;
      assert( nObjsAllocInit != 0 );
    }
  if ( nVerbose > 1 )
    printf( "Allocate nodes by 2^%d\n", Abc_Base2Log( nObjsAllocInit ) );
  p = Abc_BddManAlloc( Gia_ManCiNum( pGia ), nObjsAllocInit, nVerbose > 1 );
  Abc_BddGia( pGia, nVerbose > 1, nJump, p );
  abctime clk1 = Abc_Clock();
    if ( nVerbose > 1 ) printf( "\n" );
  if ( nVerbose ) ABC_PRT( "BDD (latch) construction time", clk1 - clk );
  cache = ABC_CALLOC( unsigned, (long long)p->nObjsAlloc );
  vars = Vec_IntAlloc( Gia_ManCiNum( pGia ) );
  for ( i = 0; i < Gia_ManCiNum( pGia ) - nLatch; i++ )
    Vec_IntPush( vars, Abc_BddInvalidLit() );
  Gia_ManForEachCo( pGia, pObj, i )
    Vec_IntPush( vars, pObj->Value );
  vLatchVars = Vec_IntAlloc( nLatch );
  for ( i = 0; i < nLatch; i++ )
    Vec_IntPush( vLatchVars, Gia_ManCiNum( pGia ) - nLatch + i );
  while ( 1 )
    {
      nInit++;
      if ( nVerbose ) printf( "init %d X:\n\t", nInit );
      X = 1;
      for ( i = 0; i < nLatch; i++ )
	if ( rand() & 1 )
	  X = Abc_BddAnd( p, X, Abc_BddIthVar( Gia_ManCiNum( pGia ) - nLatch + i ) );
	else
	  X = Abc_BddAnd( p, X, Abc_BddLitNot( Abc_BddIthVar( Gia_ManCiNum( pGia ) - nLatch + i ) ) );
      X = Abc_BddLitNot( X );
      assert( !Abc_BddLitIsInvalid( X ) );
      if ( nVerbose ) Abc_BddPrint( p, X );
      while ( 1 )
	{
	  nIte++;
	  if ( nVerbose ) printf( "\n####################\n###### ite %2d ######\n####################\n", nIte );
	  Y = Abc_BddVectorCompose( p, X, vars, cache, 1 );
	  assert( !Abc_BddLitIsInvalid( Y ) );
	  Z = Abc_BddOr( p, Abc_BddLitNot( X ), Y );
	  assert( !Abc_BddLitIsInvalid( Z ) );
	  if ( Z == 1 )
	    {
	      if ( nVerbose ) printf( "Z is always 1\n" );
	      break;
	    }
	  if ( nVerbose ) printf( "Z is not always 1:\n\t" );
	  if ( nVerbose ) Abc_BddPrint( p, Z );
	  if ( nVerbose ) printf( "K:\n\t" );
	  K = Abc_BddTraverseAnd( p, Z, vLatchVars, 1 );
	  assert( !Abc_BddLitIsInvalid( K ) );
	  if ( nVerbose ) Abc_BddPrint( p, K );
	  if ( nVerbose ) printf( "next X:\n\t" );
	  X = Abc_BddAnd( p, X, K );
	  assert( !Abc_BddLitIsInvalid( X ) );
	  if ( nVerbose ) Abc_BddPrint( p, X );
	}
      if ( X != 0 && X != 1 ) break;
      if ( nVerbose ) printf( "trivial result, always %u\n", X );
    }
  abctime clk2 = Abc_Clock();
  if ( nVerbose > 1 ) printf( "\n" );
  if ( nVerbose ) ABC_PRT( "inductive invariant generation time", clk2 - clk1 );
  ABC_PRT( "total time", clk2 - clk );
  printf( "result:\n\t" );
  Abc_BddPrint( p, X );
  printf( "init %d\n", nInit );
  printf( "iteration %d\n", nIte );
  printf( "nObjs = %u\n", p->nObjs );
  ABC_FREE( cache );
  Vec_IntFree( vars );
  Vec_IntFree( vLatchVars );
  Abc_BddManFree( p );
}
void Abc_BddGiaIigReverse( Gia_Man_t * pGia, int nVerbose, int nMem, int nJump, int nLatch )
{
  abctime clk = Abc_Clock();
  Abc_BddMan * p;
  Gia_Obj_t * pObj;
  int i;
  int nIte = 0;
  int nInit = 0;
  unsigned X, Y, Z, K;
  unsigned d0, d1, r;
  unsigned * cache;
  unsigned * nextCache;
  Vec_Int_t * vars;
  Vec_Int_t * nextVars;
  Vec_Int_t * vLatchVars;
  Vec_Int_t * vNextLatchVars;
  srand( time(NULL) );
  unsigned nObjsAllocInit = 1 << nMem;
  while ( nObjsAllocInit < Gia_ManCiNum( pGia ) + nLatch + 2 )
    {
      nObjsAllocInit = nObjsAllocInit << 1;
      assert( nObjsAllocInit != 0 );
    }
  if ( nVerbose > 1 )
    printf( "Allocate nodes by 2^%d\n", Abc_Base2Log( nObjsAllocInit ) );
  p = Abc_BddManAlloc( Gia_ManCiNum( pGia ) + nLatch, nObjsAllocInit, nVerbose > 1 );
  Abc_BddGia( pGia, nVerbose > 1, nJump, p );
  abctime clk1 = Abc_Clock();
  if ( nVerbose > 1 ) printf( "\n" );
  if ( nVerbose ) ABC_PRT( "BDD (latch) construction time", clk1 - clk );
  cache = ABC_CALLOC( unsigned, (long long)p->nObjsAlloc );
  vars = Vec_IntAlloc( Gia_ManCiNum( pGia ) );
  for ( i = 0; i < Gia_ManCiNum( pGia ) - nLatch; i++ )
    Vec_IntPush( vars, Abc_BddInvalidLit() );
  Gia_ManForEachCo( pGia, pObj, i )
    Vec_IntPush( vars, pObj->Value );
  vLatchVars = Vec_IntAlloc( nLatch );
  for ( i = 0; i < nLatch; i++ )
    Vec_IntPush( vLatchVars, Gia_ManCiNum( pGia ) - nLatch + i );
  nextCache = ABC_CALLOC( unsigned, (long long)p->nObjsAlloc );
  nextVars = Vec_IntAlloc( Gia_ManCiNum( pGia ) + nLatch );
  for ( i = 0; i < Gia_ManCiNum( pGia ); i++ )
    Vec_IntPush( nextVars, Abc_BddInvalidLit() );
  for ( i = 0; i < nLatch; i++ )
    Vec_IntPush( nextVars, Abc_BddIthVar( Gia_ManCiNum( pGia ) - nLatch + i ) );
  vNextLatchVars = Vec_IntAlloc( nLatch );
  for ( i = 0; i < nLatch; i++ )
    Vec_IntPush( vNextLatchVars, Gia_ManCiNum( pGia ) + i );
  while ( 1 )
    {
      nInit++;
      if ( nVerbose ) printf( "init %d X:\n\t", nInit );
      X = 1;
      for ( i = 0; i < nLatch; i++ )
	if ( rand() & 1 )
	  X = Abc_BddAnd( p, X, Abc_BddIthVar( Gia_ManCiNum( pGia ) - nLatch + i ) );
	else
	  X = Abc_BddAnd( p, X, Abc_BddLitNot( Abc_BddIthVar( Gia_ManCiNum( pGia ) - nLatch + i ) ) );
      assert( !Abc_BddLitIsInvalid( X ) );
      if ( nVerbose ) Abc_BddPrint( p, X );
      while ( 1 )
	{
	  nIte++;
	  if ( nVerbose ) printf( "\n####################\n###### ite %2d ######\n####################\n", nIte );
	  Y = Abc_BddVectorCompose( p, X, vars, cache, 1 );
	  assert( !Abc_BddLitIsInvalid( Y ) );
	  Z = Abc_BddOr( p, Abc_BddLitNot( X ), Y );
	  assert( !Abc_BddLitIsInvalid( Z ) );
	  if ( Z == 1 )
	    {
	      if ( nVerbose ) printf( "Z is always 1\n" );
	      break;
	    }
	  if ( nVerbose ) printf( "Z is not always 1:\n\t" );
	  if ( nVerbose ) Abc_BddPrint( p, Z );
	  if ( nVerbose ) printf( "K:\n\t" );
	  K = 1;
	  Gia_ManForEachCo( pGia, pObj, i )
	    {
	      d1 = Abc_BddOr( p, Z, Abc_BddIthVar( Gia_ManCiNum( pGia ) + i ) );
	      assert( !Abc_BddLitIsInvalid( d1 ) );
	      d0 = Abc_BddOr( p, Z, Abc_BddLitNot( Abc_BddIthVar( Gia_ManCiNum( pGia ) + i ) ) );
	      assert( !Abc_BddLitIsInvalid( d0 ) );
	      r = Abc_BddIteAnd( p, pObj->Value, d1, d0 );
	      assert( !Abc_BddLitIsInvalid( r ) );
	      K = Abc_BddAnd( p, K, r );
	      assert( !Abc_BddLitIsInvalid( K ) );
	    }
	  K = Abc_BddTraverseOr( p, K, vNextLatchVars, 0 );
	  assert( !Abc_BddLitIsInvalid( K ) );
	  K = Abc_BddVectorCompose( p, K, nextVars, nextCache, 1 );
	  if ( nVerbose ) Abc_BddPrint( p, K );
	  if ( nVerbose ) printf( "next X:\n\t" );
	  X = Abc_BddOr( p, X, K );
	  assert( !Abc_BddLitIsInvalid( X ) );
	  if ( nVerbose ) Abc_BddPrint( p, X );
	}
      if ( X != 0 && X != 1 ) break;
      if ( nVerbose ) printf( "trivial result, always %u\n", X );
    }
  abctime clk2 = Abc_Clock();
  if ( nVerbose > 1 ) printf( "\n" );
  if ( nVerbose ) ABC_PRT( "inductive invariant generation time", clk2 - clk1 );
  ABC_PRT( "total time", clk2 - clk );
  printf( "result:\n\t" );
  Abc_BddPrint( p, X );
  printf( "init %d\n", nInit );
  printf( "iteration %d\n", nIte );
  printf( "nObjs = %u\n", p->nObjs );
  ABC_FREE( cache );
  Vec_IntFree( vars );
  Vec_IntFree( vLatchVars );
  ABC_FREE( nextCache );
  Vec_IntFree( nextVars );
  Vec_IntFree( vNextLatchVars );
  Abc_BddManFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

