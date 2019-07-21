/**CFile****************************************************************

   FileName    [extraUtilMult.c]

   SystemName  [ABC: Logic synthesis and verification system.]

   PackageName [extra]

   Synopsis    [Dynamic Variable Reordering for simple BDD package]

   Author      [Yukio Miyasaka]
  
   Affiliation [U Tokyo]

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

struct Abc_BddNode_ {
  int Bvar;
  unsigned Then;
  unsigned Else;
  int Edge;
};
typedef struct Abc_BddNode_ Abc_BddNode;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
void Abc_BddP_rec( Abc_BddMan * p, unsigned i )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  if ( Abc_BddMark( p, i ) ) return;
  printf("Bvar %d  Var %3d  Then %5d  Else %5d\n", Abc_BddLit2Bvar( i ), Abc_BddVar( p, i ), Abc_BddThen( p, i ), Abc_BddElse( p, i ) );
  Abc_BddSetMark( p, i, 1 );
  Abc_BddP_rec( p, Abc_BddElse( p, i ) );
  Abc_BddP_rec( p, Abc_BddThen( p, i ) );
}
void Abc_BddP( Abc_BddMan * p, Vec_Int_t * pFunctions )
{
  int i;
  unsigned a;
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddP_rec( p, a );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddP_rec( p, Abc_BddLitIthVar( i ) );
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddUnmark_rec( p, a );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddUnmark_rec( p, Abc_BddLitIthVar( i ) );
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline void Abc_BddSimulateShiftBvar( Abc_BddMan * p, int i, int d )
{
  // change
  p->pVars[i] = p->pVars[i] + d;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline int Abc_BddSimulateSwapBvar( Abc_BddMan * p, int i )
{
  int Var = Abc_BddVarOfBvar( p, i );
  unsigned Then = Abc_BddThenOfBvar( p, i );
  unsigned Else = Abc_BddElseOfBvar( p, i );
  unsigned f00, f01, f10, f11, newThen, newElse;
  int b;
  unsigned hash;
  int * q;
  // new chlidren
   if ( Abc_BddVar( p, Then ) == Var || Abc_BddVar( p, Then ) == Var + 1 )
    f11 = Abc_BddThen( p, Then ), f10 = Abc_BddElse( p, Then );
  else
    f11 = f10 = Then;
  if ( Abc_BddVar( p, Else ) == Var || Abc_BddVar( p, Else ) == Var + 1)
    f01 = Abc_BddThen( p, Else ), f00 = Abc_BddElse( p, Else );
  else
    f01 = f00 = Else;
  if ( f11 == f01 ) newThen = f11;
  else
    {
      int fCompl = 0;
      if ( Abc_BddLitIsCompl( f01 ) )
	{
	  fCompl = 1;
	  f11 = Abc_BddLitNot( f11 );
	  f01 = Abc_BddLitNot( f01 );
	}
      newThen = Abc_BddLitInvalid();
      hash = Abc_BddHash( 0, f11, f01 ) & p->nTableMask;
      q = p->pTable + hash;
      for ( ; *q; q = p->pNextsTmp + *q )
	if ( Abc_BddVarOfBvar( p, *q ) != Var + 1 || *q >= p->nSimObjs )
	  {
	    *q = 0;
	    break;
	  }
	else if ( Abc_BddThenOfBvar( p, *q ) == f11 &&
		  Abc_BddElseOfBvar( p, *q ) == f01 &&
		  Abc_BddEdgeOfBvar( p, *q ) )
	  {
	    newThen = Abc_BddBvar2Lit( *q, 0 );
	    break;
	  }
      if ( Abc_BddLitIsInvalid( newThen ) )
	{
	  if ( (unsigned)p->nSimObjs == p->nObjsAlloc ||
	       (unsigned)p->nSimObjs == Abc_BddLit2Bvar( Abc_BddLitInvalid() ) )
	    return 1;
	  b = p->nSimObjs++;
	  newThen = Abc_BddBvar2Lit( b, 0 );
	  Abc_BddSetVarOfBvar( p, b, Var + 1 );
	  Abc_BddSetThenOfBvar( p, b, f11 );
	  Abc_BddSetElseOfBvar( p, b, f01 );
	  Abc_BddSetEdgeOfBvar( p, b, 0 );
	  Abc_BddIncEdgeNonConst( p, f11 );
	  Abc_BddIncEdgeNonConst( p, f01 );
	  Vec_IntPush( p->liveBvars[p->nVars + 1], b );
	  q = p->pTable + hash;
	  Abc_BddSetNextTmpOfBvar( p, b, *q );
	  *q = b;
	}
      newThen = Abc_BddLitNotCond( newThen, fCompl );
    }
  Abc_BddIncEdgeNonConst( p, newThen );
  if ( f10 == f00 ) newElse = f10;
  else
    {
      newElse = Abc_BddLitInvalid();
      hash = Abc_BddHash( 0, f10, f00 ) & p->nTableMask;
      q = p->pTable + hash;
      for ( ; *q; q = p->pNextsTmp + *q )
	if ( Abc_BddVarOfBvar( p, *q ) != Var + 1 || *q >= p->nSimObjs )
	  {
	    *q = 0;
	    break;
	  }
	else if ( Abc_BddThenOfBvar( p, *q ) == f10 &&
		  Abc_BddElseOfBvar( p, *q ) == f00 &&
		  Abc_BddEdgeOfBvar( p, *q ) )
	  {
	    newElse = Abc_BddBvar2Lit( *q, 0 );
	    break;
	  }
      if ( Abc_BddLitIsInvalid( newElse ) )
	{
	  if ( (unsigned)p->nSimObjs == p->nObjsAlloc ||
	       (unsigned)p->nSimObjs == Abc_BddLit2Bvar( Abc_BddLitInvalid() ) )
	    return 1;
	  b = p->nSimObjs++;
	  newElse = Abc_BddBvar2Lit( b, 0 );
	  Abc_BddSetVarOfBvar( p, b, Var + 1 );
	  Abc_BddSetThenOfBvar( p, b, f10 );
	  Abc_BddSetElseOfBvar( p, b, f00 );
	  Abc_BddSetEdgeOfBvar( p, b, 0 );
	  Abc_BddIncEdgeNonConst( p, f10 );
	  Abc_BddIncEdgeNonConst( p, f00 );
	  Vec_IntPush( p->liveBvars[p->nVars + 1], b );
	  q = p->pTable + hash;
	  Abc_BddSetNextTmpOfBvar( p, b, *q );
	  *q = b;
	}
    }
  Abc_BddIncEdgeNonConst( p, newElse );
  // change
  Abc_BddSetThenOfBvar( p, i, newThen );
  Abc_BddSetElseOfBvar( p, i, newElse );
  return 0;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
// swap (pos)-th variable and (pos+1)-th variable
static inline int Abc_BddSimulateSwap( Abc_BddMan * p, int pos, int * diff )
{
  int i;
  int fOutOfNodes = 0;
  int b;
  Vec_IntShrink( p->liveBvars[p->nVars], 0 );
  Vec_IntShrink( p->liveBvars[p->nVars + 1], 0 );
  // walk upper level
  Vec_IntForEachEntry( p->liveBvars[pos], b, i )
    if ( Abc_BddVar( p, Abc_BddThenOfBvar( p, b ) ) == pos + 1 ||
	 Abc_BddVar( p, Abc_BddElseOfBvar( p, b ) ) == pos + 1 )
      {
	Abc_BddDecEdgeNonConst( p, Abc_BddThenOfBvar( p, b ) );
	Abc_BddDecEdgeNonConst( p, Abc_BddElseOfBvar( p, b ) );
      }
    else
      {
	Abc_BddSimulateShiftBvar( p, b, 1 );
	Vec_IntPush( p->liveBvars[p->nVars + 1], b );
	// register
	int Var = Abc_BddVarOfBvar( p, b );
	unsigned Then = Abc_BddThenOfBvar( p, b );
	unsigned Else = Abc_BddElseOfBvar( p, b );
	unsigned hash = Abc_BddHash( 0, Then, Else ) & p->nTableMask;
	int * q = p->pTable + hash;
	for ( ; *q; q = p->pNextsTmp + *q )
	  if ( p->pVars[*q] != Var || *q == b )
	    {
	      *q = 0;
	      break;
	    }
	q = p->pTable + hash;
	Abc_BddSetNextTmpOfBvar( p, b, *q );
	*q = b;
      }
  // walk lower level
  Vec_IntForEachEntry( p->liveBvars[pos + 1], b, i )
    if ( !Abc_BddEdgeOfBvar( p, b ) )
      {
	Abc_BddDecEdgeNonConst( p, Abc_BddThenOfBvar( p, b ) );
	Abc_BddDecEdgeNonConst( p, Abc_BddElseOfBvar( p, b ) );
      }
    else
      {
	Abc_BddSimulateShiftBvar( p, b, -1 );
	Vec_IntPush( p->liveBvars[p->nVars], b );
      }
  // walk upper level again
  Vec_IntForEachEntry( p->liveBvars[pos], b, i )
    if ( Abc_BddVarOfBvar( p, b ) == pos )
      {
	if ( Abc_BddSimulateSwapBvar( p, b ) )
	  {
	    fOutOfNodes = 1;
	    break;
	  }
	Vec_IntPush( p->liveBvars[p->nVars], b );
      }
  if ( fOutOfNodes ) return 1;
  // swap liveBvars
  *diff += Vec_IntSize( p->liveBvars[p->nVars] ) + Vec_IntSize( p->liveBvars[p->nVars + 1] ) - Vec_IntSize( p->liveBvars[pos] ) - Vec_IntSize( p->liveBvars[pos + 1] );
  Vec_Int_t * tmp;
  tmp = p->liveBvars[pos];
  p->liveBvars[pos] = p->liveBvars[p->nVars];
  p->liveBvars[p->nVars] = tmp;
  tmp = p->liveBvars[pos + 1];
  p->liveBvars[pos + 1] = p->liveBvars[p->nVars + 1];
  p->liveBvars[p->nVars + 1] = tmp;
  return 0;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline int Abc_BddSimulateShift( Abc_BddMan * p, int pos, int distance, int fUp, int * bestPos, int * bestDiff, int fVerbose )
{
  int i, j;
  int curPos = pos;
  int diff = 0;
  int fOutOfNodes = 0;
  Abc_BddNode * x;
  p->nSimObjs = p->nObjs;
  for ( j = 0; j < distance; j++ )
    {
      if ( fUp ) curPos -= 1;
      if ( Abc_BddSimulateSwap( p, curPos, &diff ) )
	{
	  if ( !fUp ) curPos += 1;
	  fOutOfNodes = 1;
	  break;
	}
      if ( !fUp ) curPos += 1;
      if ( diff < *bestDiff )
	{
	  *bestDiff = diff;
	  *bestPos = curPos;
	}
      if ( fVerbose )
	printf("  current position %d  gain %d\n", curPos, diff);
    }
  for ( i = 0; i < p->nVars; i++ )
    if ( ( fUp && curPos <= i && i <= pos ) || ( !fUp && curPos >= i && i >= pos ) )
      Vec_IntShrink( p->liveBvars[i], 0 );
  for ( i = 0; i < p->nVars; i++ )
    Vec_PtrForEachEntry( Abc_BddNode *, p->liveNodes[i], x, j )
      {
	if ( ( fUp && curPos <= i && i <= pos ) || ( !fUp && curPos >= i && i >= pos ) )
	  {
	    Abc_BddSetVarOfBvar( p, x->Bvar, i );
	    Abc_BddSetThenOfBvar( p, x->Bvar, x->Then );
	    Abc_BddSetElseOfBvar( p, x->Bvar, x->Else );
	    Vec_IntPush( p->liveBvars[i], x->Bvar );
	  }
	Abc_BddSetEdgeOfBvar( p, x->Bvar, x->Edge );
      }
  return fOutOfNodes;
}

void Abc_BddReorder2Alloc( Abc_BddMan * p )
{
  int i;
  p->liveBvars = ABC_ALLOC( Vec_Int_t *, p->nVars + 2);
  for ( i = 0; i < p->nVars + 2; i++ )
    p->liveBvars[i] = Vec_IntAlloc( p->nObjsAlloc / p->nVars );
  p->pEdges = ABC_CALLOC( unsigned, p->nObjsAlloc );
  assert( p->pEdges );
  p->liveNodes = ABC_ALLOC( Vec_Ptr_t *, p->nVars + 2);
  for ( i = 0; i < p->nVars + 2; i++ )
    p->liveNodes[i] = Vec_PtrAlloc( p->nObjsAlloc / p->nVars );
  p->nTableMask = ( 1 << Abc_Base2Log( p->nObjsAlloc / p->nVars ) ) - 1;
  p->pTable = ABC_CALLOC( int, p->nTableMask + 1 );
  p->pNextsTmp = ABC_CALLOC( int, p->nObjsAlloc );
}
void Abc_BddReorder2Free( Abc_BddMan * p )
{
  int i;
  ABC_FREE( p->pEdges );
  for ( i = 0; i < p->nVars + 2; i++ )
    Vec_IntFree( p->liveBvars[i] );
  ABC_FREE( p->liveBvars );
  for ( i = 0; i < p->nVars + 2; i++ )
    Vec_PtrFreeFree( p->liveNodes[i] );
  ABC_FREE( p->liveNodes );
  ABC_FREE( p->pTable );
  ABC_FREE( p->pNextsTmp );
}

int Abc_BddReorder2( Abc_BddMan * p, Vec_Int_t * pFunctions, int nVerbose )
{
  //  Abc_BddP( p, pFunctions );
  int i, j, k;
  int b;
  int best_i;
  Abc_BddNode * x;
  int fOutOfNodes = 0;
  for ( i = 0; i < p->nVars + 2; i++ )
    Vec_IntShrink( p->liveBvars[i], 0 );
  Abc_BddCountEdgeAndBvar( p, pFunctions );
  for ( j = 0; j < p->nVars; j++ )
    Vec_IntForEachEntry( p->liveBvars[j], b, k )
      {
	if ( k < Vec_PtrSize( p->liveNodes[j] ) )
	  x = Vec_PtrEntry( p->liveNodes[j], k );
	else
	  {
	    x = ABC_ALLOC( Abc_BddNode, 1 );
	    Vec_PtrPush( p->liveNodes[j], x );
	  }
	x->Bvar = b;
	x->Then = Abc_BddThenOfBvar( p, b );
	x->Else = Abc_BddElseOfBvar( p, b );
	x->Edge = Abc_BddEdgeOfBvar( p, b );
      }
  for ( j = 0; j < p->nVars; j++ )
    Vec_PtrShrink( p->liveNodes[j], Vec_IntSize( p->liveBvars[j] ) );
  int * new2old = ABC_CALLOC( int, p->nVars );
  for ( i = 0; i < p->nVars; i++ ) new2old[i] = i;
  int * descendingOrder = ABC_CALLOC( int, p->nVars );
  for ( i = 0; i < p->nVars; i++ ) descendingOrder[i] = i;
  for ( i = 0; i < p->nVars - 1; i++ )
    {
      best_i = i;
      for ( j = i + 1; j < p->nVars; j++ )
	if ( Vec_PtrSize( p->liveNodes[descendingOrder[j]] ) > Vec_PtrSize( p->liveNodes[descendingOrder[best_i]] ) )
	  best_i = j;
      ABC_SWAP( int, descendingOrder[i], descendingOrder[best_i] );
    }
  if ( nVerbose )
    {
      printf( "num_nodes : " );
      for ( i = 0; i < p->nVars; i++ ) printf( "%d,", Vec_PtrSize( p->liveNodes[i] ) );
      printf( "\n" );
      printf( "index (descending order) : " );
      for ( i = 0; i < p->nVars; i++ ) printf( "%d,", descendingOrder[i] );
      printf( "\n" );
    }
  for ( i = 0; i < p->nVars; i++ )
    {
      int pos = -1;
      int curPos;
      int diff = 0;
      int bestPos;
      int bestDiff;
      int goUp = 0;
      int distance;
      for ( j = 0; j < p->nVars; j++ )
	if ( new2old[j] == descendingOrder[i] )
	  {
	    pos = j;
	    break;
	  }
      assert( pos >= 0 );
      curPos = pos;
      bestPos = pos;
      bestDiff = diff;
      if( pos < p->nVars >> 1 )
	{
	  goUp ^= 1;
	  distance = pos;
	}
      else distance = p->nVars - pos - 1;
      if ( nVerbose )
	{
	  printf( "###############################\n" );
	  printf( "# begin shift %d (%d/%d)\n", descendingOrder[i], i + 1, p->nVars );
	  printf( "###############################\n" );
	  printf( "%d goes %s by %d\n", descendingOrder[i], goUp? "up": "down", distance );
	}
      fOutOfNodes = Abc_BddSimulateShift( p, pos, distance, goUp, &bestPos, &bestDiff, nVerbose > 1 );
      if ( fOutOfNodes ) break;
      goUp ^= 1;
      distance = p->nVars - distance - 1;
      if ( nVerbose )
	printf( "%d goes %s by %d\n", descendingOrder[i], goUp? "up": "down", distance );
      fOutOfNodes = Abc_BddSimulateShift( p, pos, distance, goUp, &bestPos, &bestDiff, nVerbose > 1 );
      if ( fOutOfNodes ) break;
      if ( pos > bestPos )
	{
	  distance = pos - bestPos;
	  goUp = 1;
	}
      else
	{
	  distance = bestPos - pos;
	  goUp = 0;
	}
      if ( nVerbose )
	{
	  printf( "best position %d, gain %d\n", bestPos, bestDiff );
	  printf( "%d goes %s by %d\n", descendingOrder[i], goUp? "up": "down", distance );
        }
      int r = Abc_BddShift( p, &curPos, &diff, distance, goUp, &bestPos, &bestDiff, new2old, nVerbose > 1 );
      assert( !r );
      for ( j = 0; j < p->nVars; j++ )
	Vec_IntForEachEntry( p->liveBvars[j], b, k )
	  {
	    if ( ( goUp && curPos <= j && j <= pos ) || ( !goUp && curPos >= j && j >= pos ) )
	      {
		if ( k < Vec_PtrSize( p->liveNodes[j] ) )
		  x = Vec_PtrEntry( p->liveNodes[j], k );
		else
		  {
		    x = ABC_ALLOC( Abc_BddNode, 1 );
		    Vec_PtrPush( p->liveNodes[j], x );
		  }
		x->Bvar = b;
		x->Then = Abc_BddThenOfBvar( p, b );
		x->Else = Abc_BddElseOfBvar( p, b );
	      }
	    else
	      x = Vec_PtrEntry( p->liveNodes[j], k );
	    x->Edge = Abc_BddEdgeOfBvar( p, b );
	  }
      for ( j = 0; j < p->nVars; j++ )
	if ( ( goUp && curPos <= j && j <= pos ) || ( !goUp && curPos >= j && j >= pos ) )
	  Vec_PtrShrink( p->liveNodes[j], Vec_IntSize( p->liveBvars[j] ) );
      if ( nVerbose )
	{
	  printf( "###############################\n" );
	  printf( "# end shift %d (%d/%d)\n", descendingOrder[i], i + 1, p->nVars );
	  printf( "###############################\n" );
	}
      if ( fOutOfNodes ) break;
    }
  Abc_BddUncountEdge( p, pFunctions );
  ABC_FREE( new2old );
  ABC_FREE( descendingOrder );
  //  printf( "###############################\n" );  
  //  Abc_BddP( p, pFunctions );
  return fOutOfNodes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

