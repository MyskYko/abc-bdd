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
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddCountEdge_rec( Abc_BddMan * p, unsigned x )
{
  if ( Abc_BddLitIsConst( x ) )
    return;
  Abc_BddIncEdge( p, x );
  if ( Abc_BddMark( p, x ) )
    return;
  Abc_BddSetMark( p, x, 1 );
  Abc_BddCountEdge_rec( p, Abc_BddElse( p, x ) );
  Abc_BddCountEdge_rec( p, Abc_BddThen( p, x ) );
}
static inline void Abc_BddCountEdge( Abc_BddMan * p, Vec_Int_t * pFunctions )
{
  int i;
  unsigned x;
  Vec_IntForEachEntry( pFunctions, x, i )
    Abc_BddCountEdge_rec( p, x );
  Vec_IntForEachEntry( pFunctions, x, i )
    Abc_BddUnmark_rec( p, x );
}
void Abc_BddUncountEdge_rec( Abc_BddMan * p, unsigned x )
{
  if ( Abc_BddLitIsConst( x ) )
    return;
  Abc_BddDecEdge( p, x );
  if ( Abc_BddMark( p, x ) )
    return;
  Abc_BddSetMark( p, x, 1 );
  Abc_BddUncountEdge_rec( p, Abc_BddElse( p, x ) );
  Abc_BddUncountEdge_rec( p, Abc_BddThen( p, x ) );
}
static inline void Abc_BddUncountEdge( Abc_BddMan * p, Vec_Int_t * pFunctions )
{
  int i;
  unsigned x;
  Vec_IntForEachEntry( pFunctions, x, i )
    Abc_BddUncountEdge_rec( p, x );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddUncountEdge_rec( p, Abc_BddLitIthVar( i ) );
  Vec_IntForEachEntry( pFunctions, x, i )
    Abc_BddUnmark_rec( p, x );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddUnmark_rec( p, Abc_BddLitIthVar( i ) );
}

void Abc_BddCountEdgeAndBvar_rec( Abc_BddMan * p, unsigned x )
{
  if ( Abc_BddLitIsConst( x ) )
    return;
  Abc_BddIncEdge( p, x );
  if ( Abc_BddMark( p, x ) )
    return;
  Vec_IntPush( p->liveBvars[Abc_BddVar( p, x )], Abc_BddLit2Bvar( x ) );
  Abc_BddSetMark( p, x, 1 );
  Abc_BddCountEdgeAndBvar_rec( p, Abc_BddElse( p, x ) );
  Abc_BddCountEdgeAndBvar_rec( p, Abc_BddThen( p, x ) );
}
static inline void Abc_BddCountEdgeAndBvar( Abc_BddMan * p, Vec_Int_t * pFunctions )
{
  int i;
  unsigned x;
  Vec_IntForEachEntry( pFunctions, x, i )
    Abc_BddCountEdgeAndBvar_rec( p, x );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddCountEdgeAndBvar_rec( p, Abc_BddLitIthVar( i ) );
  Vec_IntForEachEntry( pFunctions, x, i )
    Abc_BddUnmark_rec( p, x );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddUnmark_rec( p, Abc_BddLitIthVar( i ) );
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline void Abc_BddPrintOrdering( Abc_BddMan * p )
{
  int i, j;
  printf( "Ordering :\n" );
  for ( i = 0; i < p->nVars; i++ )
    {
      for ( j = 0; j < p->nVars; j++ )
	if ( Abc_BddVar( p, Abc_BddLitIthVar( j ) ) == i )
	  break;
      printf( "%d,", j );
    }
  printf( "\n" );
  printf( "----------\n" );
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline void Abc_BddShiftBvar( Abc_BddMan * p, int a, int d )
{
  int Var;
  int * q, * next;
  unsigned hash, Then, Else;
  Var = Abc_BddVarOfBvar( p, a );
  Then = Abc_BddThenOfBvar( p, a );
  Else = Abc_BddElseOfBvar( p, a );
  next = p->pNexts + a;
  // remove
  hash = Abc_BddHash( Var, Then, Else ) & p->nUniqueMask;
  q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == a )
      {
	*q = *next;
	break;
      }
  // change
  Var += d;
  Abc_BddSetVarOfBvar( p, a, Var );
  // register
  hash = Abc_BddHash( Var, Then, Else ) & p->nUniqueMask;
  q = p->pUnique + hash;
  *next = *q;
  *q = a;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline int Abc_BddSwapBvar( Abc_BddMan * p, int a, int fRestore )
{
  int Var;
  int * q, * next;
  unsigned hash, Then, Else, f00, f01, f10, f11, newThen, newElse;
  Var = Abc_BddVarOfBvar( p, a );
  Then = Abc_BddThenOfBvar( p, a );
  Else = Abc_BddElseOfBvar( p, a );
  next = p->pNexts + a;
  // new chlidren
  if ( Abc_BddVar( p, Then ) == Var || Abc_BddVar( p, Then ) == Var + 1 )
    {
      f11 = Abc_BddThen( p, Then );
      f10 = Abc_BddElse( p, Then );
    }
  else
    {
      f11 = Then;
      f10 = Then;
    }
  if ( Abc_BddVar( p, Else ) == Var || Abc_BddVar( p, Else ) == Var + 1 )
    {
      f01 = Abc_BddThen( p, Else );
      f00 = Abc_BddElse( p, Else );
    }
  else
    {
      f01 = Else;
      f00 = Else;
    }
  newThen = Abc_BddUniqueCreate( p, Var + 1, f11, f01 );
  if ( Abc_BddLitIsInvalid( newThen ) )
    return 1;
  newElse = Abc_BddUniqueCreate( p, Var + 1, f10, f00 );
  if ( Abc_BddLitIsInvalid( newElse ) )
    return 1;
  if ( !Abc_BddEdge( p, newThen ) && Abc_BddVar( p, newThen ) == Var + 1 )
    {
      if ( !fRestore )
	Vec_IntPush( p->liveBvars[p->nVars + 1], Abc_BddLit2Bvar( newThen ) );
      Abc_BddIncEdgeNonConst( p, f11 );
      Abc_BddIncEdgeNonConst( p, f01 );
    }
  Abc_BddIncEdgeNonConst( p, newThen );
  if ( !Abc_BddEdge( p, newElse ) && Abc_BddVar( p, newElse ) == Var + 1 )
    {
      if ( !fRestore )
	Vec_IntPush( p->liveBvars[p->nVars + 1], Abc_BddLit2Bvar( newElse ) );
      Abc_BddIncEdgeNonConst( p, f10 );
      Abc_BddIncEdgeNonConst( p, f00 );
    }
  Abc_BddIncEdgeNonConst( p, newElse );
  // remove
  hash = Abc_BddHash( Var, Then, Else ) & p->nUniqueMask;
  q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == a )
      {
	*q = *next;
	break;
      }
  // change
  Abc_BddSetThenOfBvar( p, a, newThen );
  Abc_BddSetElseOfBvar( p, a, newElse );
  // register
  hash = Abc_BddHash( Var, newThen, newElse ) & p->nUniqueMask;
  q = p->pUnique + hash;
  *next = *q;
  *q = a;
  return 0;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
// swap v-th variable and (v+1)-th variable
static inline int Abc_BddSwap( Abc_BddMan * p, int v, int * nNodes, int dLimit )
{
  int i, a, nSwapHead, nOut, fOutOfNodes, fOutOfLimit;
  unsigned Then, Else;
  Vec_Int_t * tmpBvars;
  Vec_IntShrink( p->liveBvars[p->nVars], 0 );
  Vec_IntShrink( p->liveBvars[p->nVars + 1], 0 );
  // walk upper level
  Vec_IntForEachEntry( p->liveBvars[v], a, i )
    if ( Abc_BddVar( p, Abc_BddThenOfBvar( p, a ) ) == v + 1 ||
	 Abc_BddVar( p, Abc_BddElseOfBvar( p, a ) ) == v + 1 )
      {
	Abc_BddDecEdgeNonConst( p, Abc_BddThenOfBvar( p, a ) );
	Abc_BddDecEdgeNonConst( p, Abc_BddElseOfBvar( p, a ) );
      }
    else
      {
	Abc_BddShiftBvar( p, a, 1 );
	Vec_IntPush( p->liveBvars[p->nVars + 1], a );
      }
  // walk lower level
  Vec_IntForEachEntry( p->liveBvars[v + 1], a, i )
    if ( !Abc_BddEdgeOfBvar( p, a ) )
      {
	Abc_BddDecEdgeNonConst( p, Abc_BddThenOfBvar( p, a ) );
	Abc_BddDecEdgeNonConst( p, Abc_BddElseOfBvar( p, a ) );
      }
    else
      {
	Abc_BddShiftBvar( p, a, -1 );
	Vec_IntPush( p->liveBvars[p->nVars], a );
      }
  nSwapHead = Vec_IntSize( p->liveBvars[p->nVars] );
  fOutOfNodes = 0;
  fOutOfLimit = 0;
  // walk upper level again
  Vec_IntForEachEntry( p->liveBvars[v], a, i )
    if ( Abc_BddVarOfBvar( p, a ) == v )
      {
	if ( Abc_BddSwapBvar( p, a, 0 ) )
	  {
	    nOut = i;
	    fOutOfNodes = 1;
	    break;
	  }
	Vec_IntPush( p->liveBvars[p->nVars], a );
	if ( Vec_IntSize( p->liveBvars[p->nVars] )
	     + Vec_IntSize( p->liveBvars[p->nVars + 1] )
	     - Vec_IntSize( p->liveBvars[v] )
	     - Vec_IntSize( p->liveBvars[v + 1] )
	     > dLimit )
	  {
	    nOut = i + 1;
	    fOutOfLimit = 1;
	    break;
	  }
      }
  if ( !fOutOfNodes && !fOutOfLimit )
    {
      // swap liveBvars
      *nNodes += Vec_IntSize( p->liveBvars[p->nVars] ) + Vec_IntSize( p->liveBvars[p->nVars + 1] ) - Vec_IntSize( p->liveBvars[v] ) - Vec_IntSize( p->liveBvars[v + 1] );
      tmpBvars = p->liveBvars[v];
      p->liveBvars[v] = p->liveBvars[p->nVars];
      p->liveBvars[p->nVars] = tmpBvars;
      tmpBvars = p->liveBvars[v + 1];
      p->liveBvars[v + 1] = p->liveBvars[p->nVars + 1];
      p->liveBvars[p->nVars + 1] = tmpBvars;
      return 0;
    }
  // restore previous tree
  // walk new upper level where swapped
  Vec_IntForEachEntryStart( p->liveBvars[p->nVars], a, i, nSwapHead )
    {
      Abc_BddDecEdgeNonConst( p, Abc_BddThenOfBvar( p, a ) );
      Abc_BddDecEdgeNonConst( p, Abc_BddElseOfBvar( p, a ) );
    }
  // walk new lower level
  Vec_IntForEachEntry( p->liveBvars[p->nVars + 1 ], a, i )
    if ( !Abc_BddEdgeOfBvar( p, a ) )
      {
	Abc_BddDecEdgeNonConst( p, Abc_BddThenOfBvar( p, a ) );
	Abc_BddDecEdgeNonConst( p, Abc_BddElseOfBvar( p, a ) );
      }
    else
      Abc_BddShiftBvar( p, a, -1 );
  // walk new upper level where shifted
  Vec_IntForEachEntry( p->liveBvars[p->nVars], a, i )
    {
      if ( i == nSwapHead )
	break;
      Abc_BddShiftBvar( p, a, 1 );
    }
  // walk upper level from where out of nodes
  Vec_IntForEachEntryStart( p->liveBvars[v], a, i, nOut )
    if ( Abc_BddVar( p, Abc_BddThenOfBvar( p, a ) ) == v + 1 ||
	 Abc_BddVar( p, Abc_BddElseOfBvar( p, a ) ) == v + 1 )
      {
        Then = Abc_BddThenOfBvar( p, a );
	Else = Abc_BddElseOfBvar( p, a );
	if ( !Abc_BddEdge( p, Then ) && Abc_BddVar( p, Then ) == v + 1 )
	  {
	    Abc_BddIncEdgeNonConst( p, Abc_BddThen( p, Then ) );
	    Abc_BddIncEdgeNonConst( p, Abc_BddElse( p, Then ) );
	  }
	Abc_BddIncEdgeNonConst( p, Then );
	if ( !Abc_BddEdge( p, Else ) && Abc_BddVar( p, Else ) == v + 1 )
	  {
	    Abc_BddIncEdgeNonConst( p, Abc_BddThen( p, Else ) );
	    Abc_BddIncEdgeNonConst( p, Abc_BddElse( p, Else ) );
	  }
	Abc_BddIncEdgeNonConst( p, Else );
      }
  // walk new upper level where swapped
  Vec_IntForEachEntryStart( p->liveBvars[p->nVars], a, i, nSwapHead )
    assert( !Abc_BddSwapBvar( p, a, 1 ) );
  if ( fOutOfNodes )
    return -1;
  return 1; // if ( fOutOfLimit );
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline void Abc_BddShift( Abc_BddMan * p, int * pos, int * nNodes, int nSwap, int fUp, int * bestPos, int * nBestNodes, int * new2old, Vec_Int_t * pFunctions, int nLimit )
{
  int i, r, dLimit, fRefresh;
  fRefresh = 0;
  for ( i = 0; i < nSwap; i++ )
    {
      dLimit = nLimit - *nNodes;
      if ( fUp )
	*pos -= 1;
      r = Abc_BddSwap( p, *pos, nNodes, dLimit );
      if ( r == 1 )
	{
	  if ( fUp )
	    *pos += 1;
	  return;
	}
      if ( r == -1 )
	{
	  if ( fUp )
	    *pos += 1;
	  if ( p->fGC && !fRefresh )
	    {
	      Abc_BddGarbageCollect( p, pFunctions );
	      fRefresh = 1;
	    }
	  else if ( p->fRealloc )
	    Abc_BddManRealloc( p );
	  else
	    {
	      printf("Error: Number of nodes exceeds the limit during reordering\n");
	      abort();
	    }
	  i--;
	  continue;
	}
      fRefresh = 0;
      ABC_SWAP( int, new2old[*pos], new2old[*pos + 1] );
      if ( !fUp )
	*pos += 1;
      if ( *nNodes <= *nBestNodes )
	{
	  *nBestNodes = *nNodes;
	  *bestPos = *pos;
	}
      if ( p->nVerbose >= 2 )
	{
	  printf( "pos : %d\nnNode : %d\n", *pos, *nNodes );
          Abc_BddPrintOrdering( p );
	}
    }
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddReorder( Abc_BddMan * p, Vec_Int_t * pFunctions )
{
  int i, j, k, best_i, pos, nNodes, nSwap, fUp, bestPos, nBestNodes, nLimit;
  int * new2old, * descendingOrder;
  if ( p->nVerbose )
    printf( "\tReordering\n" );
  // initialize
  new2old = ABC_CALLOC( int, p->nVars );
  descendingOrder = ABC_CALLOC( int, p->nVars );
  for ( i = 0; i < p->nVars + 2; i++ )
    Vec_IntClear( p->liveBvars[i] );
  Abc_BddCountEdgeAndBvar( p, pFunctions );
  for ( i = 0; i < p->nVars; i++ )
    {
      new2old[i] = i;
      descendingOrder[i] = i;
    }
  for ( i = 0; i < p->nVars - 1; i++ )
    {
      best_i = i;
      for ( j = i + 1; j < p->nVars; j++ )
	if ( Vec_IntSize( p->liveBvars[descendingOrder[j]] ) > Vec_IntSize( p->liveBvars[descendingOrder[best_i]] ) )
	  best_i = j;
      ABC_SWAP( int, descendingOrder[i], descendingOrder[best_i] );
    }
  nNodes = 0;
  for ( i = 0; i < p->nVars; i++ )
    nNodes += Vec_IntSize( p->liveBvars[i] );
  if ( p->nVerbose  >= 2 )
    {
      printf( "nNode for each level :\n" );
      for ( i = 0; i < p->nVars; i++ )
	printf( "(%d),", Vec_IntSize( p->liveBvars[i] ) );
      printf( "\n" );
      Abc_BddPrintOrdering( p );
    }
  // shift
  for ( i = 0; i < p->nVars; i++ )
    {
      pos = -1;
      fUp = 0;
      nLimit = nNodes * p->ReoThold + nNodes;
      for ( j = 0; j < p->nVars; j++ )
	if ( new2old[j] == descendingOrder[i] )
	  {
	    pos = j;
	    break;
	  }
      bestPos = pos;
      nBestNodes = nNodes;
      if ( p->nVerbose >= 2 )
	{
	  for ( k = 0; k < p->nVars; k++ )
	    if ( Abc_BddVar( p, Abc_BddLitIthVar( k ) ) == j )
	      break;
	  printf( "\tBegin shift %d (%d/%d)\n", k, i + 1, p->nVars );
	}
      if( pos < p->nVars >> 1 )
	{
	  fUp ^= 1;
	  nSwap = pos;
	}
      else nSwap = p->nVars - pos - 1;
      Abc_BddShift( p, &pos, &nNodes, nSwap, fUp, &bestPos, &nBestNodes, new2old, pFunctions, nLimit );
      fUp ^= 1;
      if ( fUp ) nSwap = pos;
      else nSwap = p->nVars - pos - 1;
      Abc_BddShift( p, &pos, &nNodes, nSwap, fUp, &bestPos, &nBestNodes, new2old, pFunctions, nLimit );
      if ( pos < bestPos )
	{
	  fUp = 0;
	  nSwap = bestPos - pos;
	}
      else
	{
	  fUp = 1;
	  nSwap = pos - bestPos;
	}
      Abc_BddShift( p, &pos, &nNodes, nSwap, fUp, &bestPos, &nBestNodes, new2old, pFunctions, nLimit );
    }
  // finish
  Abc_BddUncountEdge( p, pFunctions );
  ABC_FREE( new2old );
  ABC_FREE( descendingOrder );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

