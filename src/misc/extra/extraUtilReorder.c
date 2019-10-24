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

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddCountEdge_rec( Abc_BddMan * p, unsigned i )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  Abc_BddIncEdge( p, i );
  if ( Abc_BddMark( p, i ) ) return;
  Abc_BddSetMark( p, i, 1 );
  Abc_BddCountEdge_rec( p, Abc_BddElse( p, i ) );
  Abc_BddCountEdge_rec( p, Abc_BddThen( p, i ) );
}
static inline void Abc_BddCountEdge( Abc_BddMan * p, Vec_Int_t * pFunctions )
{
  int i;
  unsigned a;
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddCountEdge_rec( p, a );
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddUnmark_rec( p, a );
}
void Abc_BddUncountEdge_rec( Abc_BddMan * p, unsigned i )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  Abc_BddDecEdge( p, i );
  if ( Abc_BddMark( p, i ) ) return;
  Abc_BddSetMark( p, i, 1 );
  Abc_BddUncountEdge_rec( p, Abc_BddElse( p, i ) );
  Abc_BddUncountEdge_rec( p, Abc_BddThen( p, i ) );
}
static inline void Abc_BddUncountEdge( Abc_BddMan * p, Vec_Int_t * pFunctions )
{
  int i;
  unsigned a;
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddUncountEdge_rec( p, a );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddUncountEdge_rec( p, Abc_BddLitIthVar( i ) );
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddUnmark_rec( p, a );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddUnmark_rec( p, Abc_BddLitIthVar( i ) );
}

void Abc_BddCountEdgeAndBvar_rec( Abc_BddMan * p, unsigned i )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  Abc_BddIncEdge( p, i );
  if ( Abc_BddMark( p, i ) ) return;
  Vec_IntPush( p->liveBvars[Abc_BddVar( p, i )], Abc_BddLit2Bvar( i ) );
  Abc_BddSetMark( p, i, 1 );
  Abc_BddCountEdgeAndBvar_rec( p, Abc_BddElse( p, i ) );
  Abc_BddCountEdgeAndBvar_rec( p, Abc_BddThen( p, i ) );
}
static inline void Abc_BddCountEdgeAndBvar( Abc_BddMan * p, Vec_Int_t * pFunctions )
{
  int i;
  unsigned a;
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddCountEdgeAndBvar_rec( p, a );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddCountEdgeAndBvar_rec( p, Abc_BddLitIthVar( i ) );
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
void Abc_BddShiftBvar( Abc_BddMan * p, int i, int d )
{
  int Var = Abc_BddVarOfBvar( p, i );
  unsigned Then = Abc_BddThenOfBvar( p, i );
  unsigned Else = Abc_BddElseOfBvar( p, i );
  unsigned hash;
  int * q;
  int * next = p->pNexts + i;
  // remove
  hash = Abc_BddHash( Var, Then, Else ) & p->nUniqueMask;
  q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == i )
      {
	*q = *next;
	break;
      }
  // change
  Var += d;
  Abc_BddSetVarOfBvar( p, i, Var );
  // register
  hash = Abc_BddHash( Var, Then, Else ) & p->nUniqueMask;
  q = p->pUnique + hash;
  *next = *q;
  *q = i;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline int Abc_BddSwapBvar( Abc_BddMan * p, int i )
{
  int * q, * next;
  unsigned hash;
  unsigned f00, f01, f10, f11, newThen, newElse;
  int Var = Abc_BddVarOfBvar( p, i );
  unsigned Then = Abc_BddThenOfBvar( p, i );
  unsigned Else = Abc_BddElseOfBvar( p, i );
  next = p->pNexts + i;
  // new chlidren
  if ( Abc_BddVar( p, Then ) == Var || Abc_BddVar( p, Then ) == Var + 1 )
    f11 = Abc_BddThen( p, Then ), f10 = Abc_BddElse( p, Then );
  else
    f11 = f10 = Then;
  if ( Abc_BddVar( p, Else ) == Var || Abc_BddVar( p, Else ) == Var + 1)
    f01 = Abc_BddThen( p, Else ), f00 = Abc_BddElse( p, Else );
  else
    f01 = f00 = Else;
  newThen = Abc_BddUniqueCreate( p, Var + 1, f11, f01 );
  if ( Abc_BddLitIsInvalid( newThen ) ) return 1;
  newElse = Abc_BddUniqueCreate( p, Var + 1, f10, f00 );
  if ( Abc_BddLitIsInvalid( newElse ) ) return 1;
  if ( !Abc_BddEdge( p, newThen ) && Abc_BddVar( p, newThen ) == Var + 1 )
    {
      Vec_IntPush( p->liveBvars[p->nVars + 1], Abc_BddLit2Bvar( newThen ) );
      Abc_BddIncEdgeNonConst( p, f11 );
      Abc_BddIncEdgeNonConst( p, f01 );
    }
  Abc_BddIncEdgeNonConst( p, newThen );
  if ( !Abc_BddEdge( p, newElse ) && Abc_BddVar( p, newElse ) == Var + 1 )
    {
      Vec_IntPush( p->liveBvars[p->nVars + 1], Abc_BddLit2Bvar( newElse ) );
      Abc_BddIncEdgeNonConst( p, f10 );
      Abc_BddIncEdgeNonConst( p, f00 );
    }
  Abc_BddIncEdgeNonConst( p, newElse );
  // remove
  hash = Abc_BddHash( Var, Then, Else ) & p->nUniqueMask;
  q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == i )
      {
	*q = *next;
	break;
      }
  // change
  Abc_BddSetThenOfBvar( p, i, newThen );
  Abc_BddSetElseOfBvar( p, i, newElse );
  // register
  hash = Abc_BddHash( Var, newThen, newElse ) & p->nUniqueMask;
  q = p->pUnique + hash;
  *next = *q;
  *q = i;
  return 0;
}
static inline void Abc_BddSwapBvarRestore( Abc_BddMan * p, int i )
{
  int * q, * next;
  unsigned hash;
  int Var = Abc_BddVarOfBvar( p, i );
  unsigned Then = Abc_BddThenOfBvar( p, i );
  unsigned Else = Abc_BddElseOfBvar( p, i );
  unsigned f00, f01, f10, f11, newThen, newElse;
  next = p->pNexts + i;
  // new chlidren
  if ( Abc_BddVar( p, Then ) == Var || Abc_BddVar( p, Then ) == Var + 1 )
    f11 = Abc_BddThen( p, Then ), f10 = Abc_BddElse( p, Then );
  else
    f11 = f10 = Then;
  if ( Abc_BddVar( p, Else ) == Var || Abc_BddVar( p, Else ) == Var + 1)
    f01 = Abc_BddThen( p, Else ), f00 = Abc_BddElse( p, Else );
  else
    f01 = f00 = Else;
  newThen = Abc_BddUniqueCreate( p, Var + 1, f11, f01 );
  assert( !Abc_BddLitIsInvalid( newThen ) );
  newElse = Abc_BddUniqueCreate( p, Var + 1, f10, f00 );
  assert( !Abc_BddLitIsInvalid( newElse ) );
  if ( !Abc_BddEdge( p, newThen ) && Abc_BddVar( p, newThen ) == Var + 1 )
    Abc_BddIncEdgeNonConst( p, f11 ), Abc_BddIncEdgeNonConst( p, f01 );
  Abc_BddIncEdgeNonConst( p, newThen );
  if ( !Abc_BddEdge( p, newElse ) && Abc_BddVar( p, newElse ) == Var + 1 )
    Abc_BddIncEdgeNonConst( p, f10 ), Abc_BddIncEdgeNonConst( p, f00 );
  Abc_BddIncEdgeNonConst( p, newElse );
  // remove
  hash = Abc_BddHash( Var, Then, Else ) & p->nUniqueMask;
  q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == i )
      {
	*q = *next;
	break;
      }
  // change
  Abc_BddSetThenOfBvar( p, i, newThen );
  Abc_BddSetElseOfBvar( p, i, newElse );
  // register
  hash = Abc_BddHash( Var, newThen, newElse ) & p->nUniqueMask;
  q = p->pUnique + hash;
  *next = *q;
  *q = i;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
// swap x-th variable and (x+1)-th variable
static inline int Abc_BddSwap( Abc_BddMan * p, int x, int * nNode, int nLimit )
{
  int i, j, tmp0, tmp1;
  int fOutOfNodes = 0, fOutOfLimit = 0;
  int b;
  int nDec, nInc, nTmp;
  Vec_IntShrink( p->liveBvars[p->nVars], 0 );
  Vec_IntShrink( p->liveBvars[p->nVars + 1], 0 );
  // walk upper level
  Vec_IntForEachEntry( p->liveBvars[x], b, i )
    if ( Abc_BddVar( p, Abc_BddThenOfBvar( p, b ) ) == x + 1 ||
	 Abc_BddVar( p, Abc_BddElseOfBvar( p, b ) ) == x + 1 )
      {
	Abc_BddDecEdgeNonConst( p, Abc_BddThenOfBvar( p, b ) );
	Abc_BddDecEdgeNonConst( p, Abc_BddElseOfBvar( p, b ) );
      }
    else
      {
	Abc_BddShiftBvar( p, b, 1 );
	Vec_IntPush( p->liveBvars[p->nVars + 1], b );
      }
  // walk lower level
  Vec_IntForEachEntry( p->liveBvars[x + 1], b, i )
    if ( !Abc_BddEdgeOfBvar( p, b ) )
      {
	Abc_BddDecEdgeNonConst( p, Abc_BddThenOfBvar( p, b ) );
	Abc_BddDecEdgeNonConst( p, Abc_BddElseOfBvar( p, b ) );
      }
    else
      {
	Abc_BddShiftBvar( p, b, -1 );
	Vec_IntPush( p->liveBvars[p->nVars], b );
      }
  nDec = Vec_IntSize( p->liveBvars[x + 1] ) - Vec_IntSize( p->liveBvars[p->nVars] );
  nTmp = Vec_IntSize( p->liveBvars[p->nVars + 1] );
  tmp0 = Vec_IntSize( p->liveBvars[p->nVars] );
  // walk upper level again
  Vec_IntForEachEntry( p->liveBvars[x], b, i )
    if ( Abc_BddVarOfBvar( p, b ) == x )
      {
	if ( Abc_BddSwapBvar( p, b ) )
	  {
	    tmp1 = i;
	    fOutOfNodes = 1;
	    break;
	  }
	Vec_IntPush( p->liveBvars[p->nVars], b );
	nInc = Vec_IntSize( p->liveBvars[p->nVars + 1] ) - nTmp;
	if ( nInc - nDec > nLimit )
	  {
	    tmp1 = i + 1;
	    fOutOfLimit = 1;
	    break;
	  }
      }
  if ( !fOutOfNodes && !fOutOfLimit )
    {
      /*
      // remove non-used nodes
      Vec_IntForEachEntry( p->liveBvars[x + 1], b, i )
      if ( !Abc_BddEdgeOfBvar( p, b ) )
      Abc_BddRemoveNodeByBvar( p, b );
      */
      // swap liveBvars
      *nNode += Vec_IntSize( p->liveBvars[p->nVars] ) + Vec_IntSize( p->liveBvars[p->nVars + 1] ) - Vec_IntSize( p->liveBvars[x] ) - Vec_IntSize( p->liveBvars[x + 1] );
      Vec_Int_t * tmp;
      tmp = p->liveBvars[x];
      p->liveBvars[x] = p->liveBvars[p->nVars];
      p->liveBvars[p->nVars] = tmp;
      tmp = p->liveBvars[x + 1];
      p->liveBvars[x + 1] = p->liveBvars[p->nVars + 1];
      p->liveBvars[p->nVars + 1] = tmp;
      return 0;
    }
  // restore previous tree
  // walk new upper level where swapped
  Vec_IntForEachEntryStart( p->liveBvars[p->nVars], b, i, tmp0 )
    {
      Abc_BddDecEdgeNonConst( p, Abc_BddThenOfBvar( p, b ) );
      Abc_BddDecEdgeNonConst( p, Abc_BddElseOfBvar( p, b ) );
    }
  // walk new lower level
  Vec_IntForEachEntry( p->liveBvars[p->nVars + 1 ], b, i )
    if ( !Abc_BddEdgeOfBvar( p, b ) )
      {
	Abc_BddDecEdgeNonConst( p, Abc_BddThenOfBvar( p, b ) );
	Abc_BddDecEdgeNonConst( p, Abc_BddElseOfBvar( p, b ) );
      }
    else
      Abc_BddShiftBvar( p, b, -1 );
  // walk new upper level where shifted
  Vec_IntForEachEntry( p->liveBvars[p->nVars], b, i )
    {
      if ( i == tmp0 ) break;
      Abc_BddShiftBvar( p, b, 1 );
    }
  // walk upper level from where out of nodes
  Vec_IntForEachEntryStart( p->liveBvars[x], b, j, tmp1 )
    if ( Abc_BddVar( p, Abc_BddThenOfBvar( p, b ) ) == x + 1 ||
	 Abc_BddVar( p, Abc_BddElseOfBvar( p, b ) ) == x + 1 )
      {
	unsigned Then = Abc_BddThenOfBvar( p, b );
	unsigned Else = Abc_BddElseOfBvar( p, b );
	if ( !Abc_BddEdge( p, Then ) && Abc_BddVar( p, Then ) == x + 1 )
	  {
	    Abc_BddIncEdgeNonConst( p, Abc_BddThen( p, Then ) );
	    Abc_BddIncEdgeNonConst( p, Abc_BddElse( p, Then ) );
	  }
	Abc_BddIncEdgeNonConst( p, Then );
	if ( !Abc_BddEdge( p, Else ) && Abc_BddVar( p, Else ) == x + 1 )
	  {
	    Abc_BddIncEdgeNonConst( p, Abc_BddThen( p, Else ) );
	    Abc_BddIncEdgeNonConst( p, Abc_BddElse( p, Else ) );
	  }
	Abc_BddIncEdgeNonConst( p, Else );
      }
  // walk new upper level where swapped
  Vec_IntForEachEntryStart( p->liveBvars[p->nVars], b, i, tmp0 )
    Abc_BddSwapBvarRestore( p, b );
  /*
  // remove non-used nodes
  Vec_IntForEachEntry( p->liveBvars[p->nVars + 1], b, i )
  if ( !Abc_BddEdgeOfBvar( p, b ) )
  Abc_BddRemoveNodeByBvar( p, b );
  */
  if ( fOutOfNodes ) return -1;
  return 1; // if ( fOutOfLimit );
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline int Abc_BddShift( Abc_BddMan * p, int * pos, int * nNode, int distance, int fUp, int * bestPos, int * bestNode, int * new2old, int nVerbose , Vec_Int_t * pFrontiers, int fNoLimit )
{
  int j;
  int fRefresh = 0;
  for ( j = 0; j < distance; j++ )
    {
      int nLimit = *nNode * p->ReoThold;
      if ( fNoLimit ) nLimit = 0x0fffffff;
      if ( fUp ) *pos -= 1;
      int r = Abc_BddSwap( p, *pos, nNode, nLimit );
      if ( r == 1 )
	{
	  if ( fUp ) *pos += 1;
	  return 1;
	}
      if ( r == -1 )
	{
	  //assert( !fNoLimit || !fRefresh );
	  if ( !p->fGC ) return -1;
	  if ( fUp ) *pos += 1;
	  if ( !fRefresh )
	    {
	      Abc_BddGarbageCollect( p, pFrontiers );
	      fRefresh = 1;
	    }
	  else
	    {
	      if ( !p->fRealloc ) return -1;
	      if ( Abc_BddManRealloc( p ) ) return -1;
	      fRefresh = 0;
	    }
	  j--;
	  continue;
	}
      fRefresh = 0;
      ABC_SWAP( int, new2old[*pos], new2old[*pos + 1] );
      if ( !fUp ) *pos += 1;
      if ( *nNode <= *bestNode )
	{
	  *bestNode = *nNode;
	  *bestPos = *pos;
	}
      if ( nVerbose > 1 )
	{
	  int k;
	  printf("\n");
	  for ( k = 0; k < p->nVars; k++ )
	    printf( "%d,", new2old[k] );
	  printf("  current position %d  node %d\n", *pos, *nNode);
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
int Abc_BddReorder( Abc_BddMan * p, Vec_Int_t * pFunctions, int nVerbose )
{
  if ( nVerbose < 0 ) nVerbose = 0;
  int i, j, best_i;
  for ( i = 0; i < p->nVars + 2; i++ )
    Vec_IntShrink( p->liveBvars[i], 0 );
  Abc_BddCountEdgeAndBvar( p, pFunctions );
  int * new2old = ABC_CALLOC( int, p->nVars );
  for ( i = 0; i < p->nVars; i++ ) new2old[i] = i;
  int * descendingOrder = ABC_CALLOC( int, p->nVars );
  for ( i = 0; i < p->nVars; i++ ) descendingOrder[i] = i;
  for ( i = 0; i < p->nVars - 1; i++ )
    {
      best_i = i;
      for ( j = i + 1; j < p->nVars; j++ )
	if ( Vec_IntSize( p->liveBvars[descendingOrder[j]] ) > Vec_IntSize( p->liveBvars[descendingOrder[best_i]] ) )
	  best_i = j;
      ABC_SWAP( int, descendingOrder[i], descendingOrder[best_i] );
    }
  int nNode = 0;
  for ( i = 0; i < p->nVars; i++ ) nNode += Vec_IntSize( p->liveBvars[i] );
  if ( nVerbose )
    {
      printf( "num_nodes : " );
      for ( i = 0; i < p->nVars; i++ ) printf( "%d,", Vec_IntSize( p->liveBvars[i] ) );
      printf( "\n" );
      printf( "index (descending order) : " );
      for ( i = 0; i < p->nVars; i++ ) printf( "%d,", descendingOrder[i] );
      printf( "\n" );
    }

  for ( i = 0; i < p->nVars; i++ )
    {
      int pos = -1;
      int bestPos;
      int bestNode;
      int goUp = 0;
      int distance;
      for ( j = 0; j < p->nVars; j++ )
	if ( new2old[j] == descendingOrder[i] )
	  {
	    pos = j;
	    break;
	  }
      assert( pos >= 0 );
      bestPos = pos;
      bestNode = nNode;
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
	  printf( "\t%d goes %s by %d\n", descendingOrder[i], goUp? "up": "down", distance );
	}
      int fOutOfNodes;
      fOutOfNodes = Abc_BddShift( p, &pos, &nNode, distance, goUp, &bestPos, &bestNode, new2old, nVerbose, pFunctions, 0 );
      if ( fOutOfNodes == -1 ) return -1;
      goUp ^= 1;
      if ( goUp ) distance = pos;
      else distance = p->nVars - pos - 1;
      if ( nVerbose )
	printf( "\n\t%d goes %s by %d\n", descendingOrder[i], goUp? "up": "down", distance );
      fOutOfNodes = Abc_BddShift( p, &pos, &nNode, distance, goUp, &bestPos, &bestNode, new2old, nVerbose, pFunctions, 0 );
      if ( fOutOfNodes == -1 ) return -1;
      if ( pos < bestPos )
	{
	  goUp = 0;
	  distance = bestPos - pos;
	}
      else
	{
	  goUp = 1;
	  distance = pos - bestPos;
	}
      if ( nVerbose )
	{
	  printf( "\n\tbest position %d, nNode %d\n", bestPos, bestNode );
	  printf( "\t%d goes %s by %d\n", descendingOrder[i], goUp? "up": "down", distance );
        }
      fOutOfNodes = Abc_BddShift( p, &pos, &nNode, distance, goUp, &bestPos, &bestNode, new2old, nVerbose , pFunctions, 1 );
      if ( fOutOfNodes == -1 ) return -1;
      assert( pos == bestPos );
      if ( nVerbose )
	{
	  printf( "\n" );	  
	  printf( "###############################\n" );
	  printf( "# end shift %d (%d/%d)\n", descendingOrder[i], i + 1, p->nVars );
	  printf( "###############################\n" );
	}
    }
  Abc_BddUncountEdge( p, pFunctions );
  ABC_FREE( new2old );
  ABC_FREE( descendingOrder );
  return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

