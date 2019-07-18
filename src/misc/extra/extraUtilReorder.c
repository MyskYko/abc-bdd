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
static inline void Abc_BddIncEdgeNonConst( Abc_BddMan * p, unsigned i) { if ( !Abc_BddLitIsConst( i ) ) Abc_BddIncEdge( p, i ); }
static inline void Abc_BddDecEdgeNonConst( Abc_BddMan * p, unsigned i) { if ( !Abc_BddLitIsConst( i ) ) Abc_BddDecEdge( p, i ); }

void Abc_BddCountEdge_rec( Abc_BddMan * p, unsigned i )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  Abc_BddIncEdge( p, i );
  if ( Abc_BddMark( p, i ) ) return;
  Abc_BddSetMark( p, i, 1 );
  Abc_BddCountEdge_rec( p, Abc_BddElse( p, i ) );
  Abc_BddCountEdge_rec( p, Abc_BddThen( p, i ) );
}
void Abc_BddUncountEdge_rec( Abc_BddMan * p, unsigned i ) // for verification
{
  if ( Abc_BddLitIsConst( i ) ) return;
  Abc_BddDecEdge( p, i );
  if ( Abc_BddMark( p, i ) ) return;
  Abc_BddSetMark( p, i, 1 );
  Abc_BddUncountEdge_rec( p, Abc_BddElse( p, i ) );
  Abc_BddUncountEdge_rec( p, Abc_BddThen( p, i ) );
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

void Abc_BddCountEdgeAndBvar_rec( Abc_BddMan * p, unsigned i, Vec_Int_t ** liveBvars )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  Abc_BddIncEdge( p, i );
  if ( Abc_BddMark( p, i ) ) return;
  Vec_IntPush( liveBvars[Abc_BddVar( p, i )], Abc_BddLit2Bvar( i ) );
  Abc_BddSetMark( p, i, 1 );
  Abc_BddCountEdgeAndBvar_rec( p, Abc_BddElse( p, i ), liveBvars );
  Abc_BddCountEdgeAndBvar_rec( p, Abc_BddThen( p, i ), liveBvars );
}
static inline void Abc_BddCountEdgeAndBvar( Abc_BddMan * p, Vec_Int_t * pFunctions, Vec_Int_t ** liveBvars )
{
  int i;
  unsigned a;
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddCountEdgeAndBvar_rec( p, a, liveBvars );
  for ( i = 0; i < p->nVars; i++ )
    Abc_BddCountEdgeAndBvar_rec( p, Abc_BddLitIthVar( i ), liveBvars );
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
static inline void Abc_BddShiftBvar( Abc_BddMan * p, int i, int d )
{
  int Var = p->pVars[i];
  unsigned Then = p->pObjs[(unsigned)i + i];
  unsigned Else = p->pObjs[(unsigned)i + i + 1];
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
  Var = p->pVars[i] = p->pVars[i] + d;
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
static inline int Abc_BddSwapBvar4( Abc_BddMan * p, Vec_Int_t ** liveBvars, int i )
{
  int Var = p->pVars[i];
  unsigned Then = p->pObjs[(unsigned)i + i];
  unsigned Else = p->pObjs[(unsigned)i + i + 1];
  unsigned hash;
  int * q;
  int *next = p->pNexts + i;
  unsigned f00, f01, f10, f11, newThen, newElse;
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
      Vec_IntPush( liveBvars[p->nVars + 1], Abc_BddLit2Bvar( newThen ) );
      Abc_BddIncEdgeNonConst( p, f11 );
      Abc_BddIncEdgeNonConst( p, f01 );
    }
  Abc_BddIncEdgeNonConst( p, newThen );
  if ( !Abc_BddEdge( p, newElse ) && Abc_BddVar( p, newElse ) == Var + 1 )
    {
      Vec_IntPush( liveBvars[p->nVars + 1], Abc_BddLit2Bvar( newElse ) );
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
  p->pObjs[(unsigned)i + i] = newThen;
  p->pObjs[(unsigned)i + i + 1] = newElse;
  // register
  hash = Abc_BddHash( Var, newThen, newElse ) & p->nUniqueMask;
  q = p->pUnique + hash;
  *next = *q;
  *q = i;
  return 0;
}
static inline void Abc_BddSwapBvar5( Abc_BddMan * p, int i )
{
  int Var = p->pVars[i];
  unsigned Then = p->pObjs[(unsigned)i + i];
  unsigned Else = p->pObjs[(unsigned)i + i + 1];
  unsigned hash;
  int * q;
  int *next = p->pNexts + i;
  unsigned f00, f01, f10, f11, newThen, newElse;
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
  p->pObjs[(unsigned)i + i] = newThen;
  p->pObjs[(unsigned)i + i + 1] = newElse;
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
static inline int Abc_BddSwap4( Abc_BddMan * p, Vec_Int_t ** liveBvars, int x, int * diff )
{
  int i, j, tmp0, tmp1;
  int fOutOfNodes = 0;
  int b;
  unsigned a;
  liveBvars[p->nVars] = Vec_IntAlloc( Vec_IntSize( liveBvars[x] ) ); // new layer x
  liveBvars[p->nVars + 1] = Vec_IntAlloc( Vec_IntSize( liveBvars[x + 1] ) ); // new layer x + 1
  // walk upper level
  Vec_IntForEachEntry( liveBvars[x], b, i )
    {
      a = Abc_BddBvar2Lit( b, 0 );
      if ( Abc_BddVar( p, Abc_BddThen( p, a ) ) == x + 1 ||
	   Abc_BddVar( p, Abc_BddElse( p, a ) ) == x + 1 )
	{
	  Abc_BddDecEdgeNonConst( p, Abc_BddThen( p, a ) );
	  Abc_BddDecEdgeNonConst( p, Abc_BddElse( p, a ) );
	}
      else
	{
	  Abc_BddShiftBvar( p, b, 1 );
	  Vec_IntPush( liveBvars[p->nVars + 1], b );
	}
    }
  // walk lower level
  Vec_IntForEachEntry( liveBvars[x + 1], b, i )
    {
      a = Abc_BddBvar2Lit( b, 0 );
      if ( !Abc_BddEdge( p, a ) )
	{
	  Abc_BddDecEdgeNonConst( p, Abc_BddThen( p, a ) );
	  Abc_BddDecEdgeNonConst( p, Abc_BddElse( p, a ) );
	}
      else
	{
	  Abc_BddShiftBvar( p, b, -1 );
	  Vec_IntPush( liveBvars[p->nVars], b );
	}
    }
  tmp0 = Vec_IntSize( liveBvars[p->nVars] );
  // walk upper level again
  Vec_IntForEachEntry( liveBvars[x], b, i )
    {
      if ( p->pVars[b] == x )
	{
	  if ( Abc_BddSwapBvar4( p, liveBvars, b ) )
	    {
	      fOutOfNodes = 1;
	      break;
	    }
	  Vec_IntPush( liveBvars[p->nVars], b );
	}
    }
  if ( !fOutOfNodes )
    {
      // swap liveBvars
      *diff += Vec_IntSize( liveBvars[p->nVars] ) + Vec_IntSize( liveBvars[p->nVars + 1] ) - Vec_IntSize( liveBvars[x] ) - Vec_IntSize( liveBvars[x + 1] );
      Vec_IntFree( liveBvars[x] );
      Vec_IntFree( liveBvars[x + 1] );
      liveBvars[x] = liveBvars[p->nVars];
      liveBvars[x + 1] = liveBvars[p->nVars + 1];
      return 0;
    }
  tmp1 = i;
  // restore previous tree
  // walk new upper level where swapped
  Vec_IntForEachEntryStart( liveBvars[p->nVars], b, i, tmp0 )
    {
      a = Abc_BddBvar2Lit( b, 0 );
      Abc_BddDecEdgeNonConst( p, Abc_BddThen( p, a ) );
      Abc_BddDecEdgeNonConst( p, Abc_BddElse( p, a ) );
    }
  // walk new lower level
  Vec_IntForEachEntry( liveBvars[p->nVars + 1 ], b, i )
    {
      a = Abc_BddBvar2Lit( b, 0 );
      if ( !Abc_BddEdge( p, a ) )
	{
	  Abc_BddDecEdgeNonConst( p, Abc_BddThen( p, a ) );
	  Abc_BddDecEdgeNonConst( p, Abc_BddElse( p, a ) );
	}
      else
	Abc_BddShiftBvar( p, b, -1 );
    }
  // walk new upper level where shifted
  Vec_IntForEachEntry( liveBvars[p->nVars], b, i )
    {
      if ( i == tmp0 ) break;
      Abc_BddShiftBvar( p, b, 1 );
    }
  // walk upper level from where out of nodes
  Vec_IntForEachEntryStart( liveBvars[x], b, j, tmp1 )
    {
      a = Abc_BddBvar2Lit( b, 0 );
      if ( Abc_BddVar( p, Abc_BddThen( p, a ) ) == x + 1 ||
	   Abc_BddVar( p, Abc_BddElse( p, a ) ) == x + 1 )
	{
	  unsigned Then = Abc_BddThen( p, a );
	  unsigned Else = Abc_BddElse( p, a );
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
    }
  // walk new upper level where swapped
  Vec_IntForEachEntryStart( liveBvars[p->nVars], b, i, tmp0 )
    Abc_BddSwapBvar5( p, b );
  Vec_IntFree( liveBvars[p->nVars] );
  Vec_IntFree( liveBvars[p->nVars+1] );
  return 1;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline int Abc_BddShift( Abc_BddMan * p, Vec_Int_t ** liveBvars, int * pos, int * diff, int distance, int fUp, int * bestPos, int * bestDiff, int * new2old, int fVerbose )
{
  int j;
  for ( j = 0; j < distance; j++ )
    {
      if ( fUp ) *pos -= 1;
      if ( Abc_BddSwap4( p, liveBvars, *pos, diff ) )
	{
	  if ( fUp ) *pos += 1;
	  return 1;
	}
      ABC_SWAP( int, new2old[*pos], new2old[*pos + 1] );
      if ( !fUp ) *pos += 1;
      if ( *diff < *bestDiff )
	{
	  *bestDiff = *diff;
	  *bestPos = *pos;
	}
      if ( fVerbose )
	{
	  int k;
	  for ( k = 0; k < p->nVars; k++ )
	    printf( "%d,", new2old[k] );
	  printf("  current position %d  gain %d\n", *pos, *diff);
	}
    }
  return 0;
}
int Abc_BddReorder( Abc_BddMan * p, Vec_Int_t * pFunctions, int nVerbose )
{
  int i, j, best_i;
  int totalDiff = 0;
  Vec_Int_t ** liveBvars = ABC_CALLOC( Vec_Int_t *, p->nVars + 2);
  for ( i = 0; i < p->nVars; i++ )
    liveBvars[i] = Vec_IntAlloc( p->nObjs / p->nVars + p->nObjs % p->nVars );
  p->pEdges = ABC_CALLOC( unsigned, p->nObjsAlloc );
  Abc_BddCountEdgeAndBvar( p, pFunctions, liveBvars );
  int * new2old = ABC_CALLOC( int, p->nVars );
  for ( i = 0; i < p->nVars; i++ ) new2old[i] = i;
  int * descendingOrder = ABC_CALLOC( int, p->nVars );
  for ( i = 0; i < p->nVars; i++ ) descendingOrder[i] = i;
  for ( i = 0; i < p->nVars - 1; i++ )
    {
      best_i = i;
      for ( j = i + 1; j < p->nVars; j++ )
	if ( Vec_IntSize( liveBvars[descendingOrder[j]] ) > Vec_IntSize( liveBvars[descendingOrder[best_i]] ) )
	  best_i = j;
      ABC_SWAP( int, descendingOrder[i], descendingOrder[best_i] );
    }
  if ( nVerbose )
    {
      printf( "num_nodes : " );
      for ( i = 0; i < p->nVars; i++ ) printf( "%d,", Vec_IntSize( liveBvars[i] ) );
      printf( "\n" );
      printf( "index (descending order) : " );
      for ( i = 0; i < p->nVars; i++ ) printf( "%d,", descendingOrder[i] );
      printf( "\n" );
    }

  for ( i = 0; i < p->nVars; i++ )
    {
      int pos = -1;
      for ( j = 0; j < p->nVars; j++ )
	if ( new2old[j] == descendingOrder[i] )
	  {
	    pos = j;
	    break;
	  }
      assert( pos >= 0 );
      int diff = 0;
      int bestPos = pos;
      int bestDiff = 0;
      int goUp = 0;
      int distance;
      int fOutOfNodes = 0;
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
      fOutOfNodes = Abc_BddShift( p, liveBvars, &pos, &diff, distance, goUp, &bestPos, &bestDiff, new2old, nVerbose > 1 );
      if ( !fOutOfNodes )
	{
	  goUp ^= 1;
	  distance = p->nVars - 1;
	  if ( nVerbose )
	    printf( "%d goes %s by %d\n", descendingOrder[i], goUp? "up": "down", distance );
	  fOutOfNodes = Abc_BddShift( p, liveBvars, &pos, &diff, distance, goUp, &bestPos, &bestDiff, new2old, nVerbose > 1 );
	}
      goUp ^= 1;
      if ( goUp ) distance = pos - bestPos;
      else distance = bestPos - pos;
      if ( nVerbose )
	{
	  printf( "best position %d, gain %d\n", bestPos, bestDiff );
	  printf( "%d goes %s by %d\n", descendingOrder[i], goUp? "up": "down", distance );
        }
      int r = Abc_BddShift( p, liveBvars, &pos, &diff, distance, goUp, &bestPos, &bestDiff, new2old, nVerbose > 1 );
      assert( !r );
      totalDiff += bestDiff;
      if ( nVerbose )
	{
	  printf( "###############################\n" );
	  printf( "# end shift %d (%d/%d)\n", descendingOrder[i], i + 1, p->nVars );
	  printf( "###############################\n" );
	}
      if ( fOutOfNodes ) break;
    }
  //Abc_BddUncountEdge( p, pFunctions ); // for debugging
  ABC_FREE( p->pEdges );
  ABC_FREE( new2old );
  ABC_FREE( descendingOrder );
  for ( i = 0; i < p->nVars; i++ )
    Vec_IntFree( liveBvars[i] );
  ABC_FREE( liveBvars );
  return totalDiff;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

