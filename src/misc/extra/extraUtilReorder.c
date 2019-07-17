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
void Abc_BddIncEdgeNonConst( Abc_BddMan * p, unsigned i)
{
  if ( Abc_BddLitIsConst( i ) ) return;
  //  printf("inc i %d\n", i);
  Abc_BddIncEdge( p, i );
}
void Abc_BddDecEdgeNonConst( Abc_BddMan * p, unsigned i)
{
  if ( Abc_BddLitIsConst( i ) ) return;
  //  printf("dec i %d\n", i);
  Abc_BddDecEdge( p, i );
}

void Abc_BddCountEdge_rec( Abc_BddMan * p, unsigned i )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  //  printf("inc i %d\n", i);
  Abc_BddIncEdge( p, i );
  if ( Abc_BddMark( p, i ) ) return;
  Abc_BddSetMark( p, i, 1 );
  Abc_BddCountEdge_rec( p, Abc_BddElse( p, i ) );
  Abc_BddCountEdge_rec( p, Abc_BddThen( p, i ) );
}
void Abc_BddUncountEdge_rec( Abc_BddMan * p, unsigned i ) // for verification
{
  if ( Abc_BddLitIsConst( i ) ) return;
  //  printf("dec i %d\n", i);
  Abc_BddDecEdge( p, i );
  if ( Abc_BddMark( p, i ) ) return;
  Abc_BddSetMark( p, i, 1 );
  Abc_BddUncountEdge_rec( p, Abc_BddElse( p, i ) );
  Abc_BddUncountEdge_rec( p, Abc_BddThen( p, i ) );
}

void Abc_BddCountEdge( Abc_BddMan * p, Vec_Int_t * pFunctions )
{
  int i;
  unsigned a;
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddCountEdge_rec( p, a );
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddUnmark_rec( p, a );
}
void Abc_BddUncountEdge( Abc_BddMan * p, Vec_Int_t * pFunctions )
{
  int i;
  unsigned a;
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddUncountEdge_rec( p, a );
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddUnmark_rec( p, a );
}

void Abc_BddCountEdgeAndNode_rec( Abc_BddMan * p, unsigned i, Vec_Int_t ** liveNodes )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  //  printf("inc i %d\n", i);
  Abc_BddIncEdge( p, i );
  if ( Abc_BddMark( p, i ) ) return;
  Vec_IntPush( liveNodes[Abc_BddVar( p, i )], i );
  Abc_BddSetMark( p, i, 1 );
  Abc_BddCountEdgeAndNode_rec( p, Abc_BddElse( p, i ), liveNodes );
  Abc_BddCountEdgeAndNode_rec( p, Abc_BddThen( p, i ), liveNodes );
}

void Abc_BddCountEdgeAndNode( Abc_BddMan * p, Vec_Int_t * pFunctions, Vec_Int_t ** liveNodes )
{
  int i;
  unsigned a;
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddCountEdgeAndNode_rec( p, a, liveNodes );
  Vec_IntForEachEntry( pFunctions, a, i )
    Abc_BddUnmark_rec( p, a );
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
  int * q, * head;
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
  // register (overwrite. remove non-used node)
  hash = Abc_BddHash( Var, Then, Else ) & p->nUniqueMask;
  head = q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( (int)p->pVars[*q] == Var && p->pObjs[(unsigned)*q + *q] == Then && p->pObjs[(unsigned)*q + *q + 1] == Else )
      {
	*next = *(p->pNexts + *q);
	*(p->pNexts + *q) = 0;
	*q = i;
	return;
      }
  *next = *head;
  *head = i;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline void Abc_BddSwapBvar3( Abc_BddMan * p, int i, int * nNew, int * nRemoved )
{
  int Var = p->pVars[i];
  unsigned Then = p->pObjs[(unsigned)i + i];
  unsigned Else = p->pObjs[(unsigned)i + i + 1];
  unsigned hash;
  int * q, * head;
  int *next = p->pNexts + i;
  unsigned f00, f01, f10, f11, n0, n1;
  // remove
  hash = Abc_BddHash( Var, Then, Else ) & p->nUniqueMask;
  q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == i )
      {
	*q = *next;
	break;
      }
  // new chlidren
  assert( Abc_BddVar( p, Then ) != Var + 1 );
  Abc_BddDecEdgeNonConst( p, Then );
  if ( Abc_BddVar( p, Then ) == Var )
    {
      f11 = Abc_BddThen( p, Then );
      f10 = Abc_BddElse( p, Then );
      if ( !Abc_BddEdge( p, Then ) )
	{
	  *nRemoved += 1;
	  Abc_BddDecEdgeNonConst( p, f11 );
	  Abc_BddDecEdgeNonConst( p, f10 );
	}
    }
  else
    f11 = f10 = Then;
  assert( Abc_BddVar( p, Else ) != Var + 1 );
  Abc_BddDecEdgeNonConst( p, Else );
  if ( Abc_BddVar( p, Else ) == Var )
    {
      f01 = Abc_BddThen( p, Else );
      f00 = Abc_BddElse( p, Else );
      if ( !Abc_BddEdge( p, Else ) )
	{
	  *nRemoved += 1;
	  Abc_BddDecEdgeNonConst( p, f01 );
	  Abc_BddDecEdgeNonConst( p, f00 );
	}
    }
  else
    f01 = f00 = Else;
  n1 = Abc_BddUniqueCreate( p, Var + 1, f11, f01 );
  n0 = Abc_BddUniqueCreate( p, Var + 1, f10, f00 );
  if ( !Abc_BddEdge( p, n1 ) && Abc_BddVar( p, n1 ) == Var + 1 )
    {
      *nNew += 1;
      Abc_BddIncEdgeNonConst( p, f11 );
      Abc_BddIncEdgeNonConst( p, f01 );
    }
  Abc_BddIncEdgeNonConst( p, n1 );
  if ( !Abc_BddEdge( p, n0 ) && Abc_BddVar( p, n0 ) == Var + 1 )
    {
      *nNew += 1;
      Abc_BddIncEdgeNonConst( p, f10 );
      Abc_BddIncEdgeNonConst( p, f00 );
    }
  Abc_BddIncEdgeNonConst( p, n0 );
  // change
  p->pObjs[(unsigned)i + i] = n1;
  p->pObjs[(unsigned)i + i + 1] = n0;
  // register
  hash = Abc_BddHash( Var, n1, n0 ) & p->nUniqueMask;
  head = q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( (int)p->pVars[*q] == Var && p->pObjs[(unsigned)*q + *q] == n1 && p->pObjs[(unsigned)*q + *q + 1] == n0 )
      {
	*next = *(p->pNexts + *q);
	*(p->pNexts + *q) = 0;
	*q = i;
	return;
      }
  *next = *head;
  *head = i;
}
// swap x-th variable and (x+1)-th variable
int Abc_BddSwap3( Abc_BddMan * p, Vec_Int_t ** liveNodes, int x )
{
  // TODO : Hashtable
  int i, bvar, nNew = 0, nRemoved = 0;
  Vec_Int_t * pXthNodes = Vec_IntAlloc( 1 );
  for ( i = 1; i < p->nObjs; i++ )
    {
      if ( !p->pEdges[i] ) continue;
      if ( (int)p->pVars[i] == x + 1 )
	Abc_BddShiftBvar( p, i, -1 );
      else if ( (int)p->pVars[i] == x )
	{
	  if ( Abc_BddVar( p, p->pObjs[(unsigned)i + i]     ) == x     ||
	       Abc_BddVar( p, p->pObjs[(unsigned)i + i]     ) == x + 1 ||
	       Abc_BddVar( p, p->pObjs[(unsigned)i + i + 1] ) == x     ||
	       Abc_BddVar( p, p->pObjs[(unsigned)i + i + 1] ) == x + 1 )
	    Vec_IntPush( pXthNodes, i );
	  else
	    Abc_BddShiftBvar( p, i, 1 );
	}
    }
  Vec_IntForEachEntry( pXthNodes, bvar, i )
    Abc_BddSwapBvar3( p, bvar, &nNew, &nRemoved );
  //  printf( "diff = %d  new = %d  removed = %d\n", nNew - nRemoved, nNew, nRemoved );
  Vec_IntFree( pXthNodes );
  return nNew - nRemoved;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline void Abc_BddSwapBvar4( Abc_BddMan * p, Vec_Int_t ** liveNodes, int i, int * nNew, int * nRemoved )
{
  int Var = p->pVars[i];
  unsigned Then = p->pObjs[(unsigned)i + i];
  unsigned Else = p->pObjs[(unsigned)i + i + 1];
  unsigned hash;
  int * q, * head;
  int *next = p->pNexts + i;
  unsigned f00, f01, f10, f11, n0, n1;
  // remove
  hash = Abc_BddHash( Var, Then, Else ) & p->nUniqueMask;
  q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == i )
      {
	*q = *next;
	break;
      }
  // new chlidren
  if ( Abc_BddVar( p, Then ) == Var || Abc_BddVar( p, Then ) == Var + 1 )
    {
      f11 = Abc_BddThen( p, Then );
      f10 = Abc_BddElse( p, Then );
    }
  else
    f11 = f10 = Then;
  if ( Abc_BddVar( p, Else ) == Var || Abc_BddVar( p, Else ) == Var + 1)
    {
      f01 = Abc_BddThen( p, Else );
      f00 = Abc_BddElse( p, Else );
    }
  else
    f01 = f00 = Else;
  n1 = Abc_BddUniqueCreate( p, Var + 1, f11, f01 );
  n0 = Abc_BddUniqueCreate( p, Var + 1, f10, f00 );
  if ( !Abc_BddEdge( p, n1 ) && Abc_BddVar( p, n1 ) == Var + 1 )
    {
      *nNew += 1;
      Vec_IntPush( liveNodes[p->nVars + 1], n1 );
      Abc_BddIncEdgeNonConst( p, f11 );
      Abc_BddIncEdgeNonConst( p, f01 );
    }
  Abc_BddIncEdgeNonConst( p, n1 );
  if ( !Abc_BddEdge( p, n0 ) && Abc_BddVar( p, n0 ) == Var + 1 )
    {
      *nNew += 1;
      Vec_IntPush( liveNodes[p->nVars + 1], n0 );
      Abc_BddIncEdgeNonConst( p, f10 );
      Abc_BddIncEdgeNonConst( p, f00 );
    }
  Abc_BddIncEdgeNonConst( p, n0 );
  // change
  p->pObjs[(unsigned)i + i] = n1;
  p->pObjs[(unsigned)i + i + 1] = n0;
  // register
  hash = Abc_BddHash( Var, n1, n0 ) & p->nUniqueMask;
  head = q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( (int)p->pVars[*q] == Var && p->pObjs[(unsigned)*q + *q] == n1 && p->pObjs[(unsigned)*q + *q + 1] == n0 )
      {
	*next = *(p->pNexts + *q);
	*(p->pNexts + *q) = 0;
	*q = i;
	return;
      }
  *next = *head;
  *head = i;
}
// swap x-th variable and (x+1)-th variable
int Abc_BddSwap4( Abc_BddMan * p, Vec_Int_t ** liveNodes, int x )
{
  liveNodes[p->nVars    ] = Vec_IntAlloc( Vec_IntSize( liveNodes[x    ] ) ); // new layer x
  liveNodes[p->nVars + 1] = Vec_IntAlloc( Vec_IntSize( liveNodes[x + 1] ) ); // new layer x + 1
  // TODO : Hashtable
  int i, nNew = 0, nRemoved = 0;
  unsigned a;
  // walk upper level
  Vec_IntForEachEntry( liveNodes[x], a, i )
    {
      if ( Abc_BddVar( p, Abc_BddThen( p, a ) ) == x + 1 ||
	   Abc_BddVar( p, Abc_BddElse( p, a ) ) == x + 1 )
	{
	  Abc_BddDecEdgeNonConst( p, Abc_BddThen( p, a ) );
	  Abc_BddDecEdgeNonConst( p, Abc_BddElse( p, a ) );
	}
      else
	{
	  Abc_BddShiftBvar( p, Abc_BddLit2Bvar( a ), 1 );
	  Vec_IntPush( liveNodes[p->nVars + 1], a );
	}
    }
  // walk lower level
  Vec_IntForEachEntry( liveNodes[x + 1], a, i )
    {
      if ( !Abc_BddEdge( p, a ) )
	{
	  Abc_BddDecEdgeNonConst( p, Abc_BddThen( p, a ) );
	  Abc_BddDecEdgeNonConst( p, Abc_BddElse( p, a ) );
	  nRemoved++;
	}
      else
	{
	  Abc_BddShiftBvar( p, Abc_BddLit2Bvar( a ), -1 );
	  Vec_IntPush( liveNodes[p->nVars], a );
	}
    }
  // walk upper level again
  Vec_IntForEachEntryReverse( liveNodes[x], a, i )
    if ( Abc_BddVar( p, a ) == x )
      {
	Abc_BddSwapBvar4( p, liveNodes, Abc_BddLit2Bvar( a ), &nNew, &nRemoved );
	Vec_IntPush( liveNodes[p->nVars], a );
      }
  // swap liveNodes
  Vec_IntFree( liveNodes[x] );
  Vec_IntFree( liveNodes[x + 1] );
  liveNodes[x] = liveNodes[p->nVars];
  liveNodes[x + 1] = liveNodes[p->nVars + 1];
  //  printf( "diff = %d  new = %d  removed = %d\n", nNew - nRemoved, nNew, nRemoved );
  return nNew - nRemoved;
}

/**Function*************************************************************
   
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline void Abc_BddShift( Abc_BddMan * p, Vec_Int_t ** liveNodes, int * pos, int * diff, int distance, int fUp, int * bestPos, int * bestDiff, int * new2old, int fVerbose )
{
  int j;
  for ( j = 0; j < distance; j++ )
    {
      if ( fUp ) *pos -= 1;
      //*diff += Abc_BddSwap3( p, liveNodes, *pos );
      *diff += Abc_BddSwap4( p, liveNodes, *pos );
      ABC_SWAP( int, new2old[*pos], new2old[*pos + 1] ); // for debugging
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
	    printf("%d,", new2old[k]); 
	  printf("  cur pos %d  diff %d\n", *pos, *diff);
	}
    }
}
int Abc_BddReorder( Abc_BddMan * p, Vec_Int_t * pFunctions, int nVerbose )
{
  int i, j, k, best_i;
  int totalDiff = 0;
  unsigned a;
  
  Vec_Int_t ** liveNodes = ABC_CALLOC( Vec_Int_t *, p->nVars + 2);
  for ( i = 0; i < p->nVars; i++ )
    liveNodes[i] = Vec_IntAlloc( p->nObjs / p->nVars + p->nObjs % p->nVars );
  p->pEdges = ABC_CALLOC( unsigned, p->nObjsAlloc );
  abctime clk = Abc_Clock();
  Abc_BddCountEdgeAndNode( p, pFunctions, liveNodes );
  abctime clk2 = Abc_Clock();
  ABC_PRT( "tree walk time", clk2 - clk );
  
  int * new2old = ABC_CALLOC( int, p->nVars );
  for ( i = 0; i < p->nVars; i++ ) new2old[i] = i;
    
  int * descendingOrder = ABC_CALLOC( int, p->nVars );
  for ( i = 0; i < p->nVars; i++ ) descendingOrder[i] = i;
  for ( i = 0; i < p->nVars - 1; i++ )
    {
      best_i = i;
      for ( j = i + 1; j < p->nVars; j++ )
	if ( Vec_IntSize( liveNodes[descendingOrder[j]] ) > Vec_IntSize( liveNodes[descendingOrder[best_i]] ) )
	  best_i = j;
      ABC_SWAP( int, descendingOrder[i], descendingOrder[best_i] );
    }

  if ( nVerbose )
    {
      printf( "num_nodes : " );
      for ( i = 0; i < p->nVars; i++ ) printf( "%d,", Vec_IntSize( liveNodes[i] ) );
      printf( "\n" );
      printf( "indices (descending order) : " );
      for ( i = 0; i < p->nVars; i++ ) printf( "%d,", descendingOrder[i] );
      printf( "\n" );
    }

  for ( i = 0; i < p->nVars; i++ )
    {
      int pos;
      for ( k = 0; k < p->nVars; k++ )
	if ( new2old[k] == descendingOrder[i] )
	  {
	    pos = k;
	    break;
	  }
      int diff = 0;
      int bestPos = pos;
      int bestDiff = 0;
      int goUp = 0;
      int distance;
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
      Abc_BddShift( p, liveNodes, &pos, &diff, distance, goUp, &bestPos, &bestDiff, new2old, nVerbose > 1 );
      goUp ^= 1;
      distance = p->nVars - 1;
      if ( nVerbose ) printf( "%d goes %s by %d\n", descendingOrder[i], goUp? "up": "down", distance );
      Abc_BddShift( p, liveNodes, &pos, &diff, distance, goUp, &bestPos, &bestDiff, new2old, nVerbose > 1 );
      goUp ^= 1;
      if ( goUp ) distance = p->nVars - bestPos - 1;
      else distance = bestPos;
      if ( nVerbose )
	{
	  printf( "bestPos %d, bestDiff %d\n", bestPos, bestDiff );
	  printf( "%d goes %s by %d\n", descendingOrder[i], goUp? "up": "down", distance );
	}
      Abc_BddShift( p, liveNodes, &pos, &diff, distance, goUp, &bestPos, &bestDiff, new2old, nVerbose > 1 );
      totalDiff += bestDiff;
      if ( nVerbose )
	{
	  printf( "###############################\n" );
	  printf( "# end shift %d (%d/%d)\n", descendingOrder[i], i + 1, p->nVars );
	  printf( "###############################\n" );
	}
    }
  Abc_BddUncountEdge( p, pFunctions ); // for debugging
  ABC_FREE( p->pEdges );
  ABC_FREE( descendingOrder );
  for ( i = 0; i < p->nVars; i++ )
    Vec_IntFree( liveNodes[i] );
  ABC_FREE( liveNodes );
  return totalDiff;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

