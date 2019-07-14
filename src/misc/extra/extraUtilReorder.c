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
static inline void Abc_BddShiftBvar( Abc_BddMan * p, int i, int d )
{
  // remove
  unsigned hash = Abc_BddHash( (int)p->pVars[i], p->pObjs[(unsigned)i + i], p->pObjs[(unsigned)i + i + 1] ) & p->nUniqueMask;
  int *q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == i ) break;
  int *q_next = p->pNexts + *q; // == p->pNexts + i
  *q = *q_next;
  // change
  p->pVars[i] += d;
  // register
  hash = Abc_BddHash( (int)p->pVars[i], p->pObjs[(unsigned)i + i], p->pObjs[(unsigned)i + i + 1] ) & p->nUniqueMask;
  q = p->pUnique + hash;
  *q_next = *q;
  *q = i;
}
static inline void Abc_BddSwapBvar( Abc_BddMan * p, int i )
{
  // remove
  unsigned hash = Abc_BddHash( (int)p->pVars[i], p->pObjs[(unsigned)i + i], p->pObjs[(unsigned)i + i + 1] ) & p->nUniqueMask;
  int *q = p->pUnique + hash;
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == i ) break;
  int *q_next = p->pNexts + *q; // == p->pNexts + i
  *q = *q_next;
  // new chlidren
  int x = p->pVars[i];
  unsigned f00, f01, f10, f11;
  assert( Abc_BddVar( p, p->pObjs[(unsigned)i + i] ) != x + 1 );
  if ( Abc_BddVar( p, p->pObjs[(unsigned)i + i] ) == x )
    f11 = Abc_BddThen( p, p->pObjs[(unsigned)i + i] ),
      f10 = Abc_BddElse( p, p->pObjs[(unsigned)i + i] );
  else
    f11 = f10 = p->pObjs[(unsigned)i + i];
  if ( Abc_BddVar( p, p->pObjs[(unsigned)i + i + 1] ) == x )
    f01 = Abc_BddThen( p, p->pObjs[(unsigned)i + i + 1] ),
      f00 = Abc_BddElse( p, p->pObjs[(unsigned)i + i + 1] );
  else
    f01 = f00 = p->pObjs[(unsigned)i + i + 1];
  unsigned Then = Abc_BddUniqueCreate( p, x + 1, f11, f01 );
  unsigned Else = Abc_BddUniqueCreate( p, x + 1, f10, f00 );
  // change
  p->pObjs[(unsigned)i + i] = Then;
  p->pObjs[(unsigned)i + i + 1] = Else;
  // register
  hash = Abc_BddHash( (int)p->pVars[i], p->pObjs[(unsigned)i + i], p->pObjs[(unsigned)i + i + 1] ) & p->nUniqueMask;
  q = p->pUnique + hash;
  *q_next = *q;
  *q = i;
}
// swap x-th variable and (x+1)-th variable
void Abc_BddSwap( Abc_BddMan * p, int x )
{
  int i;
  int bvar;
  Vec_Int_t * pXthNodes = Vec_IntAlloc( 1 );
  for ( i = 1; i < p->nObjs; i++ )
    {
      if ( (int)p->pVars[i] == x + 1 )
	{
	  Abc_BddShiftBvar( p, i, -1 );
	}
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
    Abc_BddSwapBvar( p, bvar );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

