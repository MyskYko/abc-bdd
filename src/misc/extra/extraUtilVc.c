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

/*
bdd VectorCompose( bdd F,  bdd * Vars )
{
      if ( F == 0 )  return 0;
      if ( F == 1 )  return 1;
      if ( F is in computed table )   return Result;
      int Index = TopVar( F );
      bdd F0 = Cofactor0( F );
      bdd F1 = Cofactor1( F );
      bdd R0 = VectorCompose( F0, Vars );
      bdd R1 = VectorCompose( F1, Vars );
      bdd IndexFunc = Vars[Index];
      bdd Result = ITE( IndexFunc, R1, R0 );   // ITE( c, d1, d0 ) = (c & d1) | (!c & d0)
      add Result to computed table;
      return Result;
}
*/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

