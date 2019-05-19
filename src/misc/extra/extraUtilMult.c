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
#include "misc/vec/vec.h"
#include "aig/gia/gia.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define INVALID_LIT 0xffffffff
#define INVALID_MARK 0xff
#define CONST_VAR 0xff
#define REMOVED_VAR 0xff
#define MAX_NUM_FRONTIERS 10000

typedef struct Abc_BddMan_ Abc_BddMan;
struct Abc_BddMan_ 
{
  int                nVars;         // the number of variables
  unsigned           nObjs;         // the number of nodes used
  unsigned           nObjsAlloc;    // the number of nodes allocated
  int *              pUnique;       // unique table for nodes
  int *              pNexts;        // next pointer for nodes
  unsigned *         pCache;        // array of triples <arg0, arg1, AND(arg0, arg1)>
  unsigned *         pObjs;         // array of pairs cof0 for each node
  unsigned char *    pVars;         // array of variables for each node
  unsigned char *    pMark;         // array of marks for each BDD node
  unsigned           nUniqueMask;   // selection mask for unique table
  unsigned           nCacheMask;    // selection mask for computed table
  int                nCacheLookups; // the number of computed table lookups
  int                nCacheMisses;  // the number of computed table misses
  long long          nMemory;       // total amount of memory used (in bytes)
  unsigned           nRemoved;      // the minimum int of removed node
  int *              pFanouts;
  int                fVerbose;
};

static inline unsigned Abc_BddVar2Lit( int i, int c )                { return i + i + (int)( c > 0 );                               }
static inline int      Abc_BddLit2Var( unsigned i )                  { return i >> 1;                                               }
static inline unsigned Abc_BddLitRegular( unsigned i )               { return i & ~01;                                              }
static inline int      Abc_BddLitIsCompl( unsigned i )               { return i & 1;                                                }
static inline int      Abc_BddLitNot( unsigned i )                   { return i ^ 1;                                                }
static inline unsigned Abc_BddLitNotCond( unsigned i, int c )        { return i ^ (int)( c > 0 );                                   }

static inline unsigned Abc_BddIthVar( int i )                        { return Abc_BddVar2Lit( i + 1, 0 );                           }
static inline unsigned Abc_BddHash( int Arg0, int Arg1, int Arg2 )   { return 12582917 * Arg0 + 4256249 * Arg1 + 741457 * Arg2;     }

static inline int      Abc_BddVar( Abc_BddMan * p, unsigned i )      { return (int)p->pVars[Abc_BddLit2Var( i )];                   }
static inline unsigned Abc_BddThen( Abc_BddMan * p, unsigned i )     { return Abc_BddLitNotCond( p->pObjs[Abc_BddLitRegular( i )], Abc_BddLitIsCompl( i ) ); }
static inline unsigned Abc_BddElse( Abc_BddMan * p, unsigned i )     { return Abc_BddLitNotCond( p->pObjs[Abc_BddLitRegular( i ) + 1], Abc_BddLitIsCompl( i ) ); }

static inline int      Abc_BddMark( Abc_BddMan * p, unsigned i )     { return (int)p->pMark[Abc_BddLit2Var( i )];                   }
static inline void     Abc_BddSetMark( Abc_BddMan * p, unsigned i, int m ) { p->pMark[Abc_BddLit2Var( i )] = m;                     }
static inline void     Abc_BddIncMark( Abc_BddMan * p, unsigned i )  { assert( ++p->pMark[Abc_BddLit2Var( i )] != INVALID_MARK );   }
static inline void     Abc_BddDecMark( Abc_BddMan * p, unsigned i )  { assert( --p->pMark[Abc_BddLit2Var( i )] != INVALID_MARK );   }

static inline int      Abc_BddLitIsInvalid( unsigned i )             { return (int)( i == INVALID_LIT );                            }
static inline void     Abc_BddSetVarRemoved( Abc_BddMan * p, unsigned i ) { p->pVars[Abc_BddLit2Var( i )] = REMOVED_VAR;            }

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
  int *q = p->pUnique + ( Abc_BddHash( Var, Then, Else ) & p->nUniqueMask );
  for ( ; *q; q = p->pNexts + *q )
    if ( (int)p->pVars[*q] == Var && p->pObjs[(unsigned)*q + *q] == Then && p->pObjs[(unsigned)*q + *q + 1] == Else )
      return Abc_BddVar2Lit( *q, 0 );
  q = p->pUnique + ( Abc_BddHash( Var, Then, Else ) & p->nUniqueMask );
  int head = *q;
  if ( p->nObjs == p->nObjsAlloc - 1 )
    {
      for ( ; p->nRemoved < p->nObjs; p->nRemoved++ )
	if ( p->pVars[p->nRemoved] == REMOVED_VAR ) break;
      if ( p->nRemoved == p->nObjs ) 
	return INVALID_LIT;
      *q = p->nRemoved++;
    }
  else
    *q = p->nObjs++;
  p->pVars[*q] = Var;
  p->pObjs[(unsigned)*q + *q] = Then;
  p->pObjs[(unsigned)*q + *q + 1] = Else;
  *( p->pNexts + *q ) = head;
  if ( p->fVerbose )
    {
      printf( "\rAdded node %10d: Var = %3d.  Then = %10u.  Else = %10u. Removed = %10u.", *q, Var, Then, Else, p->nRemoved );
      fflush( stdout );
    }
  return Abc_BddVar2Lit( *q, 0 );
}
static inline unsigned Abc_BddUniqueCreate( Abc_BddMan * p, int Var, unsigned Then, unsigned Else )
{
  if ( Var < 0 || Var >= p->nVars )   return INVALID_LIT;
  if ( Var >= Abc_BddVar( p, Then ) ) return INVALID_LIT;
  if ( Var >= Abc_BddVar( p, Else ) ) return INVALID_LIT;
  if ( Then == Else )
    return Else;
  if ( !Abc_BddLitIsCompl( Else ) )
    return Abc_BddUniqueCreateInt( p, Var, Then, Else );
  unsigned r = Abc_BddUniqueCreateInt( p, Var, Abc_BddLitNot( Then ), Abc_BddLitNot( Else ) );
  return ( Abc_BddLitIsInvalid( r ) ) ? INVALID_LIT : Abc_BddLitNot( r );
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
  return ( pEnt[0] == Arg1 && pEnt[1] == Arg2 ) ? pEnt[2] : INVALID_LIT;
}
static inline unsigned Abc_BddCacheInsert( Abc_BddMan * p, unsigned Arg1, unsigned Arg2, unsigned Res )
{
  unsigned * pEnt = p->pCache + 3*(long long)( Abc_BddHash( 0, Arg1, Arg2 ) & p->nCacheMask );
  pEnt[0] = Arg1;  pEnt[1] = Arg2;  pEnt[2] = Res;
  p->nCacheMisses++;
  return Res;
}

static inline void Abc_BddCacheRemove( Abc_BddMan * p ) {
  ABC_FREE( p->pCache );
  p->pCache = ABC_CALLOC( unsigned, 3 * (long long)( p->nCacheMask + 1 ) );
}

/**Function*************************************************************
 
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline Abc_BddMan * Abc_BddManAlloc( int nVars, unsigned nObjs, int nGiaObjs, int fVerbose )
{
  Abc_BddMan * p; int i;
  p = ABC_CALLOC( Abc_BddMan, 1 );
  p->nVars       = nVars;
  assert( nVars <= (int)CONST_VAR );
  p->nObjsAlloc  = nObjs;
  p->nUniqueMask = ( 1 << Abc_Base2Log( nObjs ) ) - 1;
  p->nCacheMask  = ( 1 << Abc_Base2Log( nObjs ) ) - 1;
  p->nRemoved    = nObjs - 1;
  p->fVerbose    = 0;
  p->pFanouts    = ABC_CALLOC( int, nGiaObjs );
  assert( p->pFanouts );
  p->pUnique     = ABC_CALLOC( int, p->nUniqueMask + 1 );
  assert( p->pUnique );
  p->pNexts      = ABC_CALLOC( int, p->nUniqueMask + 1 );
  assert( p->pNexts );
  p->pCache      = ABC_CALLOC( unsigned, 3 * (long long)( p->nCacheMask + 1 ) );
  assert( p->pCache );
  p->pObjs       = ABC_CALLOC( unsigned, 2 * (long long)p->nObjsAlloc );
  assert( p->pObjs );
  p->pMark       = ABC_CALLOC( unsigned char, p->nObjsAlloc );
  assert( p->pMark );
  p->pVars       = ABC_CALLOC( unsigned char, p->nObjsAlloc );
  assert( p->pVars );
  p->fVerbose    = fVerbose;
  p->pVars[0]    = CONST_VAR;
  p->nObjs       = 1;
  for ( i = 0; i < nVars; i++ )
    Abc_BddUniqueCreate( p, i, 1, 0 );
  assert( p->nObjs == nVars + 1 );
  p->nMemory = sizeof(Abc_BddMan) + 
    ( p->nUniqueMask + 1 ) * sizeof(int) + 
    (long long)( p->nCacheMask + 1 ) * 3 * sizeof(int) + 
    (long long)p->nObjsAlloc * 2 * sizeof(int) +
    (long long)p->nObjsAlloc * 3 * sizeof(char);
  return p;
}
static inline void Abc_BddManFree( Abc_BddMan * p )
{
  if ( p->fVerbose )
    {
      printf( "BDD stats: Var = %u  Obj = %u  Alloc = %u  Hit = %u  Miss = %u  ", p->nVars, p->nObjs, p->nObjsAlloc, p->nCacheLookups-p->nCacheMisses, p->nCacheMisses );
      printf( "Mem = %.2lld MB\n", (long long)( p->nMemory / ( 1 << 20 ) ) );
    }
  ABC_FREE( p->pUnique );
  ABC_FREE( p->pNexts );
  ABC_FREE( p->pCache );
  ABC_FREE( p->pObjs );
  ABC_FREE( p->pVars );
  ABC_FREE( p->pFanouts );
  ABC_FREE( p );
}
static inline void Abc_BddRehash( Abc_BddMan * p )
{
  unsigned i;
  unsigned nObjsAllocOld = p->nObjsAlloc >> 1; // assuming nObjsAlloc has been doubled.
  for ( i = 0; i < nObjsAllocOld; i++ )
    {
      int * q = p->pUnique + i;
      int * head1 = q;
      int * head2 = q + nObjsAllocOld;
      while ( *q )
	{
	  unsigned hash = Abc_BddHash( (int)p->pVars[*q], p->pObjs[(unsigned)*q + *q], p->pObjs[(unsigned)*q + *q + 1] ) & p->nUniqueMask;
	  int * head;
	  if ( hash == i ) head = head1;
	  else
	    {
	      assert( hash == i + nObjsAllocOld );
	      head = head2;
	    }
	  if ( head != q )
	    {
	      *head = *q;
	      *q = 0;
	    }
	  q = p->pNexts + *head;
	  if ( head == head1 ) head1 = q;
	  else head2 = q;
	}
    }
}
static inline int Abc_BddManRealloc( Abc_BddMan * p )
{
  int * tmp_int;
  unsigned * tmp_uint;
  unsigned char * tmp_uchar;
  p->nObjsAlloc  = p->nObjsAlloc + p->nObjsAlloc;
  if ( p->nObjsAlloc == 0 ) return 1;
  p->nUniqueMask = ( 1 << Abc_Base2Log( p->nObjsAlloc ) ) - 1;
  p->nCacheMask  = ( 1 << Abc_Base2Log( p->nObjsAlloc ) ) - 1;
  tmp_int        = ABC_REALLOC( int, p->pUnique, p->nUniqueMask + 1 );
  if( !tmp_int ) return 1;
  memset( tmp_int + ( ( p->nUniqueMask + 1 ) >> 1 ), 0, sizeof(int) * ( ( p->nUniqueMask + 1 ) >> 1 ) );
  p->pUnique     = tmp_int; 
  tmp_int        = ABC_REALLOC( int, p->pNexts, p->nUniqueMask + 1 );
  if( !tmp_int ) return 1;
  memset( tmp_int + ( ( p->nUniqueMask + 1 ) >> 1 ), 0, sizeof(int) * ( ( p->nUniqueMask + 1 ) >> 1 ) );
  p->pNexts      = tmp_int;
  Abc_BddRehash( p );
  ABC_FREE( p->pCache );
  p->pCache      = ABC_CALLOC( unsigned, 3 * (long long)( p->nCacheMask + 1 ) );
  tmp_uint       = ABC_REALLOC( unsigned, p->pObjs, 2 * (long long)p->nObjsAlloc );
  if( !tmp_uint ) return 1;
  memset( tmp_uint + p->nObjsAlloc, 0, sizeof(unsigned) * p->nObjsAlloc );
  p->pObjs       = tmp_uint;
  tmp_uchar      = ABC_REALLOC( unsigned char, p->pMark, p->nObjsAlloc );
  if( !tmp_uchar ) return 1;
  memset( tmp_uchar + ( p->nObjsAlloc >> 1 ), 0, sizeof(unsigned char) * ( p->nObjsAlloc >> 1 ) );
  p->pMark       = tmp_uchar;
  tmp_uchar      = ABC_REALLOC( unsigned char, p->pVars, p->nObjsAlloc );
  if( !tmp_uchar ) return 1;
  memset( tmp_uchar + ( p->nObjsAlloc >> 1 ), 0, sizeof(unsigned char) * ( p->nObjsAlloc >> 1 ) );
  p->pVars       = tmp_uchar;
  p->nMemory = sizeof(Abc_BddMan) + 
    ( p->nUniqueMask + 1 ) * sizeof(int) + 
    (long long)( p->nCacheMask + 1 ) * 3 * sizeof(int) + 
    (long long)p->nObjsAlloc * 2 * sizeof(int) +
    (long long)p->nObjsAlloc * 3 * sizeof(char);
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
  if ( Abc_BddLitIsInvalid( a ) || Abc_BddLitIsInvalid( b ) ) return INVALID_LIT;
  unsigned r0, r1, r;
  if ( a == 0 ) return 0;
  if ( b == 0 ) return 0;
  if ( a == 1 ) return b;
  if ( b == 1 ) return a;
  if ( a == b ) return a;
  if ( a > b )  return Abc_BddAnd( p, b, a );
  r = Abc_BddCacheLookup( p, a, b );
  if ( !Abc_BddLitIsInvalid( r ) )
    return r;
  if ( Abc_BddVar( p, a ) < Abc_BddVar( p, b ) )
    r0 = Abc_BddAnd( p, Abc_BddElse( p, a ), b ), 
      r1 = Abc_BddAnd( p, Abc_BddThen( p, a ), b );
  else if ( Abc_BddVar( p, a ) > Abc_BddVar( p, b ) )
    r0 = Abc_BddAnd( p, a, Abc_BddElse( p, b ) ), 
      r1 = Abc_BddAnd( p, a, Abc_BddThen( p, b ) );
  else // if ( Abc_BddVar( p, a ) == Abc_BddVar( p, b ) )
    r0 = Abc_BddAnd( p, Abc_BddElse( p, a ), Abc_BddElse( p, b ) ), 
      r1 = Abc_BddAnd( p, Abc_BddThen( p, a ), Abc_BddThen( p, b ) );
  if ( Abc_BddLitIsInvalid( r0 ) || Abc_BddLitIsInvalid( r1 ) ) return INVALID_LIT;
  r = Abc_BddUniqueCreate( p, Abc_MinInt( Abc_BddVar( p, a ), Abc_BddVar( p, b ) ), r1, r0 );
  if ( Abc_BddLitIsInvalid( r ) ) return INVALID_LIT;
  return Abc_BddCacheInsert( p, a, b, r );
}
unsigned Abc_BddOr( Abc_BddMan * p, unsigned a, unsigned b )
{
  unsigned r = Abc_BddAnd( p, Abc_BddLitNot( a ), Abc_BddLitNot( b ) );
  return ( Abc_BddLitIsInvalid( r ) ) ? INVALID_LIT : Abc_BddLitNot( r );
}

/**Function*************************************************************
   
   Synopsis    [Counting nodes.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
int Abc_BddCount_rec( Abc_BddMan * p, unsigned i )
{
  if ( i < 2 )
    return 0;
  if ( Abc_BddMark( p, i ) )
    return 0;
  Abc_BddSetMark( p, i, 1 );
  return 1 + Abc_BddCount_rec( p, Abc_BddElse( p, i ) ) + Abc_BddCount_rec( p, Abc_BddThen( p, i ) );
}
void Abc_BddUnmark_rec( Abc_BddMan * p, unsigned i )
{
  if ( i < 2 )
    return;
  if ( !Abc_BddMark( p, i ) )
    return;
  Abc_BddSetMark( p, i, 0 );
  Abc_BddUnmark_rec( p, Abc_BddElse( p, i ) );
  Abc_BddUnmark_rec( p, Abc_BddThen( p, i ) );
}
int Abc_BddCountNodes( Abc_BddMan * p, unsigned i )
{
  int Count = Abc_BddCount_rec( p, i );
  Abc_BddUnmark_rec( p, i );
  return Count;
}
int Abc_BddCountNodesArray( Abc_BddMan * p, Vec_Int_t * vNodes )
{
  int i, a, Count = 0;
  Vec_IntForEachEntry( vNodes, a, i )
    Count += Abc_BddCount_rec( p, (unsigned)a );
  Vec_IntForEachEntry( vNodes, a, i )
    Abc_BddUnmark_rec( p, (unsigned)a );
  return Count;
}
int Abc_BddCountNodesArray2( Abc_BddMan * p, Vec_Int_t * vNodes )
{
  int i, a, Count = 0;
  Vec_IntForEachEntry( vNodes, a, i )
    {
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
void Abc_BddPrint_rec( Abc_BddMan * p, unsigned a, int * pPath )
{
  if ( a == 0 ) 
    return;
  if ( a == 1 )
    { 
      int i;
      for ( i = 0; i < p->nVars; i++ )
	if ( pPath[i] == 0 || pPath[i] == 1 )
	  printf( "%c%d", pPath[i] ? '+' : '-', i );
      printf( " " );
      return; 
    }
  pPath[Abc_BddVar( p, a )] =  0;
  Abc_BddPrint_rec( p, Abc_BddElse( p, a ), pPath );
  pPath[Abc_BddVar( p, a )] =  1;
  Abc_BddPrint_rec( p, Abc_BddThen( p, a ), pPath );
  pPath[Abc_BddVar( p, a )] = -1;
}
void Abc_BddPrint( Abc_BddMan * p, unsigned a )
{
  int * pPath = ABC_FALLOC( int, p->nVars );
  printf( "BDD %u = ", a );
  Abc_BddPrint_rec( p, a, pPath );
  ABC_FREE( pPath );
  printf( "\n" );
}
void Abc_BddPrintTest( Abc_BddMan * p )
{
  unsigned bVarA = Abc_BddIthVar( 0 );
  unsigned bVarB = Abc_BddIthVar( 1 );
  unsigned bVarC = Abc_BddIthVar( 2 );
  unsigned bVarD = Abc_BddIthVar( 3 );
  unsigned bAndAB = Abc_BddAnd( p, bVarA, bVarB );
  unsigned bAndCD = Abc_BddAnd( p, bVarC, bVarD );
  unsigned bFunc  = Abc_BddOr( p, bAndAB, bAndCD );
  Abc_BddPrint( p, bFunc );
  printf( "Nodes = %d\n", Abc_BddCountNodes( p, bFunc ) );
}

/**Function*************************************************************

   Synopsis    [Remove unnecessary BDD nodes.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddMarkChildren ( Abc_BddMan * p, unsigned i )
{
  unsigned Then = Abc_BddThen( p, i );
  unsigned Else = Abc_BddElse( p, i );
  if ( Abc_BddMark( p, Then ) == 0 )
    {
      Abc_BddSetMark( p, Then, INVALID_MARK );
      Abc_BddMarkChildren( p, Then );
    }
  if ( Abc_BddMark( p, Else ) == 0 )
    {
      Abc_BddSetMark( p, Else, INVALID_MARK );
      Abc_BddMarkChildren( p, Else );
    }
}
void Abc_BddUnmarkChildren ( Abc_BddMan * p, unsigned i )
{
  unsigned Then = Abc_BddThen( p, i );
  unsigned Else = Abc_BddElse( p, i );
  if ( Abc_BddMark( p, Then ) == INVALID_MARK )
    {
      Abc_BddSetMark( p, Then, 0 );
      Abc_BddUnmarkChildren( p, Then );
    }
  if ( Abc_BddMark( p, Else ) == INVALID_MARK )
    {
      Abc_BddSetMark( p, Else , 0 );
      Abc_BddUnmarkChildren( p, Else );
    }
}
static inline void Abc_BddRemoveNode( Abc_BddMan * p, unsigned i )
{
  int Var = Abc_BddVar( p, i );
  int Then = Abc_BddThen( p, i );
  int Else = Abc_BddElse( p, i );
  int *q = p->pUnique + ( Abc_BddHash( Var, Then, Else ) & p->nUniqueMask );
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == Abc_BddLit2Var( i ) )
      break;
  int *q_next = p->pNexts + *q;
  *q = *q_next;
  *q_next = 0;
  Abc_BddSetVarRemoved( p, i );
}
static inline void Abc_BddRefresh( Abc_BddMan * p )
{
  if ( p->fVerbose )
    {
      printf( "\nrefresh\n" );
      fflush( stdout );
    }
  unsigned i;
  int pFrontiers[MAX_NUM_FRONTIERS];
  int nFrontiers = 0;
  for ( i = p->nVars + 1; i < p->nObjs; i++ )
    if ( p->pMark[i] > 0 )
      {
	pFrontiers[nFrontiers] = i;
	nFrontiers += 1;
	assert( nFrontiers < MAX_NUM_FRONTIERS );
      }
  for ( i = 0; i < nFrontiers; i++ )
    Abc_BddMarkChildren ( p, Abc_Var2Lit( pFrontiers[i], 0 ) );
  for ( i = p->nVars + 1; i < p->nObjs; i++ ) 
    if ( p->pMark[i] == 0 && p->pVars[i] != REMOVED_VAR )
      {
	if ( p->nRemoved > i ) p->nRemoved = i;
	Abc_BddRemoveNode( p, Abc_BddVar2Lit( (int)i, 0 ) );
      }
  Abc_BddCacheRemove( p );
  for ( i = 0; i < nFrontiers; i++ )
    Abc_BddUnmarkChildren ( p, Abc_BddVar2Lit( pFrontiers[i], 0 ) );
}

/**Function*************************************************************

   Synopsis    [Count fanout of gates.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
static inline void Abc_BddGiaCountFanout( Gia_Man_t * pGia, Abc_BddMan * p )
{
  Gia_Obj_t * pObj; int i;
  Gia_ManStaticFanoutStart( pGia );
  Gia_ManForEachAnd( pGia, pObj, i )
    p->pFanouts[Gia_ObjId( pGia, pObj )] = Gia_ObjFanoutNum( pGia, pObj );
  Gia_ManStaticFanoutStop( pGia );
}

/**Function*************************************************************

   Synopsis    [Main for bdd with garbage collection]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddGiaTest( Gia_Man_t * pGia, int fVerbose, int nMem, int nJump )
{
  abctime clk = Abc_Clock();
  Abc_BddMan * p;
  Vec_Int_t * vNodes;
  Gia_Obj_t * pObj;
  int i;
  int fRefresh = 0;
  unsigned nObjsAllocInit = 1 << nMem;
  while ( nObjsAllocInit < Gia_ManCiNum( pGia ) + 2 )
    {
      nObjsAllocInit = nObjsAllocInit << 1;
      assert( nObjsAllocInit != 0 );
    }
  if ( fVerbose ) printf( "Allocated node to 2^%d\n", Abc_Base2Log( nObjsAllocInit ) );
  p = Abc_BddManAlloc( Gia_ManCiNum( pGia ), nObjsAllocInit, pGia->nObjs, fVerbose );
  Abc_BddGiaCountFanout( pGia, p );
  Gia_ManFillValue( pGia );
  Gia_ManConst0( pGia )->Value = 0;
  Gia_ManForEachCi( pGia, pObj, i )
    pObj->Value = Abc_BddIthVar( i );
  vNodes = Vec_IntAlloc( Gia_ManAndNum( pGia ) );
  Gia_ManForEachAnd( pGia, pObj, i )
    {
      Gia_Obj_t * pObj0 = Gia_ObjFanin0( pObj );
      Gia_Obj_t * pObj1 = Gia_ObjFanin1( pObj );
      unsigned Cof0 = Abc_BddLitNotCond( pObj0->Value, Gia_ObjFaninC0( pObj ) );
      unsigned Cof1 = Abc_BddLitNotCond( pObj1->Value, Gia_ObjFaninC1( pObj ) );
      pObj->Value = Abc_BddAnd( p, Cof0, Cof1 );
      if ( Abc_BddLitIsInvalid( pObj->Value ) )
	{
	  if ( fRefresh )
	    {
	      if ( p->nObjsAlloc == 1 << 31 )
		{
		  printf( "The number of nodes exceeds the limit 2^31\n" );
		  assert(0);
		}
	      else if ( nJump > 0 )
		{
		  if ( p->nObjsAlloc >= 1 << nJump )
		    {
		      printf( "The number of nodes exceeds the jumped limit 2^%d\n", nJump );
		      assert(0);
		    }
		  Abc_BddManFree( p );
		  if ( fVerbose ) printf( "Reallocate nodes jump to 2^%d\n", nJump );
		  p = Abc_BddManAlloc( Gia_ManCiNum( pGia ), 1 << nJump, pGia->nObjs, fVerbose );
		  Abc_BddGiaCountFanout( pGia, p );
		  Gia_ManFillValue( pGia );
		  Gia_ManConst0( pGia )->Value = 0;
		  Gia_ManForEachCi( pGia, pObj, i )
		    pObj->Value = Abc_BddIthVar( i );
		  i = -1;
		  continue;
		}
	      else if ( Abc_BddManRealloc( p ) )
		{
		  printf( "error : reallocation failed\n" );
		  assert(0);
		}
	      else if( fVerbose )
		printf( "\nReallocated node to 2^%d\n", Abc_Base2Log( p->nObjsAlloc ) );
	    }
	  else
	    {
	      fRefresh = 1;
	      Abc_BddRefresh( p );
	    }
	  i--;
	  continue;
	}
      fRefresh = 0;
      Abc_BddIncMark( p, pObj->Value );
      p->pFanouts[Gia_ObjId( pGia, pObj0 )] -= 1;
      if ( p->pFanouts[Gia_ObjId( pGia, pObj0 )] == 0 )
	Abc_BddDecMark( p, pObj0->Value );
      p->pFanouts[Gia_ObjId( pGia, pObj1 )] -= 1;
      if ( p->pFanouts[Gia_ObjId( pGia, pObj1 )] == 0 )
	Abc_BddDecMark( p, pObj1->Value );
    }
  Gia_ManForEachCo( pGia, pObj, i )
    pObj->Value = Abc_BddLitNotCond( Gia_ObjFanin0( pObj )->Value, Gia_ObjFaninC0( pObj ) );
  abctime clk2 = Abc_Clock();
  Gia_ManForEachCo( pGia, pObj, i )
    {
      //      if ( fVerbose )
      //	Abc_BddPrint( p, pObj->Value );
      if ( Abc_BddLit2Var( pObj->Value ) > p->nVars )
	{
	  Vec_IntPush( vNodes, pObj->Value );
	  if ( Abc_BddMark( p, pObj->Value ) != 0 )
	    Abc_BddDecMark( p, pObj->Value );
	}
    }
  if( fVerbose ) printf( "\n" );
  ABC_PRT( "BDD construction time", clk2 - clk );
  printf( "Shared nodes = %d Allocated nodes = %u\n", Abc_BddCountNodesArray2( p, vNodes ), p->nObjsAlloc );
  Vec_IntFree( vNodes );
  Abc_BddManFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

