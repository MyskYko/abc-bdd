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

#define MAX_NUM_FRONTIERS 10000

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
  if ( Abc_BddIsLimit( p ) )
    {
      for ( ; p->nRemoved < p->nObjs; p->nRemoved++ )
	if ( Abc_BddLitIsRemoved( p, Abc_BddVar2Lit( p->nRemoved, 0 ) ) ) break;
      if ( p->nRemoved == p->nObjs ) return Abc_BddInvalidLit();
      *q = p->nRemoved++;
    }
  else *q = p->nObjs++;
  p->pVars[*q] = Var;
  p->pObjs[(unsigned)*q + *q] = Then;
  p->pObjs[(unsigned)*q + *q + 1] = Else;
  *( p->pNexts + *q ) = head;
  if ( p->fVerbose )
    printf( "Added node %10d: Var = %3d  Then = %10u  Else = %10u  Removed = %10u\n", *q, Var, Then, Else, p->nRemoved );
  return Abc_BddVar2Lit( *q, 0 );
}
unsigned Abc_BddUniqueCreate( Abc_BddMan * p, int Var, unsigned Then, unsigned Else )
{
  if ( Var < 0 || Var >= p->nVars )   return Abc_BddInvalidLit();
  if ( Var >= Abc_BddVar( p, Then ) ) return Abc_BddInvalidLit();
  if ( Var >= Abc_BddVar( p, Else ) ) return Abc_BddInvalidLit();
  if ( Abc_BddEq( Then, Else ) ) return Else;
  if ( !Abc_BddLitIsCompl( Else ) ) return Abc_BddUniqueCreateInt( p, Var, Then, Else );
  unsigned r = Abc_BddUniqueCreateInt( p, Var, Abc_BddLitNot( Then ), Abc_BddLitNot( Else ) );
  return ( Abc_BddLitIsInvalid( r ) ) ? Abc_BddInvalidLit() : Abc_BddLitNot( r );
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
  return ( pEnt[0] == Arg1 && pEnt[1] == Arg2 ) ? pEnt[2] : Abc_BddInvalidLit();
}
static inline unsigned Abc_BddCacheInsert( Abc_BddMan * p, unsigned Arg1, unsigned Arg2, unsigned Res )
{
  unsigned * pEnt = p->pCache + 3*(long long)( Abc_BddHash( 0, Arg1, Arg2 ) & p->nCacheMask );
  pEnt[0] = Arg1;
  pEnt[1] = Arg2;
  pEnt[2] = Res;
  p->nCacheMisses++;
  return Res;
}

static inline void Abc_BddCacheRefresh( Abc_BddMan * p ) {
  ABC_FREE( p->pCache );
  p->pCache = ABC_CALLOC( unsigned, 3 * (long long)( p->nCacheMask + 1 ) );
  if ( p->fVerbose )
    printf( "Cache: Hit = %u  Miss = %u\n", p->nCacheLookups - p->nCacheMisses, p->nCacheMisses );
}

/**Function*************************************************************
 
   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
Abc_BddMan * Abc_BddManAlloc( int nVars, unsigned nObjs, int fVerbose )
{
  Abc_BddMan * p; int i;
  p = ABC_CALLOC( Abc_BddMan, 1 );
  p->nVars       = nVars;
  assert( nVars <= (int)Abc_BddConstVar() );
  p->nObjsAlloc  = nObjs;
  p->nUniqueMask = ( 1 << Abc_Base2Log( nObjs ) ) - 1;
  p->nCacheMask  = ( 1 << Abc_Base2Log( nObjs ) ) - 1;
  p->nRemoved    = nObjs - 1;
  p->fVerbose    = fVerbose;
  p->pUnique     = ABC_CALLOC( int, p->nUniqueMask + 1 );
  p->pNexts      = ABC_CALLOC( int, p->nUniqueMask + 1 );
  p->pCache      = ABC_CALLOC( unsigned, 3 * (long long)( p->nCacheMask + 1 ) );
  p->pObjs       = ABC_CALLOC( unsigned, 2 * (long long)p->nObjsAlloc );
  p->pMark       = ABC_CALLOC( unsigned char, p->nObjsAlloc );
  p->pVars       = ABC_CALLOC( unsigned char, p->nObjsAlloc );
  assert( p->pUnique );
  assert( p->pNexts );
  assert( p->pCache );
  assert( p->pObjs );
  assert( p->pMark );
  assert( p->pVars );
  p->pVars[0]    = Abc_BddConstVar();
  p->nObjs       = 1;
  for ( i = 0; i < nVars; i++ ) Abc_BddUniqueCreate( p, i, 1, 0 );
  assert( p->nObjs == nVars + 1 );
  p->nMemory = sizeof(Abc_BddMan) + 
    ( p->nUniqueMask + 1 ) * sizeof(int) + 
    (long long)( p->nCacheMask + 1 ) * 3 * sizeof(int) + 
    (long long)p->nObjsAlloc * 2 * sizeof(int) +
    (long long)p->nObjsAlloc * 3 * sizeof(char);
  return p;
}
void Abc_BddManFree( Abc_BddMan * p )
{
  if ( p->fVerbose )
    {
      printf( "BDD stats: Var = %u  Obj = %u  Alloc = %u  Hit = %u  Miss = %u  ", p->nVars, p->nObjs, p->nObjsAlloc - 1, p->nCacheLookups - p->nCacheMisses, p->nCacheMisses );
      printf( "Mem = %.2lld MB\n", (long long)( p->nMemory / ( 1 << 20 ) ) );
    }
  ABC_FREE( p->pUnique );
  ABC_FREE( p->pNexts );
  ABC_FREE( p->pCache );
  ABC_FREE( p->pObjs );
  ABC_FREE( p->pVars );
  ABC_FREE( p );
}
void Abc_BddRehash( Abc_BddMan * p )
{
  unsigned i, hash;
  int * q, * head, * head1, * head2;
  unsigned nObjsAllocOld = p->nObjsAlloc >> 1; // assuming nObjsAlloc has been doubled.
  for ( i = 0; i < nObjsAllocOld; i++ )
    {
      q = p->pUnique + i;
      head1 = q;
      head2 = q + nObjsAllocOld;
      while ( *q )
	{
	  hash = Abc_BddHash( (int)p->pVars[*q], p->pObjs[(unsigned)*q + *q], p->pObjs[(unsigned)*q + *q + 1] ) & p->nUniqueMask;
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
void Abc_BddManRealloc( Abc_BddMan * p )
{
  p->nObjsAlloc  = p->nObjsAlloc + p->nObjsAlloc;
  assert( p->nObjsAlloc != 0 );
  p->nUniqueMask = ( 1 << Abc_Base2Log( p->nObjsAlloc ) ) - 1;
  p->nCacheMask  = ( 1 << Abc_Base2Log( p->nObjsAlloc ) ) - 1;
  p->pUnique     = ABC_REALLOC( int, p->pUnique, p->nUniqueMask + 1 );
  p->pNexts      = ABC_REALLOC( int, p->pNexts, p->nUniqueMask + 1 );
  p->pObjs       = ABC_REALLOC( unsigned, p->pObjs, 2 * (long long)p->nObjsAlloc );
  p->pMark       = ABC_REALLOC( unsigned char, p->pMark, p->nObjsAlloc );
  p->pVars       = ABC_REALLOC( unsigned char, p->pVars, p->nObjsAlloc );
  assert( p->pUnique );
  assert( p->pNexts );
  assert( p->pObjs );
  assert( p->pMark );
  assert( p->pVars );
  memset( p->pUnique + ( ( p->nUniqueMask + 1 ) >> 1 ), 0, sizeof(int) * ( ( p->nUniqueMask + 1 ) >> 1 ) );
  memset( p->pNexts + ( ( p->nUniqueMask + 1 ) >> 1 ), 0, sizeof(int) * ( ( p->nUniqueMask + 1 ) >> 1 ) );
  memset( p->pObjs + p->nObjsAlloc, 0, sizeof(unsigned) * p->nObjsAlloc );
  memset( p->pMark + ( p->nObjsAlloc >> 1 ), 0, sizeof(unsigned char) * ( p->nObjsAlloc >> 1 ) );
  memset( p->pVars + ( p->nObjsAlloc >> 1 ), 0, sizeof(unsigned char) * ( p->nObjsAlloc >> 1 ) );
  Abc_BddCacheRefresh( p );
  p->nMemory = sizeof(Abc_BddMan) + 
    ( p->nUniqueMask + 1 ) * sizeof(int) + 
    (long long)( p->nCacheMask + 1 ) * 3 * sizeof(int) + 
    (long long)p->nObjsAlloc * 2 * sizeof(int) +
    (long long)p->nObjsAlloc * 3 * sizeof(char);
  Abc_BddRehash( p );
}

/**Function*************************************************************
   
   Synopsis    [Boolean AND.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
unsigned Abc_BddAnd( Abc_BddMan * p, unsigned a, unsigned b )
{
  if ( Abc_BddLitIsInvalid( a ) || Abc_BddLitIsInvalid( b ) ) return Abc_BddInvalidLit();
  if ( Abc_BddLitIsConst0( a ) ) return a;
  if ( Abc_BddLitIsConst0( b ) ) return b;
  if ( Abc_BddLitIsConst1( a ) ) return b;
  if ( Abc_BddLitIsConst1( b ) ) return a;
  if ( Abc_BddEq( a, b ) ) return a;
  if ( a > b )  return Abc_BddAnd( p, b, a );
  unsigned r0, r1, r;
  unsigned s0, s1, t0, t1;
  r = Abc_BddCacheLookup( p, a, b );
  if ( !Abc_BddLitIsInvalid( r ) ) return r;
  if ( Abc_BddVar( p, a ) < Abc_BddVar( p, b ) )
    s0 = Abc_BddElse( p, a ), t0 = b, s1 = Abc_BddThen( p, a ), t1 = b;
  else if ( Abc_BddVar( p, a ) > Abc_BddVar( p, b ) )
    s0 = a, t0 = Abc_BddElse( p, b ), s1 = a, t1 = Abc_BddThen( p, b );
  else // if ( Abc_BddVar( p, a ) == Abc_BddVar( p, b ) )
    s0 = Abc_BddElse( p, a ), t0 = Abc_BddElse( p, b ), s1 = Abc_BddThen( p, a ), t1 = Abc_BddThen( p, b );
  r0 = Abc_BddAnd( p, s0, t0 );
  if ( Abc_BddLitIsInvalid( r0 ) ) return Abc_BddInvalidLit();
  r1 = Abc_BddAnd( p, s1, t1 );
  if ( Abc_BddLitIsInvalid( r1 ) ) return Abc_BddInvalidLit();
  r = Abc_BddUniqueCreate( p, Abc_MinInt( Abc_BddVar( p, a ), Abc_BddVar( p, b ) ), r1, r0 );
  if ( Abc_BddLitIsInvalid( r ) ) return Abc_BddInvalidLit();
  return Abc_BddCacheInsert( p, a, b, r );
}
unsigned Abc_BddOr( Abc_BddMan * p, unsigned a, unsigned b )
{
  unsigned r = Abc_BddAnd( p, Abc_BddLitNot( a ), Abc_BddLitNot( b ) );
  return ( Abc_BddLitIsInvalid( r ) ) ? Abc_BddInvalidLit() : Abc_BddLitNot( r );
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
void Abc_BddUnmark_rec( Abc_BddMan * p, unsigned i )
{
  if ( Abc_BddLitIsConst( i ) ) return;
  if ( !Abc_BddMark( p, i ) ) return;
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
void Abc_BddPrint_rec( Abc_BddMan * p, unsigned a, int * pPath, int offset, FILE * f )
{
  if ( Abc_BddLitIsConst0( a ) ) return;
  if ( Abc_BddLitIsConst1( a ) )
    { 
      int i;
      for ( i = 0; i < p->nVars; i++ )
	if ( pPath[i] == 0 || pPath[i] == 1 )
	  fprintf( f, "%c%d", pPath[i] ? '+' : '-', i - offset );
      fprintf( f, "\n" );
      return; 
    }
  pPath[Abc_BddVar( p, a )] =  0;
  Abc_BddPrint_rec( p, Abc_BddElse( p, a ), pPath, offset, f );
  pPath[Abc_BddVar( p, a )] =  1;
  Abc_BddPrint_rec( p, Abc_BddThen( p, a ), pPath, offset, f );
  pPath[Abc_BddVar( p, a )] = -1;
}
void Abc_BddPrint( Abc_BddMan * p, unsigned a, int offset, FILE * f )
{
  int * pPath = ABC_FALLOC( int, p->nVars );
  fprintf( f, "BDD %u =\n", a );
  Abc_BddPrint_rec( p, a, pPath, offset, f );
  ABC_FREE( pPath );
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
  if ( !Abc_BddMark( p, Then ) )
    {
      Abc_BddSetMarkInvalid( p, Then );
      Abc_BddMarkChildren( p, Then );
    }
  if ( !Abc_BddMark( p, Else ) )
    {
      Abc_BddSetMarkInvalid( p, Else );
      Abc_BddMarkChildren( p, Else );
    }
}
void Abc_BddUnmarkChildren ( Abc_BddMan * p, unsigned i )
{
  unsigned Then = Abc_BddThen( p, i );
  unsigned Else = Abc_BddElse( p, i );
  if ( Abc_BddMarkIsInvalid( p, Then ) )
    {
      Abc_BddSetMark( p, Then, 0 );
      Abc_BddUnmarkChildren( p, Then );
    }
  if ( Abc_BddMarkIsInvalid( p, Else ) )
    {
      Abc_BddSetMark( p, Else , 0 );
      Abc_BddUnmarkChildren( p, Else );
    }
}
void Abc_BddRemoveNode( Abc_BddMan * p, unsigned i )
{
  int Var = Abc_BddVar( p, i );
  unsigned Then = Abc_BddThen( p, i );
  unsigned Else = Abc_BddElse( p, i );
  int *q = p->pUnique + ( Abc_BddHash( Var, Then, Else ) & p->nUniqueMask );
  for ( ; *q; q = p->pNexts + *q )
    if ( *q == Abc_BddLit2Var( i ) ) break;
  int *q_next = p->pNexts + *q;
  *q = *q_next;
  *q_next = 0;
  Abc_BddSetLitRemoved( p, i );
}
void Abc_BddRefresh( Abc_BddMan * p )
{
  int i, nFrontiers = 0;
  unsigned a;
  unsigned pFrontiers[MAX_NUM_FRONTIERS];
  if ( p->fVerbose ) printf( "Refresh\n" );
  for ( i = p->nVars + 1; i < p->nObjs; i++ )
    {
      a = Abc_BddVar2Lit( i, 0 );
      if ( Abc_BddMark( p, a ) )
	{
	  pFrontiers[nFrontiers] = a;
	  nFrontiers += 1;
	  assert( nFrontiers < MAX_NUM_FRONTIERS );
	}
    }
  for ( i = 0; i < nFrontiers; i++ ) Abc_BddMarkChildren ( p, pFrontiers[i] );
  for ( i = p->nVars + 1; i < p->nObjs; i++ )
    {
      a = Abc_BddVar2Lit( i, 0 );
      if ( !Abc_BddMark( p, a ) && !Abc_BddLitIsRemoved( p, a ) )
	{
	  if ( p->nRemoved > i ) p->nRemoved = i;
	  Abc_BddRemoveNode( p, a );
	}
    }
  for ( i = 0; i < nFrontiers; i++ ) Abc_BddUnmarkChildren ( p, pFrontiers[i] );
  Abc_BddCacheRefresh( p );
  
}

/**Function*************************************************************

   Synopsis    [Count fanout of gates.]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddGiaCountFanout( Gia_Man_t * pGia, int * pFanouts )
{
  Gia_Obj_t * pObj; int i;
  Gia_ManStaticFanoutStart( pGia );
  Gia_ManForEachAnd( pGia, pObj, i )
    pFanouts[Gia_ObjId( pGia, pObj )] = Gia_ObjFanoutNum( pGia, pObj );
  Gia_ManStaticFanoutStop( pGia );
}

/**Function*************************************************************

   Synopsis    [Main for bdd with garbage collection]

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
void Abc_BddGia( Gia_Man_t * pGia, int nVerbose, int nJump, Abc_BddMan * p, int fGarbage, int fRealloc )
{
  Gia_Obj_t * pObj, * pObj0, *pObj1;
  int i, fRefresh = 0;
  unsigned Cof0, Cof1;
  int * pFanouts = ABC_CALLOC( int, pGia->nObjs );
  assert( pFanouts );
  Abc_BddGiaCountFanout( pGia, pFanouts );
  Gia_ManFillValue( pGia );
  Gia_ManConst0( pGia )->Value = Abc_BddConst0();
  Gia_ManForEachCi( pGia, pObj, i ) pObj->Value = Abc_BddIthVar( i );
  Gia_ManForEachAnd( pGia, pObj, i )
    {
      pObj0 = Gia_ObjFanin0( pObj );
      pObj1 = Gia_ObjFanin1( pObj );
      Cof0 = Abc_BddLitNotCond( pObj0->Value, Gia_ObjFaninC0( pObj ) );
      Cof1 = Abc_BddLitNotCond( pObj1->Value, Gia_ObjFaninC1( pObj ) );
      pObj->Value = Abc_BddAnd( p, Cof0, Cof1 );
      if ( Abc_BddLitIsInvalid( pObj->Value ) )
	{
	  if ( fGarbage && !fRefresh )
	    {
	      fRefresh = 1;
	      Abc_BddRefresh( p );
	      i--;
	      continue;
	    }
	  if ( fRealloc )
	    {
	      if ( nJump > 0 )
		{
		  assert( p->nObjsAlloc < 1 << nJump );
		  Abc_BddManFree( p );
		  if ( nVerbose ) printf( "Reallocate nodes jump to 2^%d\n", nJump );
		  p = Abc_BddManAlloc( Gia_ManCiNum( pGia ), 1 << nJump, nVerbose > 1 );
		  Abc_BddGiaCountFanout( pGia, pFanouts );
		  Gia_ManFillValue( pGia );
		  Gia_ManConst0( pGia )->Value = 0;
		  Gia_ManForEachCi( pGia, pObj, i ) pObj->Value = Abc_BddIthVar( i );
		  i = -1;
		  continue;
		}
	      assert( p->nObjsAlloc < 1 << 31 );
	      if( nVerbose )
		printf( "Reallocate nodes by 2^%d\n", Abc_Base2Log( p->nObjsAlloc << 1 ) );
	      Abc_BddManRealloc( p );
	      i--;
	      continue;
	    }
	}
      assert( !Abc_BddLitIsInvalid( pObj->Value ) );
      fRefresh = 0;
      Abc_BddIncMark( p, pObj->Value );
      pFanouts[Gia_ObjId( pGia, pObj0 )] -= 1;
      if ( pFanouts[Gia_ObjId( pGia, pObj0 )] == 0 ) Abc_BddDecMark( p, pObj0->Value );
      pFanouts[Gia_ObjId( pGia, pObj1 )] -= 1;
      if ( pFanouts[Gia_ObjId( pGia, pObj1 )] == 0 ) Abc_BddDecMark( p, pObj1->Value );
    }
  Gia_ManForEachCo( pGia, pObj, i )
    pObj->Value = Abc_BddLitNotCond( Gia_ObjFanin0( pObj )->Value, Gia_ObjFaninC0( pObj ) );
  Gia_ManForEachCo( pGia, pObj, i )
    if ( Abc_BddLit2Var( pObj->Value ) > p->nVars && Abc_BddMark( p, pObj->Value ) != 0 )
      Abc_BddDecMark( p, pObj->Value );
  ABC_FREE( pFanouts );
}
void Abc_BddGiaTest( Gia_Man_t * pGia, int nVerbose, int nMem, int nJump, FILE * pFile, int fRealloc, int fGarbage )
{
  abctime clk = Abc_Clock();
  Abc_BddMan * p;
  Vec_Int_t * vNodes;
  Gia_Obj_t * pObj;
  int i;
  unsigned nObjsAllocInit = 1 << nMem;
  while ( nObjsAllocInit < Gia_ManCiNum( pGia ) + 2 )
    {
      nObjsAllocInit = nObjsAllocInit << 1;
      assert( nObjsAllocInit != 0 );
    }
  if ( nVerbose ) printf( "Allocate nodes by 2^%d\n", Abc_Base2Log( nObjsAllocInit ) );
  p = Abc_BddManAlloc( Gia_ManCiNum( pGia ), nObjsAllocInit, nVerbose > 1 );
  Abc_BddGia( pGia, nVerbose, nJump, p, fRealloc, fGarbage );
  abctime clk2 = Abc_Clock();
  vNodes = Vec_IntAlloc( Gia_ManCoNum( pGia ) );
  Gia_ManForEachCo( pGia, pObj, i )
    {
      if ( pFile != NULL ) Abc_BddPrint( p, pObj->Value, 0, pFile );
      if ( Abc_BddLit2Var( pObj->Value ) > p->nVars ) Vec_IntPush( vNodes, pObj->Value );
    }
  ABC_PRT( "BDD construction time", clk2 - clk );
  printf( "Shared nodes = %d  Used nodes = %d  Allocated nodes = %u\n", Abc_BddCountNodesArray2( p, vNodes ), p->nObjs, p->nObjsAlloc - 1 );
  Vec_IntFree( vNodes );
  Abc_BddManFree( p );
}

/**Function*************************************************************

   Synopsis    []

   Description []
               
   SideEffects []

   SeeAlso     []

***********************************************************************/
int Abc_BddCount0s( Abc_BddMan * p, unsigned a, int depth )
{
  if ( p->nVars - depth < 0 ) return 0;
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

