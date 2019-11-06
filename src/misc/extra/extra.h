/**CFile****************************************************************

  FileName    [extra.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [extra]

  Synopsis    [Various reusable software utilities.]

  Description [This library contains a number of operators and 
  traversal routines developed to extend the functionality of 
  CUDD v.2.3.x, by Fabio Somenzi (http://vlsi.colorado.edu/~fabio/)
  To compile your code with the library, #include "extra.h" 
  in your source files and link your project to CUDD and this 
  library. Use the library at your own risk and with caution. 
  Note that debugging of some operators still continues.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: extra.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__misc__extra__extra_h
#define ABC__misc__extra__extra_h


#ifdef _WIN32
#define inline __inline // compatible with MS VS 6.0
#endif

/*---------------------------------------------------------------------------*/
/* Nested includes                                                           */
/*---------------------------------------------------------------------------*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "misc/st/st.h"
#include "aig/gia/gia.h"

ABC_NAMESPACE_HEADER_START


/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

typedef unsigned char      uint8;
typedef unsigned short     uint16;
typedef unsigned int       uint32;

/*===========================================================================*/
/*     Various Utilities                                                     */
/*===========================================================================*/

/*=== extraUtilBitMatrix.c ================================================================*/

typedef struct Extra_BitMat_t_ Extra_BitMat_t;
extern Extra_BitMat_t * Extra_BitMatrixStart( int nSize );
extern void         Extra_BitMatrixClean( Extra_BitMat_t * p );
extern void         Extra_BitMatrixStop( Extra_BitMat_t * p );
extern void         Extra_BitMatrixPrint( Extra_BitMat_t * p );
extern int          Extra_BitMatrixReadSize( Extra_BitMat_t * p );
extern void         Extra_BitMatrixInsert1( Extra_BitMat_t * p, int i, int k );
extern int          Extra_BitMatrixLookup1( Extra_BitMat_t * p, int i, int k );
extern void         Extra_BitMatrixDelete1( Extra_BitMat_t * p, int i, int k );
extern void         Extra_BitMatrixInsert2( Extra_BitMat_t * p, int i, int k );
extern int          Extra_BitMatrixLookup2( Extra_BitMat_t * p, int i, int k );
extern void         Extra_BitMatrixDelete2( Extra_BitMat_t * p, int i, int k );
extern void         Extra_BitMatrixOr( Extra_BitMat_t * p, int i, unsigned * pInfo );
extern void         Extra_BitMatrixOrTwo( Extra_BitMat_t * p, int i, int j );
extern int          Extra_BitMatrixCountOnesUpper( Extra_BitMat_t * p );
extern int          Extra_BitMatrixIsDisjoint( Extra_BitMat_t * p1, Extra_BitMat_t * p2 );
extern int          Extra_BitMatrixIsClique( Extra_BitMat_t * p );

/*=== extraUtilFile.c ========================================================*/

extern char *       Extra_FileGetSimilarName( char * pFileNameWrong, char * pS1, char * pS2, char * pS3, char * pS4, char * pS5 );
extern char *       Extra_FileNameExtension( char * FileName );
extern char *       Extra_FileNameAppend( char * pBase, char * pSuffix );
extern char *       Extra_FileNameGeneric( char * FileName );
extern char *       Extra_FileNameGenericAppend( char * pBase, char * pSuffix );
extern void         Extra_FileNameCorrectPath( char * FileName );
extern char *       Extra_FileNameWithoutPath( char * FileName );
extern char *       Extra_FilePathWithoutName( char * FileName );
extern char *       Extra_FileDesignName( char * pFileName );
extern int          Extra_FileCheck( char * pFileName );
extern int          Extra_FileSize( char * pFileName );
extern char *       Extra_FileRead( FILE * pFile );
extern char *       Extra_FileRead2( FILE * pFile, FILE * pFile2 );
extern char *       Extra_FileReadContents( char * pFileName );
extern char *       Extra_FileReadContents2( char * pFileName, char * pFileName2 );
extern int          Extra_FileIsType( char * pFileName, char * pS1, char * pS2, char * pS3 );
extern char *       Extra_TimeStamp();
extern char *       Extra_StringAppend( char * pStrGiven, char * pStrAdd );
extern void         Extra_StringClean( char * pStrGiven, char * pCharKeep );
extern unsigned     Extra_ReadBinary( char * Buffer );
extern void         Extra_PrintBinary( FILE * pFile, unsigned Sign[], int nBits );
extern void         Extra_PrintBinary2( FILE * pFile, unsigned Sign[], int nBits );
extern int          Extra_ReadHex( unsigned Sign[], char * pString, int nDigits );
extern int          Extra_ReadHexadecimal( unsigned Sign[], char * pString, int nVars );
extern void         Extra_PrintHexadecimal( FILE * pFile, unsigned Sign[], int nVars );
extern void         Extra_PrintHexadecimalString( char * pString, unsigned Sign[], int nVars );
extern void         Extra_PrintHex( FILE * pFile, unsigned * pTruth, int nVars );
extern void         Extra_PrintHex2( FILE * pFile, unsigned * pTruth, int nVars );
extern void         Extra_PrintHexReverse( FILE * pFile, unsigned * pTruth, int nVars );
extern void         Extra_PrintSymbols( FILE * pFile, char Char, int nTimes, int fPrintNewLine );

/*=== extraUtilReader.c ========================================================*/

typedef struct Extra_FileReader_t_ Extra_FileReader_t;
extern Extra_FileReader_t * Extra_FileReaderAlloc( char * pFileName, 
    char * pCharsComment, char * pCharsStop, char * pCharsClean );
extern void         Extra_FileReaderFree( Extra_FileReader_t * p );
extern char *       Extra_FileReaderGetFileName( Extra_FileReader_t * p );
extern int          Extra_FileReaderGetFileSize( Extra_FileReader_t * p );
extern int          Extra_FileReaderGetCurPosition( Extra_FileReader_t * p );
extern void *       Extra_FileReaderGetTokens( Extra_FileReader_t * p );
extern int          Extra_FileReaderGetLineNumber( Extra_FileReader_t * p, int iToken );

/*=== extraUtilMemory.c ========================================================*/

typedef struct Extra_MmFixed_t_    Extra_MmFixed_t;    
typedef struct Extra_MmFlex_t_     Extra_MmFlex_t;     
typedef struct Extra_MmStep_t_     Extra_MmStep_t;     

// fixed-size-block memory manager
extern Extra_MmFixed_t *  Extra_MmFixedStart( int nEntrySize );
extern void        Extra_MmFixedStop( Extra_MmFixed_t * p );
extern char *      Extra_MmFixedEntryFetch( Extra_MmFixed_t * p );
extern void        Extra_MmFixedEntryRecycle( Extra_MmFixed_t * p, char * pEntry );
extern void        Extra_MmFixedRestart( Extra_MmFixed_t * p );
extern int         Extra_MmFixedReadMemUsage( Extra_MmFixed_t * p );
extern int         Extra_MmFixedReadMaxEntriesUsed( Extra_MmFixed_t * p );
// flexible-size-block memory manager
extern Extra_MmFlex_t * Extra_MmFlexStart();
extern void        Extra_MmFlexStop( Extra_MmFlex_t * p );
extern void        Extra_MmFlexPrint( Extra_MmFlex_t * p );
extern char *      Extra_MmFlexEntryFetch( Extra_MmFlex_t * p, int nBytes );
extern int         Extra_MmFlexReadMemUsage( Extra_MmFlex_t * p );
// hierarchical memory manager
extern Extra_MmStep_t * Extra_MmStepStart( int nSteps );
extern void        Extra_MmStepStop( Extra_MmStep_t * p );
extern char *      Extra_MmStepEntryFetch( Extra_MmStep_t * p, int nBytes );
extern void        Extra_MmStepEntryRecycle( Extra_MmStep_t * p, char * pEntry, int nBytes );
extern int         Extra_MmStepReadMemUsage( Extra_MmStep_t * p );

/*=== extraUtilMisc.c ========================================================*/

/* finds the smallest integer larger or equal than the logarithm */
extern int         Extra_Base2LogDouble( double Num );
/* returns the power of two as a double */
extern double      Extra_Power2( int Num );
extern int         Extra_Power3( int Num );
/* the number of combinations of k elements out of n */
extern int         Extra_NumCombinations( int k, int n  );
extern int *       Extra_DeriveRadixCode( int Number, int Radix, int nDigits );
/* counts the number of 1s in the bitstring */
extern int         Extra_CountOnes( unsigned char * pBytes, int nBytes );
/* the factorial of number */
extern int         Extra_Factorial( int n );
/* the permutation of the given number of elements */
extern char **     Extra_Permutations( int n );
/* permutation and complementation of a truth table */
unsigned           Extra_TruthPermute( unsigned Truth, char * pPerms, int nVars, int fReverse );
unsigned           Extra_TruthPolarize( unsigned uTruth, int Polarity, int nVars );
/* canonical forms of a truth table */
extern unsigned    Extra_TruthCanonN( unsigned uTruth, int nVars );
extern unsigned    Extra_TruthCanonNN( unsigned uTruth, int nVars );
extern unsigned    Extra_TruthCanonP( unsigned uTruth, int nVars );
extern unsigned    Extra_TruthCanonNP( unsigned uTruth, int nVars );
extern unsigned    Extra_TruthCanonNPN( unsigned uTruth, int nVars );
/* canonical forms of 4-variable functions */
extern void        Extra_Truth4VarNPN( unsigned short ** puCanons, char ** puPhases, char ** puPerms, unsigned char ** puMap );
extern void        Extra_Truth4VarN( unsigned short ** puCanons, char *** puPhases, char ** ppCounters, int nPhasesMax );
/* permutation mapping */
extern unsigned short Extra_TruthPerm4One( unsigned uTruth, int Phase );
extern unsigned    Extra_TruthPerm5One( unsigned uTruth, int Phase );
extern void        Extra_TruthPerm6One( unsigned * uTruth, int Phase, unsigned * uTruthRes );
extern void        Extra_TruthExpand( int nVars, int nWords, unsigned * puTruth, unsigned uPhase, unsigned * puTruthR );
/* precomputing tables for permutation mapping */
extern void **     Extra_ArrayAlloc( int nCols, int nRows, int Size );
extern unsigned short ** Extra_TruthPerm43();
extern unsigned ** Extra_TruthPerm53();
extern unsigned ** Extra_TruthPerm54();
/* bubble sort for small number of entries */
extern void        Extra_BubbleSort( int Order[], int Costs[], int nSize, int fIncreasing );
/* complementation/permutation generation */
extern int *       Extra_GreyCodeSchedule( int n );
extern int *       Extra_PermSchedule( int n );
extern word        Extra_Truth6MinimumExact( word t, int * pComp, int * pPerm );
extern word        Extra_Truth6MinimumHeuristic( word t );

/*=== extraUtilCanon.c ========================================================*/

/* fast computation of N-canoninical form up to 6 inputs */
extern int         Extra_TruthCanonFastN( int nVarsMax, int nVarsReal, unsigned * pt, unsigned ** pptRes, char ** ppfRes );

/*=== extraUtilDsd.c ========================================================*/

typedef struct Sdm_Man_t_ Sdm_Man_t; 
extern int         Sdm_ManCanRead();
extern Sdm_Man_t * Sdm_ManRead();
extern void        Sdm_ManQuit();
extern int         Sdm_ManComputeFunc( Sdm_Man_t * p, int iDsdLit0, int iDsdLit1, int * pCut, int uMask, int fXor );
extern void        Sdm_ManPrintDsdStats( Sdm_Man_t * p, int fVerbose );
extern int         Sdm_ManReadDsdVarNum( Sdm_Man_t * p, int iDsd );
extern int         Sdm_ManReadDsdAndNum( Sdm_Man_t * p, int iDsd );
extern int         Sdm_ManReadDsdClauseNum( Sdm_Man_t * p, int iDsd );
extern word        Sdm_ManReadDsdTruth( Sdm_Man_t * p, int iDsd );
extern char *      Sdm_ManReadDsdStr( Sdm_Man_t * p, int iDsd );
extern void        Sdm_ManReadCnfCosts( Sdm_Man_t * p, int * pCosts, int nCosts );

/*=== extraUtilProgress.c ================================================================*/

typedef struct ProgressBarStruct ProgressBar;

extern ProgressBar * Extra_ProgressBarStart( FILE * pFile, int nItemsTotal );
extern void        Extra_ProgressBarStop( ProgressBar * p );
extern void        Extra_ProgressBarUpdate_int( ProgressBar * p, int nItemsCur, char * pString );

static inline void Extra_ProgressBarUpdate( ProgressBar * p, int nItemsCur, char * pString ) 
{  if ( p && nItemsCur < *((int*)p) ) return; Extra_ProgressBarUpdate_int(p, nItemsCur, pString); }

/*=== extraUtilTruth.c ================================================================*/

static inline int   Extra_BitWordNum( int nBits )    { return nBits/(8*sizeof(unsigned)) + ((nBits%(8*sizeof(unsigned))) > 0);  }
static inline int   Extra_TruthWordNum( int nVars )  { return nVars <= 5 ? 1 : (1 << (nVars - 5)); }

static inline void  Extra_TruthSetBit( unsigned * p, int Bit )   { p[Bit>>5] |= (unsigned)(1<<(Bit & 31));               }
static inline void  Extra_TruthXorBit( unsigned * p, int Bit )   { p[Bit>>5] ^= (unsigned)(1<<(Bit & 31));               }
static inline int   Extra_TruthHasBit( unsigned * p, int Bit )   { return (p[Bit>>5] & (unsigned)(1<<(Bit & 31))) > 0;   }

static inline int Extra_WordCountOnes( unsigned uWord )
{
    uWord = (uWord & 0x55555555) + ((uWord>>1) & 0x55555555);
    uWord = (uWord & 0x33333333) + ((uWord>>2) & 0x33333333);
    uWord = (uWord & 0x0F0F0F0F) + ((uWord>>4) & 0x0F0F0F0F);
    uWord = (uWord & 0x00FF00FF) + ((uWord>>8) & 0x00FF00FF);
    return  (uWord & 0x0000FFFF) + (uWord>>16);
}
static inline int Extra_TruthCountOnes( unsigned * pIn, int nVars )
{
    int w, Counter = 0;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        Counter += Extra_WordCountOnes(pIn[w]);
    return Counter;
}
static inline int Extra_TruthIsEqual( unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        if ( pIn0[w] != pIn1[w] )
            return 0;
    return 1;
}
static inline int Extra_TruthIsConst0( unsigned * pIn, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        if ( pIn[w] )
            return 0;
    return 1;
}
static inline int Extra_TruthIsConst1( unsigned * pIn, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        if ( pIn[w] != ~(unsigned)0 )
            return 0;
    return 1;
}
static inline int Extra_TruthIsImply( unsigned * pIn1, unsigned * pIn2, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        if ( pIn1[w] & ~pIn2[w] )
            return 0;
    return 1;
}
static inline void Extra_TruthCopy( unsigned * pOut, unsigned * pIn, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = pIn[w];
}
static inline void Extra_TruthClear( unsigned * pOut, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = 0;
}
static inline void Extra_TruthFill( unsigned * pOut, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = ~(unsigned)0;
}
static inline void Extra_TruthNot( unsigned * pOut, unsigned * pIn, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = ~pIn[w];
}
static inline void Extra_TruthAnd( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = pIn0[w] & pIn1[w];
}
static inline void Extra_TruthOr( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = pIn0[w] | pIn1[w];
}
static inline void Extra_TruthSharp( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = pIn0[w] & ~pIn1[w];
}
static inline void Extra_TruthNand( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars )
{
    int w;
    for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
        pOut[w] = ~(pIn0[w] & pIn1[w]);
}
static inline void Extra_TruthAndPhase( unsigned * pOut, unsigned * pIn0, unsigned * pIn1, int nVars, int fCompl0, int fCompl1 )
{
    int w;
    if ( fCompl0 && fCompl1 )
    {
        for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
            pOut[w] = ~(pIn0[w] | pIn1[w]);
    }
    else if ( fCompl0 && !fCompl1 )
    {
        for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
            pOut[w] = ~pIn0[w] & pIn1[w];
    }
    else if ( !fCompl0 && fCompl1 )
    {
        for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
            pOut[w] = pIn0[w] & ~pIn1[w];
    }
    else // if ( !fCompl0 && !fCompl1 )
    {
        for ( w = Extra_TruthWordNum(nVars)-1; w >= 0; w-- )
            pOut[w] = pIn0[w] & pIn1[w];
    }
}

extern unsigned ** Extra_TruthElementary( int nVars );
extern void        Extra_TruthSwapAdjacentVars( unsigned * pOut, unsigned * pIn, int nVars, int Start );
extern void        Extra_TruthStretch( unsigned * pOut, unsigned * pIn, int nVars, int nVarsAll, unsigned Phase );
extern void        Extra_TruthShrink( unsigned * pOut, unsigned * pIn, int nVars, int nVarsAll, unsigned Phase );
extern int         Extra_TruthVarInSupport( unsigned * pTruth, int nVars, int iVar );
extern int         Extra_TruthSupportSize( unsigned * pTruth, int nVars );
extern int         Extra_TruthSupport( unsigned * pTruth, int nVars );
extern void        Extra_TruthCofactor0( unsigned * pTruth, int nVars, int iVar );
extern void        Extra_TruthCofactor1( unsigned * pTruth, int nVars, int iVar );
extern void        Extra_TruthExist( unsigned * pTruth, int nVars, int iVar );
extern void        Extra_TruthForall( unsigned * pTruth, int nVars, int iVar );
extern void        Extra_TruthMux( unsigned * pOut, unsigned * pCof0, unsigned * pCof1, int nVars, int iVar );
extern void        Extra_TruthChangePhase( unsigned * pTruth, int nVars, int iVar );
extern int         Extra_TruthMinCofSuppOverlap( unsigned * pTruth, int nVars, int * pVarMin );
extern void        Extra_TruthCountOnesInCofs( unsigned * pTruth, int nVars, short * pStore );
extern unsigned    Extra_TruthHash( unsigned * pIn, int nWords );
extern unsigned    Extra_TruthSemiCanonicize( unsigned * pInOut, unsigned * pAux, int nVars, char * pCanonPerm, short * pStore );

/*=== extraUtilUtil.c ================================================================*/

extern abctime       Extra_CpuTime();
extern double        Extra_CpuTimeDouble();
extern int           Extra_GetSoftDataLimit();
extern ABC_DLL void  Extra_UtilGetoptReset();
extern int           Extra_UtilGetopt( int argc, char *argv[], const char *optstring );
extern char *        Extra_UtilPrintTime( long t );
extern char *        Extra_UtilStrsav( const char *s );
extern char *        Extra_UtilTildeExpand( char *fname );
extern char *        Extra_UtilFileSearch( char *file, char *path, char *mode );
extern void          (*Extra_UtilMMoutOfMemory)( long size );

extern const char *  globalUtilOptarg;
extern int           globalUtilOptind;

/*=== extraUtilMult.c ================================================================*/

typedef struct Abc_BddMan_ Abc_BddMan;
struct Abc_BddMan_ 
{
  int                nVars;         // the number of variables
  int                nObjs;         // the number of nodes used
  unsigned           nObjsAlloc;    // the number of nodes allocated
  int *              pUnique;       // unique table for nodes
  int *              pNexts;        // next pointer for nodes
  unsigned *         pCache;        // array of triples <arg0, arg1, AND(arg0, arg1)>
  unsigned *         pObjs;         // array of pairs cof0 for each node
  unsigned char *    pVars;         // array of variables for each node
  unsigned char *    pMarks;        // array of marks for each BDD node
  unsigned           nUniqueMask;   // selection mask for unique table
  unsigned           nCacheMask;    // selection mask for computed table
  int                nMinRemoved;   // the minimum int of removed nodes
  int                nVerbose;      // the level of verbosing information

  unsigned short *   pSVars;        // array of variables for each node for more than 255 variables
  
  int                fGC;           // flag to garbage collect
  int                fRealloc;      // flag to reallocate
  Vec_Int_t *        pFrontiers;    // vector of frontier nodes
  
  float              ReoThold;      // threshold to terminate reordering. 0=off.
  unsigned *         pEdges;        // array of number of incoming edges for each BDD node. used for reordering
  Vec_Int_t **       liveBvars;     // array of live bvars for each layer. used for reordering
};

// Var = Variable, Lit = Literal, Bvar = BddVariable = Lit >> 1 
static inline unsigned Abc_BddHash( int Arg0, int Arg1, int Arg2 ) { return 12582917 * Arg0 + 4256249 * Arg1 + 741457 * Arg2; }
static inline int      Abc_BddBvarConst()                          { return 0;                            }
static inline int      Abc_BddVarConst( Abc_BddMan * p )           { return ( p->pVars )? 0xff: 0xffff ;  }
static inline int      Abc_BddBvarInvalid()                        { return 0x7fffffff;                   }
static inline unsigned Abc_BddEdgeInvalid()                        { return 0xffffffff;                   }
static inline int      Abc_BddMarkInvalid()                        { return 0xff;                         }
static inline int      Abc_BddVarRemoved( Abc_BddMan * p )         { return ( p->pVars )? 0xff: 0xffff;   }

static inline int      Abc_BddBvarIsEq( int a, int b )             { return a == b;                       }
static inline int      Abc_BddBvarIsConst( int a )                 { return Abc_BddBvarIsEq( a, Abc_BddBvarConst() ); }
static inline int      Abc_BddBvarIsInvalid( int a )               { return Abc_BddBvarIsEq( a, Abc_BddBvarInvalid() ); }

static inline unsigned Abc_BddBvar2Lit( int a, int c )             { return a + a + (int)( c > 0 );       }
static inline int      Abc_BddLit2Bvar( unsigned x )               { return x >> 1;                       }
static inline unsigned Abc_BddBvarIthVar( int a )                  { return a + 1;                        }
static inline unsigned Abc_BddLitIthVar( int a )                   { return Abc_BddBvar2Lit( Abc_BddBvarIthVar( a ), 0 ); }

static inline unsigned Abc_BddLitRegular( unsigned x )             { return x & ~01;                      }
static inline unsigned Abc_BddLitNot( unsigned x )                 { return x ^ 1;                        }
static inline unsigned Abc_BddLitNotCond( unsigned x, int c )      { return x ^ (int)( c > 0 );           }
static inline unsigned Abc_BddLitConst0()                          { return Abc_BddBvar2Lit( Abc_BddBvarConst(), 0 ); }
static inline unsigned Abc_BddLitConst1()                          { return Abc_BddLitNot( Abc_BddLitConst0() ); }
static inline unsigned Abc_BddLitInvalid()                         { return Abc_BddBvar2Lit( Abc_BddBvarInvalid(), 0 ); }
static inline int      Abc_BddLitIsCompl( unsigned x )             { return x & 1;                        }
static inline int      Abc_BddLitIsEq( unsigned x, unsigned y )    { return x == y;                       }
static inline int      Abc_BddLitIsConst0( unsigned x )            { return Abc_BddLitIsEq( x, Abc_BddLitConst0() ); }
static inline int      Abc_BddLitIsConst1( unsigned x )            { return Abc_BddLitIsEq( x, Abc_BddLitConst1() ); }
static inline int      Abc_BddLitIsConst( unsigned x )             { return Abc_BddBvarIsConst( Abc_BddLit2Bvar( x ) ); }
static inline int      Abc_BddLitIsInvalid( unsigned x )           { return Abc_BddBvarIsInvalid( Abc_BddLit2Bvar( x ) ); }

static inline int      Abc_BddBvarIsRemoved( Abc_BddMan * p, int a ) { return (( p->pVars )? p->pVars[a]: p->pSVars[a]) == Abc_BddVarRemoved( p ); }
static inline void     Abc_BddSetBvarRemoved( Abc_BddMan * p, int a ) { if ( p->pVars ) p->pVars[a] = Abc_BddVarRemoved( p ); else p->pSVars[a] = Abc_BddVarRemoved( p ); }

static inline int      Abc_BddVar( Abc_BddMan * p, unsigned x )    { return ( p->pVars )? p->pVars[Abc_BddLit2Bvar( x )]: p->pSVars[Abc_BddLit2Bvar( x )]; }
static inline unsigned Abc_BddThen( Abc_BddMan * p, unsigned x )   { return Abc_BddLitNotCond( p->pObjs[Abc_BddLitRegular( x )], Abc_BddLitIsCompl( x ) ); }
static inline unsigned Abc_BddElse( Abc_BddMan * p, unsigned x )   { return Abc_BddLitNotCond( p->pObjs[Abc_BddLitNot( Abc_BddLitRegular( x ) )], Abc_BddLitIsCompl( x ) ); }
static inline int      Abc_BddNext( Abc_BddMan * p, unsigned x )   { return p->pNexts[Abc_BddLit2Bvar( x )]; }
static inline int      Abc_BddMark( Abc_BddMan * p, unsigned x )   { return p->pMarks[Abc_BddLit2Bvar( x )]; }
static inline unsigned Abc_BddEdge( Abc_BddMan * p, unsigned x )   { return p->pEdges[Abc_BddLit2Bvar( x )]; }

static inline int      Abc_BddVarOfBvar( Abc_BddMan * p, int a )   { return ( p->pVars )? p->pVars[a]: p->pSVars[a]; }
static inline unsigned Abc_BddThenOfBvar( Abc_BddMan * p, int a )  { return p->pObjs[Abc_BddBvar2Lit( a, 0 )]; }
static inline unsigned Abc_BddElseOfBvar( Abc_BddMan * p, int a )  { return p->pObjs[Abc_BddBvar2Lit( a, 1 )]; }
static inline int      Abc_BddNextOfBvar( Abc_BddMan * p, int a )  { return p->pNexts[a];                 }
static inline int      Abc_BddMarkOfBvar( Abc_BddMan * p, int a )  { return p->pMarks[a];                 }
static inline unsigned Abc_BddEdgeOfBvar( Abc_BddMan * p, int a )  { return p->pEdges[a];                 }

static inline void     Abc_BddSetVarOfBvar( Abc_BddMan * p, int a, int Var ) { if ( p->pVars ) p->pVars[a] = Var; else p->pSVars[a] = Var; }
static inline void     Abc_BddSetThenOfBvar( Abc_BddMan * p, int a, unsigned Then ) { p->pObjs[Abc_BddBvar2Lit( a, 0 )] = Then; }
static inline void     Abc_BddSetElseOfBvar( Abc_BddMan * p, int a, unsigned Else ) { p->pObjs[Abc_BddBvar2Lit( a, 1 )] = Else; }
static inline void     Abc_BddSetNextOfBvar( Abc_BddMan * p, int a, int Next ) { p->pNexts[a] = Next;     }
static inline void     Abc_BddSetMarkOfBvar( Abc_BddMan * p, int a, int Mark ) { p->pMarks[a] = Mark;     }
static inline void     Abc_BddSetEdgeOfBvar( Abc_BddMan * p, int a, int Edge ) { p->pEdges[a] = Edge;     }

static inline void     Abc_BddSetMark( Abc_BddMan * p, unsigned x, int m ) { p->pMarks[Abc_BddLit2Bvar( x )] = m; }
static inline void     Abc_BddIncMark( Abc_BddMan * p, unsigned x ) { assert( ++p->pMarks[Abc_BddLit2Bvar( x )] != Abc_BddMarkInvalid() ); }
static inline void     Abc_BddDecMark( Abc_BddMan * p, unsigned x ) { assert( --p->pMarks[Abc_BddLit2Bvar( x )] != Abc_BddMarkInvalid() ); }

static inline void     Abc_BddIncEdge( Abc_BddMan * p, unsigned x ) { assert( ++p->pEdges[Abc_BddLit2Bvar( x )] != Abc_BddEdgeInvalid() ); }
static inline void     Abc_BddDecEdge( Abc_BddMan * p, unsigned x ) { assert( --p->pEdges[Abc_BddLit2Bvar( x )] != Abc_BddEdgeInvalid() ); }
static inline void     Abc_BddIncEdgeNonConst( Abc_BddMan * p, unsigned x) { if ( !Abc_BddLitIsConst( x ) ) Abc_BddIncEdge( p, x ); }
static inline void     Abc_BddDecEdgeNonConst( Abc_BddMan * p, unsigned x) { if ( !Abc_BddLitIsConst( x ) ) Abc_BddDecEdge( p, x ); }

static inline int      Abc_BddIsLimit( Abc_BddMan * p ) { return (unsigned)p->nObjs == p->nObjsAlloc || p->nObjs == Abc_BddBvarInvalid(); }

extern unsigned        Abc_BddUniqueCreate( Abc_BddMan * p, int Var, unsigned Then, unsigned Else );
extern Abc_BddMan *    Abc_BddManAlloc( int nVars, unsigned nObjs, int fDynAlloc, int fVerbose );
extern void            Abc_BddManRealloc( Abc_BddMan * p );
extern void            Abc_BddManFree( Abc_BddMan * p );
extern unsigned        Abc_BddAnd( Abc_BddMan * p, unsigned x, unsigned y );
extern unsigned        Abc_BddOr( Abc_BddMan * p, unsigned x, unsigned y );
extern unsigned        Abc_BddXnor( Abc_BddMan * p, unsigned x, unsigned y );
extern void            Abc_BddUnmark_rec( Abc_BddMan * p, unsigned x );
extern int             Abc_BddCountNodesArrayShared( Abc_BddMan * p, Vec_Int_t * vNodes );
extern int             Abc_BddCountNodesArrayIndependent( Abc_BddMan * p, Vec_Int_t * vNodes );
extern void            Abc_BddRemoveNodeByBvar( Abc_BddMan * p, int a );
extern void            Abc_BddGarbageCollect( Abc_BddMan * p, Vec_Int_t * pFrontiers );
extern void            Abc_BddGiaCountFanout( Gia_Man_t * pGia, int * pFanouts );
extern void            Abc_BddGiaRefreshConfig( Abc_BddMan * p, int fRealloc, int fGC, int nReorderThreshold );
extern int             Abc_BddGia( Gia_Man_t * pGia, Abc_BddMan * p );
extern Gia_Man_t *     Abc_BddGenGia( Abc_BddMan * p, Vec_Int_t * vNodes );
extern void            Abc_BddWriteBlif( Abc_BddMan * p, Vec_Int_t * vNodes, char * pFileName, int fName );  
extern unsigned        Abc_BddUnivAbstract( Abc_BddMan * p, unsigned x, Vec_Int_t * vVars );

/*=== extraUtilReorder.c ================================================================*/

extern void            Abc_BddReorder( Abc_BddMan * p, Vec_Int_t * pFunctions, int fVerbose );

/*=== extraUtilVc.c ================================================================*/

extern unsigned        Abc_BddIteAnd( Abc_BddMan * p, unsigned c, unsigned d1, unsigned d0 );
extern unsigned        Abc_BddVectorCompose( Abc_BddMan * p, unsigned F,  Vec_Int_t * Vars, unsigned * cache, int fAnd );

/**AutomaticEnd***************************************************************/



ABC_NAMESPACE_HEADER_END



#endif /* __EXTRA_H__ */
