/**CFile****************************************************************

  FileName    [pdrCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdrCore.c,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdrInt.h"
#include "base/main/main.h"
#include "misc/hash/hash.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern int Gia_ManToBridgeResult(FILE *pFile, int Result, Abc_Cex_t *pCex, int iPoProved);
extern int Gia_ManToBridgeAbort(FILE *pFile, int Size, unsigned char *pBuffer);

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the symmetric cube for a given cube.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t *Pdr_ManSymmetricCube(Pdr_Man_t *p, Pdr_Set_t *pCube)
{
    Pdr_Set_t *pCubeSym;

    int i, RegId, SymReg, cubeDiff = 0;

    pCubeSym = (Pdr_Set_t *)ABC_ALLOC(char, sizeof(Pdr_Set_t) + (pCube->nLits) * sizeof(int));
    pCubeSym->nLits = pCube->nLits;
    pCubeSym->nTotal = pCube->nLits;
    pCubeSym->nRefs = 1;
    pCubeSym->Sign = 0;

    for (i = 0; i < pCube->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCube->Lits[i]);
        assert(RegId < Vec_IntSize(p->vSymMap) && 0 <= RegId);
        // We don't handle the case where the literal corresponds to a non-register
        // assert(RegId != -1);
        // Abc_Print(0, "Original RegId: %d\n", RegId);
        SymReg = Vec_IntEntry(p->vSymMap, RegId);
        // Abc_Print(0, "Symmetric RegId: %d\n", RegId);
        pCubeSym->Lits[i] = Abc_Var2Lit(SymReg, Abc_LitIsCompl(pCube->Lits[i]));
        pCubeSym->Sign |= ((word)1) << (pCubeSym->Lits[i] % 63);
    }

    for (i = 0; i < pCube->nLits; i++)
    {
        if (pCube->Lits[i] != pCubeSym->Lits[i])
        {
            cubeDiff = 1;
            break;
        }
    }

    // Vec_IntSelectSort(pCubeSym->Lits, pCubeSym->nLits);

    if (cubeDiff)
    {
        // Abc_Print(1, "Diifferent cube\n");
        return pCubeSym;
    }
    else
    {
        // Abc_Print(1, "No Diifferent cube\n");
        Pdr_SetDeref(pCubeSym);
        return NULL;
    }
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the state could be blocked.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManSetDefaultParams(Pdr_Par_t *pPars)
{
    memset(pPars, 0, sizeof(Pdr_Par_t));
    //    pPars->iOutput        =      -1;  // zero-based output number
    pPars->nRecycle = 300;         // limit on vars for recycling
    pPars->nFrameMax = 10000;      // limit on number of timeframes
    pPars->nTimeOut = 0;           // timeout in seconds
    pPars->nTimeOutGap = 0;        // timeout in seconds since the last solved
    pPars->nConfLimit = 0;         // limit on SAT solver conflicts
    pPars->nConfGenLimit = 0;      // limit on SAT solver conflicts during generalization
    pPars->nRestLimit = 0;         // limit on the number of proof-obligations
    pPars->nRandomSeed = 91648253; // value to seed the SAT solver with
    pPars->fTwoRounds = 0;         // use two rounds for generalization
    pPars->fMonoCnf = 0;           // monolythic CNF
    pPars->fNewXSim = 0;           // updated X-valued simulation
    pPars->fFlopPrio = 0;          // use structural flop priorities
    pPars->fFlopOrder = 0;         // order flops for 'analyze_final' during generalization
    pPars->fDumpInv = 0;           // dump inductive invariant
    pPars->fUseSupp = 1;           // using support variables in the invariant
    pPars->fShortest = 0;          // forces bug traces to be shortest
    pPars->fUsePropOut = 1;        // use property output
    pPars->fSkipDown = 1;          // apply down in generalization
    pPars->fCtgs = 0;              // handle CTGs in down
    pPars->fUseAbs = 0;            // use abstraction
    pPars->fUseSimpleRef = 0;      // simplified CEX refinement
    pPars->fVerbose = 0;           // verbose output
    pPars->fVeryVerbose = 0;       // very verbose output
    pPars->fNotVerbose = 0;        // not printing line-by-line progress
    pPars->iFrame = -1;            // explored up to this frame
    pPars->nFailOuts = 0;          // the number of disproved outputs
    pPars->nDropOuts = 0;          // the number of timed out outputs
    pPars->timeLastSolved = 0;     // last one solved
    pPars->fUseSymmetry = 0;
    pPars->fPredicateReplace = 0;
    pPars->fIterativePredicate = 0;
    pPars->pInvFileName = NULL; // invariant file name
    pPars->pPriFileName = NULL; // priority file name
    pPars->pRelFileName = NULL; // Relation file name
}

/**Function*************************************************************

  Synopsis    [Reduces clause using analyzeFinal.]

  Description [Assumes that the SAT solver just terminated an UNSAT call.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t *Pdr_ManReduceClause(Pdr_Man_t *p, int k, Pdr_Set_t *pCube)
{
    Pdr_Set_t *pCubeMin;
    Vec_Int_t *vLits;
    int i, Entry, nCoreLits, *pCoreLits;
    // get relevant SAT literals
    nCoreLits = sat_solver_final(Pdr_ManSolver(p, k), &pCoreLits);
    // translate them into register literals and remove auxiliary
    vLits = Pdr_ManLitsToCube(p, k, pCoreLits, nCoreLits);
    // skip if there is no improvement
    if (Vec_IntSize(vLits) == pCube->nLits)
        return NULL;
    assert(Vec_IntSize(vLits) < pCube->nLits);
    // if the cube overlaps with init, add any literal
    Vec_IntForEachEntry(vLits, Entry, i) if (Abc_LitIsCompl(Entry) == 0) // positive literal
        break;
    if (i == Vec_IntSize(vLits)) // only negative literals
    {
        // add the first positive literal
        for (i = 0; i < pCube->nLits; i++)
            if (Abc_LitIsCompl(pCube->Lits[i]) == 0) // positive literal
            {
                Vec_IntPush(vLits, pCube->Lits[i]);
                break;
            }
        assert(i < pCube->nLits);
    }
    // generate a starting cube
    pCubeMin = Pdr_SetCreateSubset(pCube, Vec_IntArray(vLits), Vec_IntSize(vLits));
    assert(!Pdr_SetIsInit(pCubeMin, -1));
    /*
        // make sure the cube works
        {
        int RetValue;
        RetValue = Pdr_ManCheckCube( p, k, pCubeMin, NULL, 0, 0, 1 );
        assert( RetValue );
        }
    */
    return pCubeMin;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the state could be blocked.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManPushClauses(Pdr_Man_t *p)
{
    Pdr_Set_t *pTemp, *pCubeK, *pCubeK1, *pCubeKSym, *pCubePred;
    Vec_Ptr_t *vArrayK, *vArrayK1;
    int i, j, k, m, RetValue = 0, RetValue2, RetValue3, kMax = Vec_PtrSize(p->vSolvers) - 1;
    int iStartFrame = p->pPars->fShiftStart ? p->iUseFrame : 1;
    int Counter = 0;
    pCubeKSym = NULL;
    abctime clk = Abc_Clock();
    assert(p->iUseFrame > 0);
    Vec_VecForEachLevelStartStop(p->vClauses, vArrayK, k, iStartFrame, kMax)
    {
        Vec_PtrSort(vArrayK, (int (*)(const void *, const void *))Pdr_SetCompare);
        vArrayK1 = Vec_VecEntry(p->vClauses, k + 1);
        Vec_PtrForEachEntry(Pdr_Set_t *, vArrayK, pCubeK, j)
        {
            Counter++;

            // remove cubes in the same frame that are contained by pCubeK
            Vec_PtrForEachEntryStart(Pdr_Set_t *, vArrayK, pTemp, m, j + 1)
            {
                if (!Pdr_SetContains(pTemp, pCubeK)) // pCubeK contains pTemp
                    continue;
                // if (p->pPars->fVeryVerbose){
                //     Abc_Print(1, "cube ");
                //     Pdr_SetPrint(stdout, pCubeK, Aig_ManRegNum(p->pAig), NULL);
                //     Abc_Print(1, "\n");
                //     Abc_Print(1, "subsumes cube ");
                //     Pdr_SetPrint(stdout, pTemp, Aig_ManRegNum(p->pAig), NULL);
                //     Abc_Print(1, "\n");
                // }
                Pdr_SetDeref(pTemp);
                Vec_PtrWriteEntry(vArrayK, m, Vec_PtrEntryLast(vArrayK));
                Vec_PtrPop(vArrayK);
                m--;
            }

            // check if the clause can be moved to the next frame
            RetValue2 = Pdr_ManCheckCube(p, k, pCubeK, &pCubePred, 0, 0, 1);
            if (RetValue2 == -1)
                return -1;

            if (!RetValue2)
            {
                continue;
            }

            {
                Pdr_Set_t *pCubeMin;
                pCubeMin = Pdr_ManReduceClause(p, k, pCubeK);
                if (pCubeMin != NULL)
                {
                    //                Abc_Print( 1, "%d ", pCubeK->nLits - pCubeMin->nLits );
                    // if (p->pPars->fVeryVerbose){
                    //     Abc_Print(1, "cube ");
                    //     Pdr_SetPrint(stdout, pCubeK, Aig_ManRegNum(p->pAig), NULL);
                    //     Abc_Print(1, "\nis reduced to cube ");
                    //     Pdr_SetPrint(stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL);
                    //     Abc_Print(1, "\n");
                    // }
                    Pdr_SetDeref(pCubeK);
                    pCubeK = pCubeMin;
                }
            }

            // if it can be moved, add it to the next frame
            // if (p->pPars->fVeryVerbose)
            // {
            //     Abc_Print(1, "Pushing cube ");
            //     Pdr_SetPrint(stdout, pCubeK, Aig_ManRegNum(p->pAig), NULL);
            //     Abc_Print(1, " from frame %d to frame %d.\n", k, k + 1);
            // }

            Pdr_ManSolverAddClause(p, k + 1, pCubeK);

            // check if the clause subsumes others
            Vec_PtrForEachEntry(Pdr_Set_t *, vArrayK1, pCubeK1, i)
            {
                if (!Pdr_SetContains(pCubeK1, pCubeK)) // pCubeK contains pCubeK1
                    continue;
                Pdr_SetDeref(pCubeK1);
                Vec_PtrWriteEntry(vArrayK1, i, Vec_PtrEntryLast(vArrayK1));
                Vec_PtrPop(vArrayK1);
                i--;
            }
            // add the last clause
            Vec_PtrPush(vArrayK1, pCubeK);
            Vec_PtrWriteEntry(vArrayK, j, Vec_PtrEntryLast(vArrayK));
            Vec_PtrPop(vArrayK);
            j--;

            // if (p->pPars->pRelFileName != NULL && p->pPars->fUseSymmetry)
            // {
            //     pCubeKSym = Pdr_ManSymmetricCube(p, pCubeK);
            //     if (pCubeKSym != NULL)
            //     {
            //         RetValue3 = 1;//Pdr_ManCheckCube(p, k, pCubeKSym, &pCubePred, 0, 0, 1);
            //         if (RetValue3 == 0)
            //         {
            //             if (p->pPars->fVeryVerbose)
            //             {

            //                 Abc_Print(1, "symmetric cube ");
            //                 Pdr_SetPrint(stdout, pCubeKSym, Aig_ManRegNum(p->pAig), NULL);
            //                 Abc_Print(1, " cannot be pushed from frame %d to frame %d.\n", k, k + 1);
            //                 Abc_Print(1, "cex cube ");
            //                 Pdr_SetPrint(stdout, pCubePred, Aig_ManRegNum(p->pAig), NULL);
            //                 Abc_Print(1, " at frame %d\n", k);
            //                 Pdr_ManPrintClauses(p, 0);
            //                 return -1;
            //             }
            //         }
            //         Pdr_ManSolverAddClause(p, k + 1, pCubeKSym);
            //         Vec_PtrForEachEntry(Pdr_Set_t *, vArrayK1, pCubeK1, i)
            //         {
            //             if (!Pdr_SetContains(pCubeK1, pCubeKSym)) // pCubeK contains pCubeK1
            //                 continue;
            //             Pdr_SetDeref(pCubeK1);
            //             Vec_PtrWriteEntry(vArrayK1, i, Vec_PtrEntryLast(vArrayK1));
            //             Vec_PtrPop(vArrayK1);
            //             i--;
            //         }
            //         Vec_PtrPush(vArrayK1, pCubeKSym);

            //         // Pdr_SetDeref(pCubeKSym);

            //     }
            // }
        }
        if (Vec_PtrSize(vArrayK) == 0)
            RetValue = 1;

        // if (k==4){
        //     Pdr_ManPrintClauses(p, 0);
        //     return -1;
        // }
    }

    // clean up the last one
    vArrayK = Vec_VecEntry(p->vClauses, kMax);
    Vec_PtrSort(vArrayK, (int (*)(const void *, const void *))Pdr_SetCompare);
    Vec_PtrForEachEntry(Pdr_Set_t *, vArrayK, pCubeK, j)
    {
        // remove cubes in the same frame that are contained by pCubeK
        Vec_PtrForEachEntryStart(Pdr_Set_t *, vArrayK, pTemp, m, j + 1)
        {
            if (!Pdr_SetContains(pTemp, pCubeK)) // pCubeK contains pTemp
                continue;
            // if (p->pPars->fVeryVerbose)
            // {
            //     Abc_Print(1, "cube ");
            //     Pdr_SetPrint(stdout, pCubeK, Aig_ManRegNum(p->pAig), NULL);
            //     Abc_Print(1, "\n");
            //     Abc_Print(1, "subsumes cube ");
            //     Pdr_SetPrint(stdout, pTemp, Aig_ManRegNum(p->pAig), NULL);
            //     Abc_Print(1, "\n");
            // }
            /*
                        Abc_Print( 1, "===\n" );
                        Pdr_SetPrint( stdout, pCubeK, Aig_ManRegNum(p->pAig), NULL );
                        Abc_Print( 1, "\n" );
                        Pdr_SetPrint( stdout, pTemp, Aig_ManRegNum(p->pAig), NULL );
                        Abc_Print( 1, "\n" );
            */
            Pdr_SetDeref(pTemp);
            Vec_PtrWriteEntry(vArrayK, m, Vec_PtrEntryLast(vArrayK));
            Vec_PtrPop(vArrayK);
            m--;
        }
    }
    p->tPush += Abc_Clock() - clk;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the clause is contained in higher clauses.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManCheckContainment(Pdr_Man_t *p, int k, Pdr_Set_t *pSet)
{
    Pdr_Set_t *pThis;
    Vec_Ptr_t *vArrayK;
    int i, j, kMax = Vec_PtrSize(p->vSolvers) - 1;
    Vec_VecForEachLevelStartStop(p->vClauses, vArrayK, i, k, kMax + 1)
        Vec_PtrForEachEntry(Pdr_Set_t *, vArrayK, pThis, j) if (Pdr_SetContains(pSet, pThis)) return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Sorts literals by priority.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int *Pdr_ManSortByPriority(Pdr_Man_t *p, Pdr_Set_t *pCube)
{
    int *pPrios = Vec_IntArray(p->vPrio);
    int *pArray = p->pOrder;
    int temp, i, j, best_i, nSize = pCube->nLits;
    // initialize variable order
    for (i = 0; i < nSize; i++)
        pArray[i] = i;
    for (i = 0; i < nSize - 1; i++)
    {
        best_i = i;
        for (j = i + 1; j < nSize; j++)
            //            if ( pArray[j] < pArray[best_i] )
            if (pPrios[pCube->Lits[pArray[j]] >> 1] < pPrios[pCube->Lits[pArray[best_i]] >> 1]) // list lower priority first (these will be removed first)
                best_i = j;
        temp = pArray[i];
        pArray[i] = pArray[best_i];
        pArray[best_i] = temp;
    }
    /*
        for ( i = 0; i < pCube->nLits; i++ )
            Abc_Print( 1, "%2d : %5d    %5d  %5d\n", i, pArray[i], pCube->Lits[pArray[i]]>>1, pPrios[pCube->Lits[pArray[i]]>>1] );
        Abc_Print( 1, "\n" );
    */
    return pArray;
}

/**Function*************************************************************

  Synopsis    [Return 1 if regId1 should be placed after regId2.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManPredicateCmp(Pdr_Man_t *p, int regId1, int regId2)
{

    // Abc_Print(1, "%2d %2d\n", regId1, regId2);
    if (Pdr_ManIsPredicate(p, regId1) && Pdr_ManIsPredicate(p, regId2))
    {
        if (Vec_IntEntry(p->vPredicateScore, regId1) < Vec_IntEntry(p->vPredicateScore, regId2))
            return 1;
        if (Vec_IntEntry(p->vPredicateScore, regId1) == Vec_IntEntry(p->vPredicateScore, regId2) &&
            regId1 > regId2)
            return 1;
    }
    else if (Pdr_ManIsPredicate(p, regId1))
    {
        int score1 = Vec_IntEntry(p->vPredicateScore, regId1);
        if (Vec_IntEntry(p->vEquivMap, regId2) != -1) // regId2 is a register copy
        {
            int score2 = Vec_IntEntry(p->vPredicateScore, Vec_IntEntry(p->vEquivMap, regId2));
            if (score1 < score2)
                return 1;
            if (score1 == score2 && regId1 < Vec_IntEntry(p->vEquivMap, regId2))
                return 1;
        }
    }
    else if (Pdr_ManIsPredicate(p, regId2))
    {
        if (Vec_IntEntry(p->vEquivMap, regId1) == regId2)
            return 1;
        int score2 = Vec_IntEntry(p->vPredicateScore, regId2);
        if (Vec_IntEntry(p->vEquivMap, regId1) != -1) // regId1 is a register copy
        {
            int score1 = Vec_IntEntry(p->vPredicateScore, Vec_IntEntry(p->vEquivMap, regId1));
            if (score1 < score2)
                return 1;
            if (score1 == score2 && Vec_IntEntry(p->vEquivMap, regId1) < regId2)
                return 1;
        }
    }
    else
    { // both are not predicate register
        if (Vec_IntEntry(p->vEquivMap, regId1) != -1 &&
            Vec_IntEntry(p->vEquivMap, regId2) != -1) // both are register copies
        {
            if (Vec_IntEntry(p->vPredicateScore, Vec_IntEntry(p->vEquivMap, regId1)) <
                Vec_IntEntry(p->vPredicateScore, Vec_IntEntry(p->vEquivMap, regId2)))
                return 1;
            if (Vec_IntEntry(p->vPredicateScore, Vec_IntEntry(p->vEquivMap, regId1)) ==
                    Vec_IntEntry(p->vPredicateScore, Vec_IntEntry(p->vEquivMap, regId2)) &&
                Vec_IntEntry(p->vEquivMap, regId1) < Vec_IntEntry(p->vEquivMap, regId2))
                return 1;
        }
        if (Vec_IntEntry(p->vEquivMap, regId1) == -1 &&
            Vec_IntEntry(p->vEquivMap, regId2) != -1) // regId1 is global
        {
            return 1;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Return 1 if regId1 should be placed after regId2.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManPredicateCmp2(Pdr_Man_t *p, int regId1, int regId2)
{

    // Abc_Print(1, "%2d %2d\n", regId1, regId2);
    if (Pdr_ManIsEqInitPredicate(p, regId1) && Pdr_ManIsEqInitPredicate(p, regId2))
    {
        if (Vec_IntEntry(p->vEqInitScore, regId1) < Vec_IntEntry(p->vEqInitScore, regId2))
            return 1;
        if (Vec_IntEntry(p->vEqInitScore, regId1) == Vec_IntEntry(p->vEqInitScore, regId2) &&
            regId1 > regId2)
            return 1;
    }
    else if (Pdr_ManIsEqInitPredicate(p, regId1))
    {
        int score1 = Vec_IntEntry(p->vEqInitScore, regId1);
        if (Vec_IntEntry(p->vEqinitMap, regId2) != -1) // regId2 is a register copy
        {
            int score2 = Vec_IntEntry(p->vEqInitScore, Vec_IntEntry(p->vEqinitMap, regId2));
            if (score1 < score2)
                return 1;
            if (score1 == score2 && regId1 < Vec_IntEntry(p->vEqinitMap, regId2))
                return 1;
        }
    }
    else if (Pdr_ManIsEqInitPredicate(p, regId2))
    {
        if (Vec_IntEntry(p->vEqinitMap, regId1) == regId2)
            return 1;
        int score2 = Vec_IntEntry(p->vEqInitScore, regId2);
        if (Vec_IntEntry(p->vEqinitMap, regId1) != -1) // regId1 is a register copy
        {
            int score1 = Vec_IntEntry(p->vEqInitScore, Vec_IntEntry(p->vEqinitMap, regId1));
            if (score1 < score2)
                return 1;
            if (score1 == score2 && Vec_IntEntry(p->vEqinitMap, regId1) < regId2)
                return 1;
        }
    }
    else
    { // both are not predicate register
        if (Vec_IntEntry(p->vEqinitMap, regId1) != -1 &&
            Vec_IntEntry(p->vEqinitMap, regId2) != -1) // both are register copies
        {
            if (Vec_IntEntry(p->vEqInitScore, Vec_IntEntry(p->vEqinitMap, regId1)) <
                Vec_IntEntry(p->vEqInitScore, Vec_IntEntry(p->vEqinitMap, regId2)))
                return 1;
            if (Vec_IntEntry(p->vEqInitScore, Vec_IntEntry(p->vEqinitMap, regId1)) ==
                    Vec_IntEntry(p->vEqInitScore, Vec_IntEntry(p->vEqinitMap, regId2)) &&
                Vec_IntEntry(p->vEqinitMap, regId1) < Vec_IntEntry(p->vEqinitMap, regId2))
                return 1;
        }
        if (Vec_IntEntry(p->vEqinitMap, regId1) == -1 &&
            Vec_IntEntry(p->vEqinitMap, regId2) != -1) // regId1 is global
        {
            return 1;
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Inplace sort by predicate priority.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManSortByPredPriority(Pdr_Man_t *p, Pdr_Set_t *pCube)
{
    int temp, i, j, best_i, nSize = pCube->nLits;
    int reg_i, reg_j;
    for (i = 0; i < nSize - 1; i++)
    {
        reg_i = pCube->Lits[i] >> 1;
        best_i = i;
        for (j = i + 1; j < nSize; j++)
        {
            reg_j = pCube->Lits[j] >> 1;
            if (Pdr_ManPredicateCmp(p, reg_i, reg_j))
            {
                best_i = j;
                reg_i = reg_j;
            }
        }
        temp = pCube->Lits[i];
        pCube->Lits[i] = pCube->Lits[best_i];
        pCube->Lits[best_i] = temp;
        // printf("Best %i=%i\n", i, pCube->Lits[best_i]>>1);
    }
}

/**Function*************************************************************

  Synopsis    [Inplace sort by predicate priority.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManSortByPredPriority2(Pdr_Man_t *p, Pdr_Set_t *pCube)
{
    int temp, i, j, best_i, nSize = pCube->nLits;
    int reg_i, reg_j;
    for (i = 0; i < nSize - 1; i++)
    {
        reg_i = pCube->Lits[i] >> 1;
        best_i = i;
        for (j = i + 1; j < nSize; j++)
        {
            reg_j = pCube->Lits[j] >> 1;
            if (Pdr_ManPredicateCmp2(p, reg_i, reg_j))
            {
                best_i = j;
                reg_i = reg_j;
            }
        }
        temp = pCube->Lits[i];
        pCube->Lits[i] = pCube->Lits[best_i];
        pCube->Lits[best_i] = temp;
        // printf("Best %i=%i\n", i, pCube->Lits[best_i]>>1);
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int ZPdr_ManSimpleMic(Pdr_Man_t *p, int k, Pdr_Set_t **ppCube)
{
    int *pOrder;
    int i, j, Lit, RetValue;
    Pdr_Set_t *pCubeTmp;
    // perform generalization
    if (p->pPars->fSkipGeneral)
        return 0;

    // sort literals by their occurences
    pOrder = Pdr_ManSortByPriority(p, *ppCube);
    // try removing literals
    for (j = 0; j < (*ppCube)->nLits; j++)
    {
        // use ordering
        //        i = j;
        i = pOrder[j];

        assert((*ppCube)->Lits[i] != -1);
        // check init state
        if (Pdr_SetIsInit(*ppCube, i))
            continue;
        // try removing this literal
        Lit = (*ppCube)->Lits[i];
        (*ppCube)->Lits[i] = -1;
        RetValue = Pdr_ManCheckCube(p, k, *ppCube, NULL, p->pPars->nConfLimit, 0, 1);
        if (RetValue == -1)
            return -1;
        (*ppCube)->Lits[i] = Lit;
        if (RetValue == 0)
            continue;

        // success - update the cube
        *ppCube = Pdr_SetCreateFrom(pCubeTmp = *ppCube, i);
        Pdr_SetDeref(pCubeTmp);
        assert((*ppCube)->nLits > 0);

        // get the ordering by decreasing priority
        pOrder = Pdr_ManSortByPriority(p, *ppCube);
        j--;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int ZPdr_ManDown(Pdr_Man_t *p, int k, Pdr_Set_t **ppCube, Pdr_Set_t *pPred, Hash_Int_t *keep, Pdr_Set_t *pIndCube, int *added)
{
    int RetValue = 0, CtgRetValue, i, ctgAttempts, l, micResult;
    int kMax = Vec_PtrSize(p->vSolvers) - 1;
    Pdr_Set_t *pCubeTmp, *pCubeMin, *pCtg;
    while (RetValue == 0)
    {
        ctgAttempts = 0;
        while (p->pPars->fCtgs && RetValue == 0 && k > 1 && ctgAttempts < 3)
        {
            pCtg = Pdr_SetDup(pPred);
            // Check CTG for inductiveness
            if (Pdr_SetIsInit(pCtg, -1))
            {
                Pdr_SetDeref(pCtg);
                break;
            }
            if (*added == 0)
            {
                for (i = 1; i <= k; i++)
                    Pdr_ManSolverAddClause(p, i, pIndCube);
                *added = 1;
            }
            ctgAttempts++;
            CtgRetValue = Pdr_ManCheckCube(p, k - 1, pCtg, NULL, p->pPars->nConfLimit, 0, 1);
            if (CtgRetValue != 1)
            {
                Pdr_SetDeref(pCtg);
                break;
            }
            pCubeMin = Pdr_ManReduceClause(p, k - 1, pCtg);
            if (pCubeMin == NULL)
                pCubeMin = Pdr_SetDup(pCtg);

            for (l = k; l < kMax; l++)
                if (!Pdr_ManCheckCube(p, l, pCubeMin, NULL, 0, 0, 1))
                    break;
            micResult = ZPdr_ManSimpleMic(p, l - 1, &pCubeMin);
            assert(micResult != -1);

            // add new clause
            if (p->pPars->fVeryVerbose)
            {
                Abc_Print(1, "Adding cube ");
                Pdr_SetPrint(stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL);
                Abc_Print(1, " to frame %d.\n", l);
            }
            // set priority flops
            for (i = 0; i < pCubeMin->nLits; i++)
            {
                assert(pCubeMin->Lits[i] >= 0);
                assert((pCubeMin->Lits[i] / 2) < Aig_ManRegNum(p->pAig));
                if ((Vec_IntEntry(p->vPrio, pCubeMin->Lits[i] / 2) >> p->nPrioShift) == 0)
                    p->nAbsFlops++;
                Vec_IntAddToEntry(p->vPrio, pCubeMin->Lits[i] / 2, 1 << p->nPrioShift);
            }

            Vec_VecPush(p->vClauses, l, pCubeMin); // consume ref
            p->nCubes++;
            // add clause
            for (i = 1; i <= l; i++)
                Pdr_ManSolverAddClause(p, i, pCubeMin);
            Pdr_SetDeref(pPred);
            RetValue = Pdr_ManCheckCube(p, k, *ppCube, &pPred, p->pPars->nConfLimit, 0, 1);
            assert(RetValue >= 0);
            Pdr_SetDeref(pCtg);
            if (RetValue == 1)
            {
                // printf ("IT'S A ONE\n");
                return 1;
            }
        }

        // join
        if (p->pPars->fVeryVerbose)
        {
            printf("Cube:\n");
            ZPdr_SetPrint(*ppCube);
            printf("\nPred:\n");
            ZPdr_SetPrint(pPred);
        }
        *ppCube = ZPdr_SetIntersection(pCubeTmp = *ppCube, pPred, keep);
        Pdr_SetDeref(pCubeTmp);
        Pdr_SetDeref(pPred);
        if (*ppCube == NULL)
            return 0;
        if (p->pPars->fVeryVerbose)
        {
            printf("Intersection:\n");
            ZPdr_SetPrint(*ppCube);
        }
        if (Pdr_SetIsInit(*ppCube, -1))
        {
            if (p->pPars->fVeryVerbose)
                printf("Failed initiation\n");
            return 0;
        }
        RetValue = Pdr_ManCheckCube(p, k, *ppCube, &pPred, p->pPars->nConfLimit, 0, 1);
        if (RetValue == -1)
            return -1;
        if (RetValue == 1)
        {
            // printf ("*********IT'S A ONE\n");
            break;
        }
        if (RetValue == 0 && (*ppCube)->nLits == 1)
        {
            Pdr_SetDeref(pPred); // fixed memory leak
            // A workaround for the incomplete assignment returned by the SAT
            // solver
            return 0;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Specialized sorting of flops based on priority.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Vec_IntSelectSortPrioReverseLit(int *pArray, int nSize, Vec_Int_t *vPrios)
{
    int i, j, best_i;
    for (i = 0; i < nSize - 1; i++)
    {
        best_i = i;
        for (j = i + 1; j < nSize; j++)
            if (Vec_IntEntry(vPrios, Abc_Lit2Var(pArray[j])) > Vec_IntEntry(vPrios, Abc_Lit2Var(pArray[best_i]))) // prefer higher priority
                best_i = j;
        ABC_SWAP(int, pArray[i], pArray[best_i]);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Performs generalization using a different idea.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManGeneralize2(Pdr_Man_t *p, int k, Pdr_Set_t *pCube, Pdr_Set_t **ppCubeMin)
{
#if 0
    int fUseMinAss = 0;
    sat_solver * pSat = Pdr_ManFetchSolver( p, k );
    int Order = Vec_IntSelectSortPrioReverseLit( pCube->Lits, pCube->nLits, p->vPrio );
    Vec_Int_t * vLits1 = Pdr_ManCubeToLits( p, k, pCube, 1, 0 );
    int RetValue, Count = 0, iLit, Lits[2], nLits = Vec_IntSize( vLits1 );
    // create free variables
    int i, iUseVar, iAndVar;
    iAndVar = Pdr_ManFreeVar(p, k);
    for ( i = 1; i < nLits; i++ )
        Pdr_ManFreeVar(p, k);
    iUseVar = Pdr_ManFreeVar(p, k);
    for ( i = 1; i < nLits; i++ )
        Pdr_ManFreeVar(p, k);
    assert( iUseVar == iAndVar + nLits );
    // if there is only one positive literal, put it in front and always assume
    if ( fUseMinAss )
    {
        for ( i = 0; i < pCube->nLits && Count < 2; i++ )
            Count += !Abc_LitIsCompl(pCube->Lits[i]);
        if ( Count == 1 )
        {
            for ( i = 0; i < pCube->nLits; i++ )
                if ( !Abc_LitIsCompl(pCube->Lits[i]) )
                    break;
            assert( i < pCube->nLits );
            iLit = pCube->Lits[i];
            for ( ; i > 0; i-- )
                pCube->Lits[i] = pCube->Lits[i-1];
            pCube->Lits[0] = iLit;
        }
    }
    // add clauses for the additional AND-gates
    Vec_IntForEachEntry( vLits1, iLit, i )
    {
        sat_solver_add_buffer_enable( pSat, iAndVar + i, Abc_Lit2Var(iLit), iUseVar + i, Abc_LitIsCompl(iLit) );
        Vec_IntWriteEntry( vLits1, i, Abc_Var2Lit(iAndVar + i, 0) );
    }
    // add clauses for the additional OR-gate
    RetValue = sat_solver_addclause( pSat, Vec_IntArray(vLits1), Vec_IntLimit(vLits1) );
    assert( RetValue == 1 );
    // add implications
    vLits1 = Pdr_ManCubeToLits( p, k, pCube, 0, 1 );
    assert( Vec_IntSize(vLits1) == nLits );
    Vec_IntForEachEntry( vLits1, iLit, i )
    {
        Lits[0] = Abc_Var2Lit(iUseVar + i, 1);
        Lits[1] = iLit;
        RetValue = sat_solver_addclause( pSat, Lits, Lits+2 );
        assert( RetValue == 1 );
        Vec_IntWriteEntry( vLits1, i, Abc_Var2Lit(iUseVar + i, 0) );
    }
    sat_solver_compress( pSat );
    // perform minimization
    if ( fUseMinAss )
    {
        if ( Count == 1 ) // always assume the only positive literal
        {
            if ( !sat_solver_push(pSat, Vec_IntEntry(vLits1, 0)) ) // UNSAT with the first (mandatory) literal
                nLits = 1;
            else
                nLits = 1 + sat_solver_minimize_assumptions2( pSat, Vec_IntArray(vLits1)+1, nLits-1, p->pPars->nConfLimit );
            sat_solver_pop(pSat); // unassume the first literal
        }
        else
            nLits = sat_solver_minimize_assumptions2( pSat, Vec_IntArray(vLits1), nLits, p->pPars->nConfLimit );
        Vec_IntShrink( vLits1, nLits );
    }
    else
    {
        // try removing one literal at a time in the old-fashioned way
        int k, Entry;
        Vec_Int_t * vTemp = Vec_IntAlloc( nLits );
        for ( i = nLits - 1; i >= 0; i-- )
        {
            // if we are about to remove a positive lit, make sure at least one positive lit remains
            if ( !Abc_LitIsCompl(Vec_IntEntry(vLits1, i)) )
            {
                Vec_IntForEachEntry( vLits1, iLit, k )
                    if ( iLit != -1 && k != i && !Abc_LitIsCompl(iLit) )
                        break;
                if ( k == Vec_IntSize(vLits1) ) // no other positive literals, except the i-th one
                    continue;
            }
            // load remaining literals
            Vec_IntClear( vTemp );
            Vec_IntForEachEntry( vLits1, Entry, k )
                if ( Entry != -1 && k != i )
                    Vec_IntPush( vTemp, Entry );
                else if ( Entry != -1 ) // assume opposite literal
                    Vec_IntPush( vTemp, Abc_LitNot(Entry) );
            // solve with assumptions
            RetValue = sat_solver_solve( pSat, Vec_IntArray(vTemp), Vec_IntLimit(vTemp), p->pPars->nConfLimit, 0, 0, 0 );
            // commit the literal
            if ( RetValue == l_False )
            {
                int LitNot = Abc_LitNot(Vec_IntEntry(vLits1, i));
                int RetValue = sat_solver_addclause( pSat, &LitNot, &LitNot+1 );
                assert( RetValue );
            }
            // update the clause
            if ( RetValue == l_False )
                Vec_IntWriteEntry( vLits1, i, -1 );
        }
        Vec_IntFree( vTemp );
        // compact
        k = 0;
        Vec_IntForEachEntry( vLits1, Entry, i )
            if ( Entry != -1 )
                Vec_IntWriteEntry( vLits1, k++, Entry );
        Vec_IntShrink( vLits1, k );
    }
    // remap auxiliary literals into original literals
    Vec_IntForEachEntry( vLits1, iLit, i )
        Vec_IntWriteEntry( vLits1, i, pCube->Lits[Abc_Lit2Var(iLit)-iUseVar] );
    // make sure the cube has at least one positive literal
    if ( fUseMinAss )
    {
        Vec_IntForEachEntry( vLits1, iLit, i )
            if ( !Abc_LitIsCompl(iLit) )
                break;
        if ( i == Vec_IntSize(vLits1) ) // has no positive literals
        {
            // find positive lit in the cube
            for ( i = 0; i < pCube->nLits; i++ )
                if ( !Abc_LitIsCompl(pCube->Lits[i]) )
                    break;
            assert( i < pCube->nLits );
            Vec_IntPush( vLits1, pCube->Lits[i] );
//            printf( "-" );
        }
//        else
//            printf( "+" );
    }
    // create a subset cube
    *ppCubeMin = Pdr_SetCreateSubset( pCube, Vec_IntArray(vLits1), Vec_IntSize(vLits1) );
    assert( !Pdr_SetIsInit(*ppCubeMin, -1) );
    Order = 0;
#endif
    return 0;
}

/**Function*************************************************************

  Synopsis    [Compute the replace-by-eqinit-predicate cube]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t *Pdr_ManEqInitPredicateReplace(Pdr_Man_t *p, int k, Pdr_Set_t *pCube)
{
    Pdr_Set_t *pCubePredicate;
    int i, RegId, SymReg, PredicateReg;

    pCubePredicate = (Pdr_Set_t *)ABC_ALLOC(char, sizeof(Pdr_Set_t) + (pCube->nTotal) * sizeof(int));
    pCubePredicate->nLits = 0;
    pCubePredicate->nTotal = 0;
    pCubePredicate->nRefs = 1;
    pCubePredicate->Sign = 0;

    for (i = 0; i < p->vPredicateStatus->nSize; i++)
        p->vPredicateStatus->pArray[i] = 0;

    // First pass, mark the status of each literal in the cube
    for (i = 0; i < pCube->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCube->Lits[i]);
        if (Vec_IntEntry(p->vEqinitMap, RegId) < 0)
        {
            p->vPredicateStatus->pArray[RegId] = -1; // -1 means this variable does not have equivalence predicates and should be kept in the cube
        }
        else
        {
            if (!Abc_LitIsCompl(pCube->Lits[i]))
            {
                p->vPredicateStatus->pArray[RegId] = 1; // 1 means the literal value is 1, and we can try to replace it with the eqinit predicate
            }
            else
            {
                p->vPredicateStatus->pArray[RegId] = -1; // -1 means the literal value is 0, we should keep it in the cube.
            }
        }
    }

    // Second pass, formulate the new cube
    int isDiff = 0;
    for (i = 0; i < pCube->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCube->Lits[i]);
        if(p->vPredicateStatus->pArray[RegId] == -1)
        {
            pCubePredicate->Lits[pCubePredicate->nLits] = pCube->Lits[i];
            pCubePredicate->Sign |= ((word)1) << (pCube->Lits[i] % 63);
            pCubePredicate->nLits++;
            p->vPredicateStatus->pArray[RegId] = 2; // If a literal is already added to cube, mark its status as 2
        }
        else if (p->vPredicateStatus->pArray[RegId] == 1)
        {
            isDiff = 1;
            PredicateReg = Vec_IntEntry(p->vEqinitMap, RegId);
            if (p->vPredicateStatus->pArray[PredicateReg] == 0) 
            {
                pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(PredicateReg, 0);
                pCubePredicate->Sign |= ((word)1) << (Abc_Var2Lit(PredicateReg, 0) % 63);
                pCubePredicate->nLits++;
                p->vPredicateStatus->pArray[PredicateReg] = 2;
            }
        }
    }

    pCubePredicate->nTotal = pCubePredicate->nLits;

    if (isDiff)
    {
        Vec_IntSelectSort(pCubePredicate->Lits, pCubePredicate->nLits);
        return pCubePredicate;
    }
    else
    {
        Pdr_SetDeref(pCubePredicate);
        return NULL;
    }
}


/**Function*************************************************************

  Synopsis    [Compute the replace-by-predicate cube iteratively with SAT checking]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManEqInitIterPredicateReplace(Pdr_Man_t *p, int k, Pdr_Set_t *pCube, Pdr_Set_t **ppPCube)
{
    Pdr_Set_t *pCubePredicate;
    int i, RegId, SymReg, PredicateReg;
    int RetValue;

    for (i = 0; i < p->vPredicateStatus->nSize; i++)
    {
        p->vPredicateStatus->pArray[i] = 0;
        p->vEqInitRegCnt->pArray[i] = 0;
    }

    Pdr_Set_t *pCubeCpy = Pdr_SetDup(pCube);
    Pdr_ManSortByPredPriority2(p, pCubeCpy);
    // Abc_Print( 1, "Printing Sorted Cube:\n");
    // for( i=0; i < pCubeCpy->nLits; i++){
    //     int regId = Abc_Lit2Var(pCubeCpy->Lits[i]);
    //     int predRegId = Vec_IntEntry(p->vEqinitMap, regId);
    //     int score = Vec_IntEntry(p->vEqInitScore, regId);
    //     int predScore = 0;
    //     if (predRegId >= 0){
    //         predScore =  Vec_IntEntry(p->vEqInitScore, predRegId);
    //     }
    //     Abc_Print( 1, "Reg %5d Pred %5d Score %5d PredScore %5d\n", regId, predRegId, score, predScore);
    //     Abc_Print( 1, "\n" );
    // }

    // The first pass, record the information of every literal in the pCube
    // First pass, mark the status of each literal in the cube
    for (i = 0; i < pCubeCpy->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCubeCpy->Lits[i]);
        if (Vec_IntEntry(p->vEqinitMap, RegId) < 0)
        {
            p->vPredicateStatus->pArray[RegId] = -1; // -1 means this variable does not have equivalence predicates and should be kept in the cube
        }
        else
        {
            if (!Abc_LitIsCompl(pCubeCpy->Lits[i]))
            {
                p->vPredicateStatus->pArray[RegId] = 1; // 1 means the literal value is 1, and we can try to replace it with the eqinit predicate
            }
            else
            {
                p->vPredicateStatus->pArray[RegId] = -1; // -1 means the literal value is 0, we should keep it in the cube.
            }
        }
    }

    // Second pass, deduce which predicates to try
    int predCnt = 0;
    for (i = 0; i < pCubeCpy->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCubeCpy->Lits[i]);
        if (Vec_IntEntry(p->vPredicateStatus, RegId) == 1)
        {
            PredicateReg = Vec_IntEntry(p->vEqinitMap, RegId);
            if (Vec_IntEntry(p->vPredicateStatus, PredicateReg) == 0) 
            {
                p->vPredicateStatus->pArray[PredicateReg] = -3; // -3 means this predicate variable is not used yet, and we can try to use it
                predCnt ++;
            }
        }
    }
    // printf("Predicate Count: %d\n", predCnt);

    pCubePredicate = (Pdr_Set_t *)ABC_ALLOC(char, sizeof(Pdr_Set_t) + (pCube->nTotal + predCnt) * sizeof(int));
    pCubePredicate->nLits = 0;
    pCubePredicate->nTotal = 0;
    pCubePredicate->nRefs = 1;
    pCubePredicate->Sign = 0;

    int isDiff = 0;
    // The third pass, compute the final cube
    int predRegs[1000];
    int predId = 0;
    for (i = 0; i < pCubeCpy->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCubeCpy->Lits[i]);
        PredicateReg = Vec_IntEntry(p->vEqinitMap, RegId);

        if (Vec_IntEntry(p->vPredicateStatus, RegId) == 1) // register copies
        {
            // printf("Predicate Status: %i, RegId: %i, PredicateReg: %i\n", Vec_IntEntry(p->vPredicateStatus, PredicateReg), RegId, PredicateReg);
            if (Vec_IntEntry(p->vPredicateStatus, PredicateReg) == -3)
            {
                // Set predicate variable to 1
                // pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(PredicateReg, 0);
                pCubePredicate->Lits[pCubePredicate->nLits] = -1;
                // printf("Setting predicate register %i to -1\n", PredicateReg);
                predRegs[predId] = PredicateReg;
                pCubePredicate->nLits++;
                p->vEqInitRegCnt->pArray[PredicateReg]++;
                predId++;

                // Skip the predicate variable
                p->vPredicateStatus->pArray[PredicateReg] = -4;
            }
            pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(RegId, Abc_LitIsCompl(pCubeCpy->Lits[i]));
            pCubePredicate->nLits++;
        }
        else if (Vec_IntEntry(p->vPredicateStatus, RegId) == -1) // predicate or global registers that already exists
        {
            pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(RegId, Abc_LitIsCompl(pCubeCpy->Lits[i]));
            pCubePredicate->nLits++;
        }
    }
    // pCubePredicate->nTotal = pCubePredicate->nLits + pCube->nTotal - pCube->nLits;
    pCubePredicate->nTotal = pCubePredicate->nLits;

    // last pass: iterative generalization
    predId = 0;
    int nSkips = 0;
    for (i = 0; i < pCubePredicate->nLits && predId < predCnt;)
    {
        // printf("Loop: %i Lits: %i\n", i, pCubePredicate->Lits[i]);
        if (pCubePredicate->Lits[i] == -1) // found a to be added predicate register
        {
            PredicateReg = predRegs[predId];
            assert(PredicateReg > 0);
            // try to add this predicate register
            pCubePredicate->Lits[i] = Abc_Var2Lit(PredicateReg, 0);
            // number of bind register copies
            int nRegs = Vec_IntEntry(p->vEqInitRegCnt, PredicateReg);
            // printf("nRegs: %i\n", nRegs);
            int regLits[256];
            // set bind register copes to don't cares
            for (int j = 0; j < nRegs; ++j)
            {
                regLits[j] = pCubePredicate->Lits[i + 1 + j];
                pCubePredicate->Lits[i + 1 + j] = -1;
            }

            RetValue = Pdr_ManCheckCube(p, k, pCubePredicate, NULL, p->pPars->nConfLimit, 1, 0);

            if (RetValue == -1)
            {
                Pdr_SetDeref(pCubePredicate);
                return -1;
            }

            if (RetValue == 0) // fail
            {
                // restore values of register copies and predicate
                pCubePredicate->Lits[i] = -1;
                for (int j = 0; j < nRegs; ++j)
                {
                    pCubePredicate->Lits[i + 1 + j] = regLits[j];
                }
                nSkips += 1;

                // if (p->pPars->fVeryVerbose)
                //     printf("Fail to set predicate %i\n", PredicateReg);
            }
            else
            {
                // success - proceed to the next predicate register
                isDiff = 1;
                nSkips += nRegs;
                // if (p->pPars->fVeryVerbose)
                //     printf("Succeed to set predicate %i nReg=%i\n", PredicateReg, nRegs);
            }

            i += (1 + nRegs);
            predId++;
        }
        else
            i++;
    }

    Pdr_SetDeref(pCubeCpy);
    if (isDiff)
    {
        Pdr_Set_t *pCubeRes = Pdr_SetSkipCreate(pCubePredicate, nSkips);
        // if (p->pPars->fVeryVerbose)
        // {
        //     Abc_Print(1, "Non-Skipped cube ");
        //     Pdr_SetPrint(stdout, pCubePredicate, Aig_ManRegNum(p->pAig), NULL);
        //     Abc_Print(1, "\n");
        //     Abc_Print(1, "Skipped cube ");
        //     Pdr_SetPrint(stdout, pCubeRes, Aig_ManRegNum(p->pAig), NULL);
        //     Abc_Print(1, "\n");
        // }
        Pdr_SetDeref(pCubePredicate);
        Vec_IntSelectSort(pCubeRes->Lits, pCubeRes->nLits);
        *ppPCube = pCubeRes;
        return 1;
    }
    else
    {
        Pdr_SetDeref(pCubePredicate);
        *ppPCube = NULL;
        return 0;
    }
}

/**Function*************************************************************

  Synopsis    [Compute the replace-by-equiv-predicate cube]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Pdr_Set_t *Pdr_ManEquivPredicateReplace(Pdr_Man_t *p, int k, Pdr_Set_t *pCube)
{
    Pdr_Set_t *pCubePredicate;
    int i, RegId, SymReg, PredicateReg;

    pCubePredicate = (Pdr_Set_t *)ABC_ALLOC(char, sizeof(Pdr_Set_t) + (pCube->nTotal) * sizeof(int));
    pCubePredicate->nLits = 0;
    pCubePredicate->nTotal = 0;
    pCubePredicate->nRefs = 1;
    pCubePredicate->Sign = 0;

    for (i = 0; i < p->vPredicateStatus->nSize; i++)
        p->vPredicateStatus->pArray[i] = 0;

    // exit(1);

    // The first pass, record the information of every literal in the pCube
    for (i = 0; i < pCube->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCube->Lits[i]);
        assert(RegId < Vec_IntSize(p->vSymMap) && 0 <= RegId);
        if (Vec_IntEntry(p->vEquivMap, RegId) < 0)
        {
            p->vPredicateStatus->pArray[RegId] = -1; // -1 means this variable does not have equivalence predicates and should be kept in the cube
        }
        else
        {
            if (Abc_LitIsCompl(pCube->Lits[i]))
            {
                p->vPredicateStatus->pArray[RegId] = 1; // 1 means the literal value is 0
            }
            else
            {
                p->vPredicateStatus->pArray[RegId] = 2; // 2 means the literal value is 1
            }
        }
    }

    // The second pass, deduce which predicates should be used
    for (i = 0; i < pCube->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCube->Lits[i]);
        if (Vec_IntEntry(p->vPredicateStatus, RegId) > 0)
        {
            SymReg = Vec_IntEntry(p->vSymMap, RegId);
            PredicateReg = Vec_IntEntry(p->vEquivMap, RegId);
            // If both literal and its symmetry exist and they hold opposite value, then add the predicate variable tentatively
            if (((Vec_IntEntry(p->vPredicateStatus, RegId) == 1 && Vec_IntEntry(p->vPredicateStatus, SymReg) == 2) || (Vec_IntEntry(p->vPredicateStatus, RegId) == 2 && Vec_IntEntry(p->vPredicateStatus, SymReg) == 1)))
            {
                p->vPredicateStatus->pArray[PredicateReg] = -3; // -3 means this predicate variable should be added to the final cube
                p->vPredicateStatus->pArray[RegId] = 0; // 0 represents this literal should not be kept in the resultant cube anymore
                p->vPredicateStatus->pArray[SymReg] = 0;
            }
        }
        // Abc_Print(1, "Reg Status: %d\n", p->vPredicateStatus->pArray[RegId]);
    }

    int isDiff = 0;
    // The third pass, compute the final cube
    for (i = 0; i < pCube->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCube->Lits[i]);
        SymReg = Vec_IntEntry(p->vSymMap, RegId);
        PredicateReg = Vec_IntEntry(p->vEquivMap, RegId);

        if (Vec_IntEntry(p->vPredicateStatus, RegId) != 0)
        {
            pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(RegId, Abc_LitIsCompl(pCube->Lits[i]));
            pCubePredicate->Sign |= ((word)1) << (pCube->Lits[i] % 63);
            pCubePredicate->nLits++;
        }
        else if (Vec_IntEntry(p->vPredicateStatus, PredicateReg) == -3)
        {
            pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(PredicateReg, 0);
            pCubePredicate->Sign |= ((word)1) << (pCubePredicate->Lits[pCubePredicate->nLits] % 63);
            pCubePredicate->nLits++;
            isDiff = 1;

            p->vPredicateStatus->pArray[PredicateReg] = 0;
        }

    }

    pCubePredicate->nTotal = pCubePredicate->nLits + pCube->nTotal - pCube->nLits;

    if (isDiff)
    {
        Vec_IntSelectSort(pCubePredicate->Lits, pCubePredicate->nLits);
        return pCubePredicate;
    }
    else
    {
        Pdr_SetDeref(pCubePredicate);
        return NULL;
    }
}

/**Function*************************************************************

  Synopsis    [Compute the replace-by-predicate cube iteratively with SAT checking]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManEquivIterPredicateReplace(Pdr_Man_t *p, int k, Pdr_Set_t *pCube, Pdr_Set_t **ppPCube)
{
    Pdr_Set_t *pCubePredicate;
    int i, RegId, SymReg, PredicateReg;
    int RetValue;

    for (i = 0; i < p->vPredicateStatus->nSize; i++)
    {
        p->vPredicateStatus->pArray[i] = 0;
        p->vPredicateRegCnt->pArray[i] = 0;
    }

    Pdr_Set_t *pCubeCpy = Pdr_SetDup(pCube);
    Pdr_ManSortByPredPriority(p, pCubeCpy);
    // for( i=0; i < pCubeCpy->nLits; i++){
    //     int regId = Abc_Lit2Var(pCubeCpy->Lits[i]);
    //     int predRegId = Vec_IntEntry(p->vEquivMap, regId);
    //     int score = Vec_IntEntry(p->vPredicateScore, regId);
    //     int predScore = 0;
    //     if (predRegId >= 0){
    //         predScore =  Vec_IntEntry(p->vPredicateScore, predRegId);
    //     }
    //     Abc_Print( 1, "Reg %5d Pred %5d Score %5d PredScore %5d\n", regId, predRegId, score, predScore);
    //     Abc_Print( 1, "\n" );
    // }

    // The first pass, record the information of every literal in the pCube
    for (i = 0; i < pCubeCpy->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCubeCpy->Lits[i]);
        assert(RegId < Vec_IntSize(p->vSymMap) && 0 <= RegId);
        if (Vec_IntEntry(p->vEquivMap, RegId) < 0)
        {
            p->vPredicateStatus->pArray[RegId] = -1; // -1 means this variable does not have equivalence predicates and should be kept in the cube
        }
        else
        {
            if (Abc_LitIsCompl(pCubeCpy->Lits[i]))
            {
                p->vPredicateStatus->pArray[RegId] = 1; // 1 means the literal value is 0
            }
            else
            {
                p->vPredicateStatus->pArray[RegId] = 2; // 2 means the literal value is 1
            }
        }
    }

    int predCnt = 0;
    // The second pass, deduce which predicates should be used
    for (i = 0; i < pCubeCpy->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCubeCpy->Lits[i]);
        if (Vec_IntEntry(p->vPredicateStatus, RegId) > 0)
        {
            SymReg = Vec_IntEntry(p->vSymMap, RegId);
            PredicateReg = Vec_IntEntry(p->vEquivMap, RegId);
            // If both literal and its symmetry exist and they hold opposite value, then add the predicate variable tentatively
            if (((Vec_IntEntry(p->vPredicateStatus, RegId) == 1 && Vec_IntEntry(p->vPredicateStatus, SymReg) == 2) || (Vec_IntEntry(p->vPredicateStatus, RegId) == 2 && Vec_IntEntry(p->vPredicateStatus, SymReg) == 1)))
            {
                p->vPredicateStatus->pArray[PredicateReg] = -3; // -3 means this predicate variable should be added to the final cube
                p->vPredicateStatus->pArray[RegId] = 0;         // 0 represents this literal should not be kept in the resultant cube anymore
                p->vPredicateStatus->pArray[SymReg] = 0;
                predCnt++;
            }
        }
        // Abc_Print(1, "Reg Status: %d\n", p->vPredicateStatus->pArray[RegId]);
    }

    // The second pass, deduce which predicates should be used
    // for (i = 0; i < pCubeCpy->nLits; i++)
    // {
    //     RegId = Abc_Lit2Var(pCubeCpy->Lits[i]);
    //     if (Vec_IntEntry(p->vPredicateStatus, RegId) > 0)
    //     {
    //         SymReg = Vec_IntEntry(p->vSymMap, RegId);
    //         PredicateReg = Vec_IntEntry(p->vEquivMap, RegId);
    //         // If both literal and its symmetry exist and they hold opposite value, then add the predicate variable tentatively
    //         if ((Vec_IntEntry(p->vPredicateStatus, PredicateReg) != -4) && ((Vec_IntEntry(p->vPredicateStatus, RegId) == 1 && Vec_IntEntry(p->vPredicateStatus, SymReg) == 2) || (Vec_IntEntry(p->vPredicateStatus, RegId) == 2 && Vec_IntEntry(p->vPredicateStatus, SymReg) == 1)))
    //         {
    //             if (Vec_IntEntry(p->vPredicateStatus, PredicateReg) == 0) // do not exist in the original cube
    //             {
    //                 p->vPredicateStatus->pArray[PredicateReg] = -3; // -3 means this predicate variable should be added to the final cube
    //                 predCnt++;
    //             }
    //         }
    //         // If the cube containts both literal and its symmetry and they have the same value, then the predicate should not be added
    //         // else if (((Vec_IntEntry(p->vPredicateStatus, RegId) == 1 && Vec_IntEntry(p->vPredicateStatus, SymReg) == 1) || (Vec_IntEntry(p->vPredicateStatus, RegId) == 2 && Vec_IntEntry(p->vPredicateStatus, SymReg) == 2)))
    //         //     p->vPredicateStatus->pArray[PredicateReg] = -4; // -4 means this predicate variable should not be added
    //     }
    // }

    pCubePredicate = (Pdr_Set_t *)ABC_ALLOC(char, sizeof(Pdr_Set_t) + (pCube->nTotal + predCnt) * sizeof(int));
    pCubePredicate->nLits = 0;
    pCubePredicate->nTotal = 0;
    pCubePredicate->nRefs = 1;
    pCubePredicate->Sign = 0;

    int isDiff = 0;
    // The third pass, compute the final cube
    int predRegs[1000];
    int predId = 0;

    for (i = 0; i < pCubeCpy->nLits; i++)
    {
        RegId = Abc_Lit2Var(pCubeCpy->Lits[i]);
        SymReg = Vec_IntEntry(p->vSymMap, RegId);
        PredicateReg = Vec_IntEntry(p->vEquivMap, RegId);

        if (Vec_IntEntry(p->vPredicateStatus, RegId) != 0)
        {
            pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(RegId, Abc_LitIsCompl(pCubeCpy->Lits[i]));
            pCubePredicate->Sign |= ((word)1) << (pCubeCpy->Lits[i] % 63);
            pCubePredicate->nLits++;
        }
        else if (Vec_IntEntry(p->vPredicateStatus, PredicateReg) == -3)
        {
            pCubePredicate->Lits[pCubePredicate->nLits] = -1;
            pCubePredicate->Sign |= ((word)1) << (pCubePredicate->Lits[pCubePredicate->nLits] % 63);
            pCubePredicate->nLits++;
            predRegs[predId] = PredicateReg;
            p->vPredicateRegCnt->pArray[PredicateReg]++;
            predId++;

            p->vPredicateStatus->pArray[PredicateReg] = 0;

            pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(RegId, Abc_LitIsCompl(pCubeCpy->Lits[i]));
            pCubePredicate->nLits++;
        }
        
    }
    pCubePredicate->nTotal = pCubePredicate->nLits;

    // for (i = 0; i < pCubeCpy->nLits; i++)
    // {
    //     RegId = Abc_Lit2Var(pCubeCpy->Lits[i]);
    //     SymReg = Vec_IntEntry(p->vSymMap, RegId);
    //     PredicateReg = Vec_IntEntry(p->vEquivMap, RegId);

    //     if (Vec_IntEntry(p->vPredicateStatus, RegId) > 0) // register copies
    //     {
    //         if (Vec_IntEntry(p->vPredicateStatus, PredicateReg) == -3)
    //         {
    //             // Set predicate variable to 1
    //             // pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(PredicateReg, 0);
    //             pCubePredicate->Lits[pCubePredicate->nLits] = -1;
    //             predRegs[predId] = PredicateReg;
    //             pCubePredicate->nLits++;
    //             p->vPredicateRegCnt->pArray[PredicateReg]++;
    //             predId++;

    //             // Skip the predicate variable
    //             p->vPredicateStatus->pArray[PredicateReg] = -4;
    //         }
    //         pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(RegId, Abc_LitIsCompl(pCubeCpy->Lits[i]));
    //         pCubePredicate->nLits++;
    //     }
    //     else if (Vec_IntEntry(p->vPredicateStatus, RegId) == -1) // predicate or global registers that already exists
    //     {
    //         pCubePredicate->Lits[pCubePredicate->nLits] = Abc_Var2Lit(RegId, Abc_LitIsCompl(pCubeCpy->Lits[i]));
    //         pCubePredicate->nLits++;
    //     }
    // }
    // // pCubePredicate->nTotal = pCubePredicate->nLits + pCube->nTotal - pCube->nLits;

    // last pass: iterative generalization
    predId = 0;
    int nSkips = 0;
    for (i = 0; i < pCubePredicate->nLits && predId < predCnt;)
    {
        // printf("Loop: %i\n", i);
        if (pCubePredicate->Lits[i] == -1) // found a to be added predicate register
        {
            PredicateReg = predRegs[predId];
            assert(PredicateReg > 0);
            // try to add this predicate register
            pCubePredicate->Lits[i] = Abc_Var2Lit(PredicateReg, 0);
            // number of bind register copies
            int nRegs = Vec_IntEntry(p->vPredicateRegCnt, PredicateReg);
            int regLits[256];
            // set bind register copes to don't cares
            for (int j = 0; j < nRegs; ++j)
            {
                regLits[j] = pCubePredicate->Lits[i + 1 + j];
                pCubePredicate->Lits[i + 1 + j] = -1;
            }

            RetValue = Pdr_ManCheckCube(p, k, pCubePredicate, NULL, p->pPars->nConfLimit, 1, 0);

            if (RetValue == -1)
            {
                Pdr_SetDeref(pCubePredicate);
                return -1;
            }

            if (RetValue == 0) // fail
            {
                // restore values of register copies and predicate
                pCubePredicate->Lits[i] = -1;
                for (int j = 0; j < nRegs; ++j)
                {
                    pCubePredicate->Lits[i + 1 + j] = regLits[j];
                }
                nSkips += 1;

                // if (p->pPars->fVeryVerbose)
                //     printf("Fail to set predicate %i\n", PredicateReg);
            }
            else
            {
                // success - proceed to the next predicate register
                isDiff = 1;
                nSkips += nRegs;
                // if (p->pPars->fVeryVerbose)
                //     printf("Succeed to set predicate %i nReg=%i\n", PredicateReg, nRegs);
            }

            i += (1 + nRegs);
            predId++;
        }
        else
            i++;
    }

    Pdr_SetDeref(pCubeCpy);
    if (isDiff)
    {
        Pdr_Set_t *pCubeRes = Pdr_SetSkipCreate(pCubePredicate, nSkips);
        // if (p->pPars->fVeryVerbose)
        // {
        //     Abc_Print(1, "Non-Skipped cube ");
        //     Pdr_SetPrint(stdout, pCubePredicate, Aig_ManRegNum(p->pAig), NULL);
        //     Abc_Print(1, "\n");
        //     Abc_Print(1, "Skipped cube ");
        //     Pdr_SetPrint(stdout, pCubeRes, Aig_ManRegNum(p->pAig), NULL);
        //     Abc_Print(1, "\n");
        // }
        Pdr_SetDeref(pCubePredicate);
        Vec_IntSelectSort(pCubeRes->Lits, pCubeRes->nLits);
        *ppPCube = pCubeRes;
        return 1;
    }
    else
    {
        Pdr_SetDeref(pCubePredicate);
        *ppPCube = NULL;
        return 0;
    }
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the state could be blocked.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManGeneralize(Pdr_Man_t *p, int k, Pdr_Set_t *pCube, Pdr_Set_t **ppPred, Pdr_Set_t **ppCubeMin)
{
    Pdr_Set_t *pCubeMin, *pCubeTmp = NULL, *pPred = NULL, *pCubeCpy = NULL, *pCubePredicate = NULL;
    int i, j, Lit, RetValue;
    abctime clk = Abc_Clock();
    int *pOrder;
    int added = 0;
    Hash_Int_t *keep = NULL;
    // if there is no induction, return
    *ppCubeMin = NULL;
    if (p->pPars->fFlopOrder)
        Vec_IntSelectSortPrioReverseLit(pCube->Lits, pCube->nLits, p->vPrio);
    // This is checking that (!pCube && R_k && Tr && pcube) is satisfiable
    RetValue = Pdr_ManCheckCube(p, k, pCube, ppPred, p->pPars->nConfLimit, 0, 1);
    if (p->pPars->fFlopOrder)
        Vec_IntSelectSort(pCube->Lits, pCube->nLits);
    if (RetValue == -1)
        return -1;
    if (RetValue == 0)
    {
        p->tGeneral += Abc_Clock() - clk;
        return 0;
    }

    // reduce clause using assumptions
    //    pCubeMin = Pdr_SetDup( pCube );
    pCubeMin = Pdr_ManReduceClause(p, k, pCube);
    if (pCubeMin == NULL)
        pCubeMin = Pdr_SetDup(pCube);

    

    // perform simplified generalization
    if (p->pPars->fSimpleGeneral)
    {
        assert(pCubeMin->nLits > 0);
        if (pCubeMin->nLits > 1)
        {
            RetValue = Pdr_ManGeneralize2(p, k, pCubeMin, ppCubeMin);
            Pdr_SetDeref(pCubeMin);
            assert(ppCubeMin != NULL);
            pCubeMin = *ppCubeMin;
        }
        *ppCubeMin = pCubeMin;
        if (p->pPars->fVeryVerbose)
        {
            printf("Cube:\n");
            for (i = 0; i < pCubeMin->nLits; i++)
                printf("%d ", pCubeMin->Lits[i]);
            printf("\n");
        }
        p->tGeneral += Abc_Clock() - clk;
        return 1;
    }

    keep = p->pPars->fSkipDown ? NULL : Hash_IntAlloc(1);

    // perform generalization
    if (!p->pPars->fSkipGeneral)
    {
        // assume the unminimized cube
        if (p->pPars->fSimpleGeneral)
        {
            sat_solver *pSat = Pdr_ManFetchSolver(p, k);
            Vec_Int_t *vLits1 = Pdr_ManCubeToLits(p, k, pCubeMin, 1, 0);
            int RetValue1 = sat_solver_addclause(pSat, Vec_IntArray(vLits1), Vec_IntArray(vLits1) + Vec_IntSize(vLits1));
            assert(RetValue1 == 1);
            sat_solver_compress(pSat);
        }

        // sort literals by their occurences
        pOrder = Pdr_ManSortByPriority(p, pCubeMin);
        // try removing literals
        for (j = 0; j < pCubeMin->nLits; j++)
        {
            // use ordering
            //        i = j;
            i = pOrder[j];

            assert(pCubeMin->Lits[i] != -1);
            if (keep && Hash_IntExists(keep, pCubeMin->Lits[i]))
            {
                // printf("Undroppable\n");
                continue;
            }

            // check init state
            if (Pdr_SetIsInit(pCubeMin, i))
                continue;

            // try removing this literal
            Lit = pCubeMin->Lits[i];
            pCubeMin->Lits[i] = -1;
            if (p->pPars->fSkipDown)
                RetValue = Pdr_ManCheckCube(p, k, pCubeMin, NULL, p->pPars->nConfLimit, 1, !p->pPars->fSimpleGeneral);
            else
                RetValue = Pdr_ManCheckCube(p, k, pCubeMin, &pPred, p->pPars->nConfLimit, 1, !p->pPars->fSimpleGeneral);
            if (RetValue == -1)
            {
                Pdr_SetDeref(pCubeMin);
                return -1;
            }
            pCubeMin->Lits[i] = Lit;
            if (RetValue == 0)
            {
                if (p->pPars->fSkipDown)
                    continue;
                pCubeCpy = Pdr_SetCreateFrom(pCubeMin, i);
                RetValue = ZPdr_ManDown(p, k, &pCubeCpy, pPred, keep, pCubeMin, &added);
                if (p->pPars->fCtgs)
                    // CTG handling code messes up with the internal order array
                    pOrder = Pdr_ManSortByPriority(p, pCubeMin);
                if (RetValue == -1)
                {
                    Pdr_SetDeref(pCubeMin);
                    Pdr_SetDeref(pCubeCpy);
                    Pdr_SetDeref(pPred);
                    return -1;
                }
                if (RetValue == 0)
                {
                    if (keep)
                        Hash_IntWriteEntry(keep, pCubeMin->Lits[i], 0);
                    if (pCubeCpy)
                        Pdr_SetDeref(pCubeCpy);
                    continue;
                }
                // Inductive subclause
                added = 0;
                Pdr_SetDeref(pCubeMin);
                pCubeMin = pCubeCpy;
                assert(pCubeMin->nLits > 0);
                pOrder = Pdr_ManSortByPriority(p, pCubeMin);
                j = -1;
                continue;
            }
            added = 0;

            // success - update the cube
            pCubeMin = Pdr_SetCreateFrom(pCubeTmp = pCubeMin, i);
            Pdr_SetDeref(pCubeTmp);
            assert(pCubeMin->nLits > 0);

            // assume the minimized cube
            if (p->pPars->fSimpleGeneral)
            {
                sat_solver *pSat = Pdr_ManFetchSolver(p, k);
                Vec_Int_t *vLits1 = Pdr_ManCubeToLits(p, k, pCubeMin, 1, 0);
                int RetValue1 = sat_solver_addclause(pSat, Vec_IntArray(vLits1), Vec_IntArray(vLits1) + Vec_IntSize(vLits1));
                assert(RetValue1 == 1);
                sat_solver_compress(pSat);
            }

            // get the ordering by decreasing priority
            pOrder = Pdr_ManSortByPriority(p, pCubeMin);
            j--;
        }

        if (p->pPars->fTwoRounds)
            for (j = 0; j < pCubeMin->nLits; j++)
            {
                // use ordering
                //        i = j;
                i = pOrder[j];

                // check init state
                assert(pCubeMin->Lits[i] != -1);
                if (Pdr_SetIsInit(pCubeMin, i))
                    continue;
                // try removing this literal
                Lit = pCubeMin->Lits[i];
                pCubeMin->Lits[i] = -1;
                RetValue = Pdr_ManCheckCube(p, k, pCubeMin, NULL, p->pPars->nConfLimit, 0, !p->pPars->fSimpleGeneral);
                if (RetValue == -1)
                {
                    Pdr_SetDeref(pCubeMin);
                    return -1;
                }
                pCubeMin->Lits[i] = Lit;
                if (RetValue == 0)
                    continue;

                // success - update the cube
                pCubeMin = Pdr_SetCreateFrom(pCubeTmp = pCubeMin, i);
                Pdr_SetDeref(pCubeTmp);
                assert(pCubeMin->nLits > 0);

                // get the ordering by decreasing priority
                pOrder = Pdr_ManSortByPriority(p, pCubeMin);
                j--;
            }
    }

    if (p->pPars->pRelFileName != NULL && p->pPars->fPredicateReplace)
    {
        if (!p->pPars->fIterativePredicate)
        {
            if (p->nPredicates > 0)
            {
                pCubePredicate = Pdr_ManEquivPredicateReplace(p, k, pCubeMin);
                if (pCubePredicate != NULL)
                {
                    // NULL or &pPred according to skipDown?
                    RetValue = Pdr_ManCheckCube(p, k, pCubePredicate, NULL, p->pPars->nConfLimit, 0, 1);
                    if (p->pPars->fVeryVerbose)
                    {
                        Abc_Print(1, "Original cube ");
                        Pdr_SetPrint(stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL);
                        Abc_Print(1, "\n");
                        Abc_Print(1, "Equiv-Predicate cube ");
                        Pdr_SetPrint(stdout, pCubePredicate, Aig_ManRegNum(p->pAig), NULL);
                        Abc_Print(1, "\n");
                    }
                    if (RetValue == -1)
                    {
                        Pdr_SetDeref(pCubeMin);
                        Pdr_SetDeref(pCubePredicate);
                        return -1;
                    }
                    else if (RetValue == 1)
                    {
                        Pdr_SetDeref(pCubeMin);
                        pCubeMin = pCubePredicate;
                        if (p->pPars->fVeryVerbose)
                            Abc_Print(1, "Successful Replacement of Equiv-Predicate\n");
                        p->nPCubes++;
                    }
                    else if (RetValue == 0)
                        Pdr_SetDeref(pCubePredicate);
                }
            }
            if (p->nEqinitPredicates > 0)
            {
                pCubePredicate = Pdr_ManEqInitPredicateReplace(p, k, pCubeMin);
                if (pCubePredicate != NULL)
                {
                    // NULL or &pPred according to skipDown?
                    RetValue = Pdr_ManCheckCube(p, k, pCubePredicate, NULL, p->pPars->nConfLimit, 0, 1);
                    if (p->pPars->fVeryVerbose)
                    {
                        Abc_Print(1, "Original cube ");
                        Pdr_SetPrint(stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL);
                        Abc_Print(1, "\n");
                        Abc_Print(1, "EqInit-Predicate cube ");
                        Pdr_SetPrint(stdout, pCubePredicate, Aig_ManRegNum(p->pAig), NULL);
                        Abc_Print(1, "\n");
                    }
                    if (RetValue == -1)
                    {
                        Pdr_SetDeref(pCubeMin);
                        Pdr_SetDeref(pCubePredicate);
                        return -1;
                    }
                    else if (RetValue == 1)
                    {
                        Pdr_SetDeref(pCubeMin);
                        pCubeMin = pCubePredicate;
                        if (p->pPars->fVeryVerbose)
                            Abc_Print(1, "Successful Replacement of EqInit-Predicate\n");
                        // p->nPCubes++;
                    }
                    else if (RetValue == 0)
                        Pdr_SetDeref(pCubePredicate);
                }
            }
        }
        else
        { // iterative predicate replacement
            if (p->nPredicates > 0)
            {
                RetValue = Pdr_ManEquivIterPredicateReplace(p, k, pCubeMin, &pCubePredicate);
                if (pCubePredicate)
                    assert(Pdr_ManCheckCube(p, k, pCubePredicate, NULL, p->pPars->nConfLimit, 1, 0) == 1);
                if (RetValue == -1)
                {
                    Pdr_SetDeref(pCubeMin);
                    Pdr_SetDeref(pCubePredicate);
                    return -1;
                }
                else if (RetValue == 1)
                {
                    assert(pCubePredicate);
                    if (p->pPars->fVeryVerbose)
                    {
                        Abc_Print(1, "Original cube ");
                        Pdr_SetPrint(stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL);
                        Abc_Print(1, "\n");
                        Abc_Print(1, "Equiv-Predicate cube ");
                        Pdr_SetPrint(stdout, pCubePredicate, Aig_ManRegNum(p->pAig), NULL);
                        Abc_Print(1, "\n");
                        Abc_Print(1, "Successful Replacement\n");
                    }
                    Pdr_SetDeref(pCubeMin);
                    pCubeMin = pCubePredicate;
                    p->nPCubes++;
                }
                else if (RetValue == 0)
                    assert(pCubePredicate == NULL);
            }
            if (p->nEqinitPredicates > 0)
            {
                RetValue = Pdr_ManEqInitIterPredicateReplace(p, k, pCubeMin, &pCubePredicate);
                if (pCubePredicate)
                    assert(Pdr_ManCheckCube(p, k, pCubePredicate, NULL, p->pPars->nConfLimit, 1, 0) == 1);
                if (RetValue == -1)
                {
                    Pdr_SetDeref(pCubeMin);
                    Pdr_SetDeref(pCubePredicate);
                    return -1;
                }
                else if (RetValue == 1)
                {
                    assert(pCubePredicate);
                    if (p->pPars->fVeryVerbose)
                    {
                        Abc_Print(1, "Original cube ");
                        Pdr_SetPrint(stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL);
                        Abc_Print(1, "\n");
                        Abc_Print(1, "EqInit-Predicate cube ");
                        Pdr_SetPrint(stdout, pCubePredicate, Aig_ManRegNum(p->pAig), NULL);
                        Abc_Print(1, "\n");
                        Abc_Print(1, "Successful Replacement\n");
                    }
                    Pdr_SetDeref(pCubeMin);
                    pCubeMin = pCubePredicate;
                    // p->nPCubes++;
                }
                else if (RetValue == 0)
                    assert(pCubePredicate == NULL);
            }
        }
    }

        if (p->pPars->fVeryVerbose)
    {
        printf("Cube:\n");
        for (i = 0; i < pCubeMin->nLits; i++)
            printf("%d ", pCubeMin->Lits[i]);
        printf("\n");
    }

    assert(ppCubeMin != NULL);
    *ppCubeMin = pCubeMin;
    p->tGeneral += Abc_Clock() - clk;
    if (keep)
        Hash_IntFree(keep);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the state could be blocked.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManBlockCube(Pdr_Man_t *p, Pdr_Set_t *pCube)
{
    Pdr_Obl_t *pThis;
    Pdr_Set_t *pPred, *pCubeMin, *pCubeMinSym;
    int i, k, RetValue, Prio = ABC_INFINITY, Counter = 0;
    int kMax = Vec_PtrSize(p->vSolvers) - 1;
    abctime clk;
    p->nBlocks++;
    // create first proof obligation
    //    assert( p->pQueue == NULL );
    pThis = Pdr_OblStart(kMax, Prio--, pCube, NULL); // consume ref
    Pdr_QueuePush(p, pThis);
    // try to solve it recursively
    while (!Pdr_QueueIsEmpty(p))
    {
        Counter++;
        pThis = Pdr_QueueHead(p);
        if (pThis->iFrame == 0 || (p->pPars->fUseAbs && Pdr_SetIsInit(pThis->pState, -1)))
            return 0;             // SAT
        if (pThis->iFrame > kMax) // finished this level
            return 1;
        if (p->nQueLim && p->nQueCur >= p->nQueLim)
        {
            p->nQueLim = p->nQueLim * 3 / 2;
            Pdr_QueueStop(p);
            return 1; // restart
        }
        pThis = Pdr_QueuePop(p);
        assert(pThis->iFrame > 0);
        assert(!Pdr_SetIsInit(pThis->pState, -1));
        if (p->pPars->fVeryVerbose)
        {
            Abc_Print(1, "Handling proof obligation cube ");
            Pdr_SetPrint(stdout, pThis->pState, Aig_ManRegNum(p->pAig), NULL);
            Abc_Print(1, " at frame %d\n", pThis->iFrame);
        }
        p->iUseFrame = Abc_MinInt(p->iUseFrame, pThis->iFrame);
        clk = Abc_Clock();
        // check if the cube is alraedy contained syntactically
        if (Pdr_ManCheckContainment(p, pThis->iFrame, pThis->pState))
        {
            p->tContain += Abc_Clock() - clk;
            Pdr_OblDeref(pThis);
            continue;
        }
        p->tContain += Abc_Clock() - clk;

        // check if the cube is already contained using sat solver
        // This is checking a sat query that (R_k && !c) is satisfiable
        RetValue = Pdr_ManCheckCubeCs(p, pThis->iFrame, pThis->pState);
        if (RetValue == -1) // resource limit is reached
        {
            Pdr_OblDeref(pThis);
            return -1;
        }
        if (RetValue) // cube is blocked by clauses in this frame
        {
            Pdr_OblDeref(pThis);
            continue;
        }

        // check if the cube holds with relative induction
        pCubeMin = NULL;
        pCubeMinSym = NULL;
        RetValue = Pdr_ManGeneralize(p, pThis->iFrame - 1, pThis->pState, &pPred, &pCubeMin);
        if (RetValue == -1) // resource limit is reached
        {
            Pdr_OblDeref(pThis);
            return -1;
        }
        if (RetValue) // cube is blocked inductively in this frame
        {
            assert(pCubeMin != NULL);
            // k is the last frame where pCubeMin holds
            k = pThis->iFrame;
            int k2 = pThis->iFrame;
            // check other frames
            assert(pPred == NULL);
            for (k = pThis->iFrame; k < kMax; k++)
            {
                RetValue = Pdr_ManCheckCube(p, k, pCubeMin, NULL, 0, 0, 1);
                if (RetValue == -1)
                {
                    Pdr_OblDeref(pThis);
                    return -1;
                }
                if (!RetValue)
                    break;
            }
            // add new clause
            if (p->pPars->fVeryVerbose)
            {
                Abc_Print(1, "Adding cube ");
                Pdr_SetPrint(stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL);
                Abc_Print(1, " to frame %d.\n", k);
            }
            // set priority flops
            for (i = 0; i < pCubeMin->nLits; i++)
            {
                assert(pCubeMin->Lits[i] >= 0);
                assert((pCubeMin->Lits[i] / 2) < Aig_ManRegNum(p->pAig));
                if ((Vec_IntEntry(p->vPrio, pCubeMin->Lits[i] / 2) >> p->nPrioShift) == 0)
                    p->nAbsFlops++;
                Vec_IntAddToEntry(p->vPrio, pCubeMin->Lits[i] / 2, 1 << p->nPrioShift);
            }
            Vec_VecPush(p->vClauses, k, pCubeMin); // consume ref
            p->nCubes++;

            // add clause
            for (i = 1; i <= k; i++)
            {
                Pdr_ManSolverAddClause(p, i, pCubeMin);
            }

            // if (p->pPars->pRelFileName != NULL && p->pPars->fUseSymmetry)
            // {
            //     pCubeMinSym = Pdr_ManSymmetricCube(p, pCubeMin);
            // }
            // else
            //     pCubeMinSym = NULL;
            // if (pCubeMinSym)
            // {
            //     // Abc_Print(1, "Checking symmetric cube ");
            //     // Pdr_SetPrint(stdout, pCubeMinSym, Aig_ManRegNum(p->pAig), NULL);
            //     // Abc_Print(1, " from frame %d to %d.\n", k2, k);
            //     // for (k2 = pThis->iFrame; k2 < kMax; k2++)
            //     // {
            //     //     RetValue = Pdr_ManCheckCube(p, k2, pCubeMinSym, NULL, 0, 0, 1);
            //     //     if (RetValue == -1)
            //     //     {
            //     //         Pdr_OblDeref(pThis);
            //     //         return -1;
            //     //     }
            //     //     if (!RetValue)
            //     //         break;
            //     // }
            //     RetValue = 1;//Pdr_ManCheckCube(p, k - 1, pCubeMinSym, NULL, 0, 0, 1);
            //     if (RetValue == -1)
            //     {
            //         Pdr_OblDeref(pThis);
            //         return -1;
            //     }
            //     else if (RetValue == 0)
            //     {
            //         Abc_Print(1, "Failing symmetric cube ");
            //         Pdr_SetPrint(stdout, pCubeMinSym, Aig_ManRegNum(p->pAig), NULL);
            //         Abc_Print(1, " in frame %d.\n", k);
            //         Pdr_SetDeref(pCubeMinSym);
            //         pCubeMinSym = NULL;
            //         if (p->pPars->fVeryVerbose)
            //             Pdr_ManPrintClauses(p, 0);
            //         // return -1;
            //     }
            //     else
            //     {
            //         if (p->pPars->fVeryVerbose)
            //         {
            //             Abc_Print(1, "Adding symmetric cube ");
            //             Pdr_SetPrint(stdout, pCubeMinSym, Aig_ManRegNum(p->pAig), NULL);
            //             Abc_Print(1, " to frame %d.\n", k);
            //         }
            //         // set priority flops
            //         for (i = 0; i < pCubeMinSym->nLits; i++)
            //         {
            //             assert(pCubeMinSym->Lits[i] >= 0);
            //             assert((pCubeMinSym->Lits[i] / 2) < Aig_ManRegNum(p->pAig));
            //             if ((Vec_IntEntry(p->vPrio, pCubeMinSym->Lits[i] / 2) >> p->nPrioShift) == 0)
            //                 p->nAbsFlops++;
            //             Vec_IntAddToEntry(p->vPrio, pCubeMinSym->Lits[i] / 2, 1 << p->nPrioShift);
            //         }
            //         Vec_VecPush(p->vClauses, k, pCubeMinSym); // consume ref
            //         p->nCubes++;
            //     }
            // }
            // // add clause
            // for (i = 1; i <= k; i++)
            // {
            //     // Pdr_ManSolverAddClause(p, i, pCubeMin);
            //     if (pCubeMinSym)
            //         Pdr_ManSolverAddClause(p, i, pCubeMinSym);
            // }
            // schedule proof obligation
            if ((k < kMax || p->pPars->fReuseProofOblig) && !p->pPars->fShortest)
            {
                pThis->iFrame = k + 1;
                pThis->prio = Prio--;
                Pdr_QueuePush(p, pThis);
            }
            else
            {
                Pdr_OblDeref(pThis);
            }
        }
        else
        {
            assert(pCubeMin == NULL);
            assert(pCubeMinSym == NULL);
            assert(pPred != NULL);
            pThis->prio = Prio--;
            Pdr_QueuePush(p, pThis);
            pThis = Pdr_OblStart(pThis->iFrame - 1, Prio--, pPred, Pdr_OblRef(pThis));
            Pdr_QueuePush(p, pThis);
        }

        // check termination
        if (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId))
            return -1;
        if (p->timeToStop && Abc_Clock() > p->timeToStop)
            return -1;
        if (p->timeToStopOne && Abc_Clock() > p->timeToStopOne)
            return -1;
        if (p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC)
            return -1;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManSolveInt(Pdr_Man_t *p)
{
    int fPrintClauses = 0;
    Pdr_Set_t *pCube = NULL;
    Aig_Obj_t *pObj;
    Abc_Cex_t *pCexNew;
    int iFrame, RetValue = -1;
    int nOutDigits = Abc_Base10Log(Saig_ManPoNum(p->pAig));
    abctime clkStart = Abc_Clock(), clkOne = 0;
    p->timeToStop = p->pPars->nTimeOut ? p->pPars->nTimeOut * CLOCKS_PER_SEC + Abc_Clock() : 0;
    assert(Vec_PtrSize(p->vSolvers) == 0);
    // in the multi-output mode, mark trivial POs (those fed by const0) as solved
    if (p->pPars->fSolveAll)
        Saig_ManForEachPo(p->pAig, pObj, iFrame) if (Aig_ObjChild0(pObj) == Aig_ManConst0(p->pAig))
        {
            Vec_IntWriteEntry(p->pPars->vOutMap, iFrame, 1); // unsat
            p->pPars->nProveOuts++;
            if (p->pPars->fUseBridge)
                Gia_ManToBridgeResult(stdout, 1, NULL, iFrame);
        }
    // create the first timeframe
    p->pPars->timeLastSolved = Abc_Clock();
    Pdr_ManCreateSolver(p, (iFrame = 0));
    while (1)
    {
        // Vec_IntPrint(p->vPrio);
        int fRefined = 0;
        if (p->pPars->fUseAbs && p->vAbsFlops == NULL && iFrame == 1)
        {
            //            int i, Prio;
            assert(p->vAbsFlops == NULL);
            p->vAbsFlops = Vec_IntStart(Saig_ManRegNum(p->pAig));
            p->vMapFf2Ppi = Vec_IntStartFull(Saig_ManRegNum(p->pAig));
            p->vMapPpi2Ff = Vec_IntAlloc(100);
            //            Vec_IntForEachEntry( p->vPrio, Prio, i )
            //                if ( Prio >> p->nPrioShift  )
            //                    Vec_IntWriteEntry( p->vAbsFlops, i, 1 );
        }
        // if ( p->pPars->fUseAbs && p->vAbsFlops )
        //     printf( "Starting frame %d with %d (%d) flops.\n", iFrame, Vec_IntCountPositive(p->vAbsFlops), Vec_IntCountPositive(p->vPrio) );
        p->nFrames = iFrame;
        assert(iFrame == Vec_PtrSize(p->vSolvers) - 1);
        p->iUseFrame = Abc_MaxInt(iFrame, 1);
        Saig_ManForEachPo(p->pAig, pObj, p->iOutCur)
        {
            if (p->iOutCur == 1) // Skip the 2nd PO, which is a dummy output.
                continue;
            // skip disproved outputs
            if (p->vCexes && Vec_PtrEntry(p->vCexes, p->iOutCur))
                continue;
            // skip output whose time has run out
            if (p->pTime4Outs && p->pTime4Outs[p->iOutCur] == 0)
                continue;
            // check if the output is trivially solved
            if (Aig_ObjChild0(pObj) == Aig_ManConst0(p->pAig))
                continue;
            // check if the output is trivially solved
            if (Aig_ObjChild0(pObj) == Aig_ManConst1(p->pAig))
            {
                if (!p->pPars->fSolveAll)
                {
                    pCexNew = Abc_CexMakeTriv(Aig_ManRegNum(p->pAig), Saig_ManPiNum(p->pAig), Saig_ManPoNum(p->pAig), iFrame * Saig_ManPoNum(p->pAig) + p->iOutCur);
                    p->pAig->pSeqModel = pCexNew;
                    return 0; // SAT
                }
                pCexNew = (p->pPars->fUseBridge || p->pPars->fStoreCex) ? Abc_CexMakeTriv(Aig_ManRegNum(p->pAig), Saig_ManPiNum(p->pAig), Saig_ManPoNum(p->pAig), iFrame * Saig_ManPoNum(p->pAig) + p->iOutCur) : (Abc_Cex_t *)(ABC_PTRINT_T)1;
                p->pPars->nFailOuts++;
                if (p->pPars->vOutMap)
                    Vec_IntWriteEntry(p->pPars->vOutMap, p->iOutCur, 0);
                if (!p->pPars->fNotVerbose)
                    Abc_Print(1, "Output %*d was trivially asserted in frame %2d (solved %*d out of %*d outputs).\n",
                              nOutDigits, p->iOutCur, iFrame, nOutDigits, p->pPars->nFailOuts, nOutDigits, Saig_ManPoNum(p->pAig));
                assert(Vec_PtrEntry(p->vCexes, p->iOutCur) == NULL);
                if (p->pPars->fUseBridge)
                    Gia_ManToBridgeResult(stdout, 0, pCexNew, pCexNew->iPo);
                Vec_PtrWriteEntry(p->vCexes, p->iOutCur, pCexNew);
                if (p->pPars->pFuncOnFail && p->pPars->pFuncOnFail(p->iOutCur, p->pPars->fStoreCex ? (Abc_Cex_t *)Vec_PtrEntry(p->vCexes, p->iOutCur) : NULL))
                {
                    if (p->pPars->fVerbose)
                        Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
                    if (!p->pPars->fSilent)
                        Abc_Print(1, "Quitting due to callback on fail in frame %d.\n", iFrame);
                    p->pPars->iFrame = iFrame;
                    return -1;
                }
                if (p->pPars->nFailOuts + p->pPars->nDropOuts == Saig_ManPoNum(p->pAig))
                    return p->pPars->nFailOuts ? 0 : -1; // SAT or UNDEC
                p->pPars->timeLastSolved = Abc_Clock();
                continue;
            }
            // try to solve this output
            if (p->pTime4Outs)
            {
                assert(p->pTime4Outs[p->iOutCur] > 0);
                clkOne = Abc_Clock();
                p->timeToStopOne = p->pTime4Outs[p->iOutCur] + Abc_Clock();
            }
            while (1)
            {
                if (p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC)
                {
                    if (p->pPars->fVerbose)
                        Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
                    if (!p->pPars->fSilent)
                        Abc_Print(1, "Reached gap timeout (%d seconds) in frame %d.\n", p->pPars->nTimeOutGap, iFrame);
                    p->pPars->iFrame = iFrame;
                    return -1;
                }
                RetValue = Pdr_ManCheckCube(p, iFrame, NULL, &pCube, p->pPars->nConfLimit, 0, 1);
                if (RetValue == 1)
                    break;
                if (RetValue == -1)
                {
                    if (p->pPars->fVerbose)
                        Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
                    if (p->timeToStop && Abc_Clock() > p->timeToStop && !p->pPars->fSilent)
                        Abc_Print(1, "Reached timeout (%d seconds) in frame %d.\n", p->pPars->nTimeOut, iFrame);
                    else if (p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC)
                        Abc_Print(1, "Reached gap timeout (%d seconds) in frame %d.\n", p->pPars->nTimeOutGap, iFrame);
                    else if (p->timeToStopOne && Abc_Clock() > p->timeToStopOne)
                    {
                        Pdr_QueueClean(p);
                        pCube = NULL;
                        break; // keep solving
                    }
                    else if (p->pPars->nConfLimit)
                        Abc_Print(1, "Reached conflict limit (%d) in frame %d.\n", p->pPars->nConfLimit, iFrame);
                    else if (p->pPars->fVerbose)
                        Abc_Print(1, "Computation cancelled by the callback in frame %d.\n", iFrame);
                    p->pPars->iFrame = iFrame;
                    return -1;
                }
                if (RetValue == 0)
                {
                    RetValue = Pdr_ManBlockCube(p, pCube);
                    if (RetValue == -1)
                    {
                        if (p->pPars->fVerbose)
                            Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
                        if (p->timeToStop && Abc_Clock() > p->timeToStop && !p->pPars->fSilent)
                            Abc_Print(1, "Reached timeout (%d seconds) in frame %d.\n", p->pPars->nTimeOut, iFrame);
                        else if (p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC)
                            Abc_Print(1, "Reached gap timeout (%d seconds) in frame %d.\n", p->pPars->nTimeOutGap, iFrame);
                        else if (p->timeToStopOne && Abc_Clock() > p->timeToStopOne)
                        {
                            Pdr_QueueClean(p);
                            pCube = NULL;
                            break; // keep solving
                        }
                        else if (p->pPars->nConfLimit)
                            Abc_Print(1, "Reached conflict limit (%d) in frame %d.\n", p->pPars->nConfLimit, iFrame);
                        else if (p->pPars->fVerbose)
                            Abc_Print(1, "Computation cancelled by the callback in frame %d.\n", iFrame);
                        p->pPars->iFrame = iFrame;
                        return -1;
                    }
                    if (RetValue == 0)
                    {
                        if (fPrintClauses)
                        {
                            Abc_Print(1, "*** Clauses after frame %d:\n", iFrame);
                            Pdr_ManPrintClauses(p, 0);
                        }
                        if (p->pPars->fVerbose && !p->pPars->fUseAbs)
                            Pdr_ManPrintProgress(p, !p->pPars->fSolveAll, Abc_Clock() - clkStart);
                        p->pPars->iFrame = iFrame;
                        if (!p->pPars->fSolveAll)
                        {
                            abctime clk = Abc_Clock();
                            Abc_Cex_t *pCex = Pdr_ManDeriveCexAbs(p);
                            p->tAbs += Abc_Clock() - clk;
                            if (pCex == NULL)
                            {
                                assert(p->pPars->fUseAbs);
                                Pdr_QueueClean(p);
                                pCube = NULL;
                                fRefined = 1;
                                break; // keep solving
                            }
                            p->pAig->pSeqModel = pCex;
                            return 0; // SAT
                        }
                        p->pPars->nFailOuts++;
                        pCexNew = (p->pPars->fUseBridge || p->pPars->fStoreCex) ? Pdr_ManDeriveCex(p) : (Abc_Cex_t *)(ABC_PTRINT_T)1;
                        if (p->pPars->vOutMap)
                            Vec_IntWriteEntry(p->pPars->vOutMap, p->iOutCur, 0);
                        assert(Vec_PtrEntry(p->vCexes, p->iOutCur) == NULL);
                        if (p->pPars->fUseBridge)
                            Gia_ManToBridgeResult(stdout, 0, pCexNew, pCexNew->iPo);
                        Vec_PtrWriteEntry(p->vCexes, p->iOutCur, pCexNew);
                        if (p->pPars->pFuncOnFail && p->pPars->pFuncOnFail(p->iOutCur, p->pPars->fStoreCex ? (Abc_Cex_t *)Vec_PtrEntry(p->vCexes, p->iOutCur) : NULL))
                        {
                            if (p->pPars->fVerbose)
                                Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
                            if (!p->pPars->fSilent)
                                Abc_Print(1, "Quitting due to callback on fail in frame %d.\n", iFrame);
                            p->pPars->iFrame = iFrame;
                            return -1;
                        }
                        if (!p->pPars->fNotVerbose)
                            Abc_Print(1, "Output %*d was asserted in frame %2d (%2d) (solved %*d out of %*d outputs).\n",
                                      nOutDigits, p->iOutCur, iFrame, iFrame, nOutDigits, p->pPars->nFailOuts, nOutDigits, Saig_ManPoNum(p->pAig));
                        if (p->pPars->nFailOuts == Saig_ManPoNum(p->pAig))
                            return 0; // all SAT
                        Pdr_QueueClean(p);
                        pCube = NULL;
                        break; // keep solving
                    }
                    if (p->pPars->fVerbose)
                        Pdr_ManPrintProgress(p, 0, Abc_Clock() - clkStart);
                }
            }
            if (fRefined)
                break;
            if (p->pTime4Outs)
            {
                abctime timeSince = Abc_Clock() - clkOne;
                assert(p->pTime4Outs[p->iOutCur] > 0);
                p->pTime4Outs[p->iOutCur] = (p->pTime4Outs[p->iOutCur] > timeSince) ? p->pTime4Outs[p->iOutCur] - timeSince : 0;
                if (p->pTime4Outs[p->iOutCur] == 0 && Vec_PtrEntry(p->vCexes, p->iOutCur) == NULL) // undecided
                {
                    p->pPars->nDropOuts++;
                    if (p->pPars->vOutMap)
                        Vec_IntWriteEntry(p->pPars->vOutMap, p->iOutCur, -1);
                    if (!p->pPars->fNotVerbose)
                        Abc_Print(1, "Timing out on output %*d in frame %d.\n", nOutDigits, p->iOutCur, iFrame);
                }
                p->timeToStopOne = 0;
            }
        }
        if (p->pPars->fUseAbs && p->vAbsFlops && !fRefined)
        {
            int i, Used;
            Vec_IntForEachEntry(p->vAbsFlops, Used, i) if (Used && (Vec_IntEntry(p->vPrio, i) >> p->nPrioShift) == 0)
                Vec_IntWriteEntry(p->vAbsFlops, i, 0);
        }
        if (p->pPars->fVerbose)
            Pdr_ManPrintProgress(p, !fRefined, Abc_Clock() - clkStart);
        if (fRefined)
            continue;
        // if ( p->pPars->fUseAbs && p->vAbsFlops )
        //     printf( "Finished frame %d with %d (%d) flops.\n", iFrame, Vec_IntCountPositive(p->vAbsFlops), Vec_IntCountPositive(p->vPrio) );
        //  open a new timeframe
        p->nQueLim = p->pPars->nRestLimit;
        assert(pCube == NULL);
        Pdr_ManSetPropertyOutput(p, iFrame);
        Pdr_ManCreateSolver(p, ++iFrame);
        if (fPrintClauses)
        {
            Abc_Print(1, "*** Clauses after frame %d:\n", iFrame);
            Pdr_ManPrintClauses(p, 0);
        }
        // push clauses into this timeframe
        RetValue = Pdr_ManPushClauses(p);
        if (RetValue == -1)
        {
            if (p->pPars->fVerbose)
                Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
            if (!p->pPars->fSilent)
            {
                if (p->timeToStop && Abc_Clock() > p->timeToStop)
                    Abc_Print(1, "Reached timeout (%d seconds) in frame %d.\n", p->pPars->nTimeOut, iFrame);
                else
                    Abc_Print(1, "Reached conflict limit (%d) in frame %d.\n", p->pPars->nConfLimit, iFrame);
            }
            p->pPars->iFrame = iFrame;
            return -1;
        }
        if (RetValue)
        {
            if (p->pPars->fVerbose)
                Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
            if (!p->pPars->fSilent)
                Pdr_ManReportInvariant(p);
            if (!p->pPars->fSilent)
                Pdr_ManVerifyInvariant(p);
            p->pPars->iFrame = iFrame;
            // count the number of UNSAT outputs
            p->pPars->nProveOuts = Saig_ManPoNum(p->pAig) - p->pPars->nFailOuts - p->pPars->nDropOuts;
            // convert previously 'unknown' into 'unsat'
            if (p->pPars->vOutMap)
                for (iFrame = 0; iFrame < Saig_ManPoNum(p->pAig); iFrame++)
                    if (Vec_IntEntry(p->pPars->vOutMap, iFrame) == -2) // unknown
                    {
                        Vec_IntWriteEntry(p->pPars->vOutMap, iFrame, 1); // unsat
                        if (p->pPars->fUseBridge)
                            Gia_ManToBridgeResult(stdout, 1, NULL, iFrame);
                    }
            if (p->pPars->nProveOuts == Saig_ManPoNum(p->pAig))
                return 1; // UNSAT
            if (p->pPars->nFailOuts > 0)
                return 0; // SAT
            return -1;
        }
        if (p->pPars->fVerbose)
            Pdr_ManPrintProgress(p, 0, Abc_Clock() - clkStart);

        // check termination
        if (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId))
        {
            p->pPars->iFrame = iFrame;
            return -1;
        }
        if (p->timeToStop && Abc_Clock() > p->timeToStop)
        {
            if (fPrintClauses)
            {
                Abc_Print(1, "*** Clauses after frame %d:\n", iFrame);
                Pdr_ManPrintClauses(p, 0);
            }
            if (p->pPars->fVerbose)
                Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
            if (!p->pPars->fSilent)
                Abc_Print(1, "Reached timeout (%d seconds) in frame %d.\n", p->pPars->nTimeOut, iFrame);
            p->pPars->iFrame = iFrame;
            return -1;
        }
        if (p->pPars->nTimeOutGap && p->pPars->timeLastSolved && Abc_Clock() > p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC)
        {
            if (fPrintClauses)
            {
                Abc_Print(1, "*** Clauses after frame %d:\n", iFrame);
                Pdr_ManPrintClauses(p, 0);
            }
            if (p->pPars->fVerbose)
                Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
            if (!p->pPars->fSilent)
                Abc_Print(1, "Reached gap timeout (%d seconds) in frame %d.\n", p->pPars->nTimeOutGap, iFrame);
            p->pPars->iFrame = iFrame;
            return -1;
        }
        if (p->pPars->nFrameMax && iFrame >= p->pPars->nFrameMax)
        {
            if (p->pPars->fVerbose)
                Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
            if (!p->pPars->fSilent)
                Abc_Print(1, "Reached limit on the number of timeframes (%d).\n", p->pPars->nFrameMax);
            p->pPars->iFrame = iFrame;
            return -1;
        }
    }
    assert(0);
    return -1;
}

/**Function*************************************************************
  Synopsis    []

  Description [Read the initial priorities from the file.]

  SideEffects []

  SeeAlso     []
***********************************************************************/
Vec_Int_t *Pdr_ManReadPriorities(char *pFileName, Aig_Man_t *pAig, int maxPrio)
{
    Vec_Int_t *vPrioInit;
    vPrioInit = Vec_IntStart(Aig_ManRegNum(pAig));
    FILE *pFile = fopen(pFileName, "r");
    int vFlop;

    if (pFile == NULL)
    {
        fprintf(stdout, "Cannot open input file \"%s\". ", pFileName);
        return NULL;
    }

    while (fscanf(pFile, "%d", &vFlop) == 1)
    {
        vPrioInit->pArray[vFlop] = maxPrio;
    }

    fclose(pFile);
    Vec_IntPrint(vPrioInit);
    return vPrioInit;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManSolve(Aig_Man_t *pAig, Pdr_Par_t *pPars)
{
    Pdr_Man_t *p;
    int k, RetValue;
    abctime clk = Abc_Clock();
    Vec_Int_t *vPrioInit = NULL;
    if (pPars->nTimeOutOne && !pPars->fSolveAll)
        pPars->nTimeOutOne = 0;
    if (pPars->nTimeOutOne && pPars->nTimeOut == 0)
        pPars->nTimeOut = pPars->nTimeOutOne * Saig_ManPoNum(pAig) / 1000 + (int)((pPars->nTimeOutOne * Saig_ManPoNum(pAig) % 1000) > 0);
    if (pPars->fVerbose)
    {
        //    Abc_Print( 1, "Running PDR by Niklas Een (aka IC3 by Aaron Bradley) with these parameters:\n" );
        Abc_Print(1, "VarMax = %d. FrameMax = %d. QueMax = %d. TimeMax = %d. ",
                  pPars->nRecycle,
                  pPars->nFrameMax,
                  pPars->nRestLimit,
                  pPars->nTimeOut);
        Abc_Print(1, "MonoCNF = %s. SkipGen = %s. SolveAll = %s.\n",
                  pPars->fMonoCnf ? "yes" : "no",
                  pPars->fSkipGeneral ? "yes" : "no",
                  pPars->fSolveAll ? "yes" : "no");
    }
    ABC_FREE(pAig->pSeqModel);
    if (pPars->pPriFileName != NULL)
    {
        vPrioInit = Pdr_ManReadPriorities(pPars->pPriFileName, pAig, 3000000);
        if (vPrioInit == NULL)
            return -1;
    }

    // Note: the third input here can be an initialized priority array
    p = Pdr_ManStart(pAig, pPars, vPrioInit);

    RetValue = Pdr_ManSolveInt(p);
    if (RetValue == 0)
        assert(pAig->pSeqModel != NULL || p->vCexes != NULL);
    if (p->vCexes)
    {
        assert(p->pAig->vSeqModelVec == NULL);
        p->pAig->vSeqModelVec = p->vCexes;
        p->vCexes = NULL;
    }
    if (p->pPars->fDumpInv)
    {
        char *pFileName = pPars->pInvFileName ? pPars->pInvFileName : Extra_FileNameGenericAppend(p->pAig->pName, "_inv.pla");
        Abc_FrameSetInv(Pdr_ManDeriveInfinityClauses(p, RetValue != 1));
        Pdr_ManDumpClauses(p, pFileName, RetValue == 1);
        printf("Dumped inductive invariant in file \"%s\".\n", pFileName);
    }
    else if (RetValue == 1)
        Abc_FrameSetInv(Pdr_ManDeriveInfinityClauses(p, RetValue != 1));
    p->tTotal += Abc_Clock() - clk;
    Pdr_ManStop(p);
    pPars->iFrame--;
    // convert all -2 (unknown) entries into -1 (undec)
    if (pPars->vOutMap)
        for (k = 0; k < Saig_ManPoNum(pAig); k++)
            if (Vec_IntEntry(pPars->vOutMap, k) == -2)    // unknown
                Vec_IntWriteEntry(pPars->vOutMap, k, -1); // undec
    if (pPars->fUseBridge)
        Gia_ManToBridgeAbort(stdout, 7, (unsigned char *)"timeout");
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END