/**CFile****************************************************************

  FileName    [pdrSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [SAT solver procedures.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdrSat.c,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdrInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates new SAT solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver *Pdr_ManCreateSolver(Pdr_Man_t *p, int k)
{
    sat_solver *pSat;
    Aig_Obj_t *pObj;
    int i;
    assert(Vec_PtrSize(p->vSolvers) == k);
    assert(Vec_VecSize(p->vClauses) == k);
    assert(Vec_IntSize(p->vActVars) == k);
    // create new solver
    //    pSat = sat_solver_new();
    pSat = zsat_solver_new_seed(p->pPars->nRandomSeed);
    pSat = Pdr_ManNewSolver(pSat, p, k, (int)(k == 0));
    Vec_PtrPush(p->vSolvers, pSat);
    Vec_VecExpand(p->vClauses, k);
    Vec_IntPush(p->vActVars, 0);
    // add property cone
    Saig_ManForEachPo(p->pAig, pObj, i)
        Pdr_ObjSatVar(p, k, 1, pObj);

    if (p->pPars->pRelFileName != NULL)
    {
        Pdr_ManAddPredicateSemantic(p, k);
    }

    return pSat;
}

/**Function*************************************************************

  Synopsis    [Add the semantic assumption for predicate variables to the sat solver]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManAddPredicateSemantic(Pdr_Man_t *p, int k)
{
    Pdr_Set_t *tempCube;
    tempCube = (Pdr_Set_t *)ABC_ALLOC(char, sizeof(Pdr_Set_t) + 3 * sizeof(int));
    tempCube->nLits = 3;
    tempCube->nTotal = 3;
    tempCube->nRefs = 1;
    tempCube->Sign = 0;

    int reg, symReg, predicateReg;

    for (reg = 0; reg < p->pAig->nRegs; reg++)
    {
        symReg = p->vSymMap->pArray[reg];
        predicateReg = Vec_IntEntry(p->vEquivMap, reg);
        if (predicateReg == -1)
        {
            continue;
        }
        
        // Add the (!predicate -> equal) constraint
        tempCube->Lits[0] = Abc_Var2Lit(reg, 1);
        tempCube->Lits[1] = Abc_Var2Lit(symReg, 0);
        tempCube->Lits[2] = Abc_Var2Lit(predicateReg, 1);

        Pdr_ManSolverAddClause(p, k, tempCube);

        // Add the (equal -> !predciate) constraint
        if (reg > symReg) {
            tempCube->Lits[0] = Abc_Var2Lit(reg, 0);
            tempCube->Lits[1] = Abc_Var2Lit(symReg, 0);
            tempCube->Lits[2] = Abc_Var2Lit(predicateReg, 0);
        }
        else {
            tempCube->Lits[0] = Abc_Var2Lit(reg, 0);
            tempCube->Lits[1] = Abc_Var2Lit(symReg, 1);
            tempCube->Lits[2] = Abc_Var2Lit(predicateReg, 1);
        }

        Pdr_ManSolverAddClause(p, k, tempCube);
    }
}


/**Function*************************************************************

  Synopsis    [Returns old or restarted solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
sat_solver *Pdr_ManFetchSolver(Pdr_Man_t *p, int k)
{
    sat_solver *pSat;
    Vec_Ptr_t *vArrayK;
    Pdr_Set_t *pCube;
    int i, j;
    pSat = Pdr_ManSolver(p, k);
    if (Vec_IntEntry(p->vActVars, k) < p->pPars->nRecycle)
        return pSat;
    assert(k < Vec_PtrSize(p->vSolvers) - 1);
    p->nStarts++;
    //    sat_solver_delete( pSat );
    //    pSat = sat_solver_new();
    //    sat_solver_restart( pSat );
    zsat_solver_restart_seed(pSat, p->pPars->nRandomSeed);
    // create new SAT solver
    pSat = Pdr_ManNewSolver(pSat, p, k, (int)(k == 0));
    // write new SAT solver
    Vec_PtrWriteEntry(p->vSolvers, k, pSat);
    Vec_IntWriteEntry(p->vActVars, k, 0);
    // set the property output
    Pdr_ManSetPropertyOutput(p, k);
    // add the clauses
    Vec_VecForEachLevelStart(p->vClauses, vArrayK, i, k)
        Vec_PtrForEachEntry(Pdr_Set_t *, vArrayK, pCube, j)
        {
            int isEmpty = 1;
            for (int j = 0; j < pCube->nLits; j++)
            {
                if (pCube->Lits[j] != -1)
                {
                    isEmpty = 0;
                    break;
                }
            }
            if (isEmpty)
            {
                Abc_Print(1, "Empty Cube found at frame %d\n", k);
                Pdr_ManPrintClauses(p, 0);
            }
            Pdr_ManSolverAddClause(p, k, pCube);
        }
    
    

    if (p->pPars->pRelFileName != NULL) {
        Pdr_ManAddPredicateSemantic(p, k);
    }

    return pSat;
}

/**Function*************************************************************

  Synopsis    [Converts SAT variables into register IDs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t *Pdr_ManLitsToCube(Pdr_Man_t *p, int k, int *pArray, int nArray)
{
    int i, RegId;
    Vec_IntClear(p->vLits);
    for (i = 0; i < nArray; i++)
    {
        RegId = Pdr_ObjRegNum(p, k, Abc_Lit2Var(pArray[i]));
        if (RegId == -1)
            continue;
        assert(RegId >= 0 && RegId < Aig_ManRegNum(p->pAig));
        Vec_IntPush(p->vLits, Abc_Var2Lit(RegId, !Abc_LitIsCompl(pArray[i])));
    }
    assert(Vec_IntSize(p->vLits) >= 0 && Vec_IntSize(p->vLits) <= nArray);
    return p->vLits;
}


/**Function*************************************************************

  Synopsis    [Converts the cube in terms of RO numbers into array of CNF literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t *Pdr_ManCubeToLits(Pdr_Man_t *p, int k, Pdr_Set_t *pCube, int fCompl, int fNext)
{
    Aig_Obj_t *pObj;
    int i, iVar, iVarMax = 0;
    abctime clk = Abc_Clock();
    Vec_IntClear(p->vLits);
    //    assert( !(fNext && fCompl) );
    for (i = 0; i < pCube->nLits; i++)
    {
        if (pCube->Lits[i] == -1)
        {
            continue;
        }
        if (fNext)
            pObj = Saig_ManLi(p->pAig, Abc_Lit2Var(pCube->Lits[i]));
        else
            pObj = Saig_ManLo(p->pAig, Abc_Lit2Var(pCube->Lits[i]));
        iVar = Pdr_ObjSatVar(p, k, fNext ? 2 - Abc_LitIsCompl(pCube->Lits[i]) : 3, pObj);
        assert(iVar >= 0);
        iVarMax = Abc_MaxInt(iVarMax, iVar);
        Vec_IntPush(p->vLits, Abc_Var2Lit(iVar, fCompl ^ Abc_LitIsCompl(pCube->Lits[i])));
    }
    if (p->vLits->nSize == 0)
    {
        Abc_Print(1, "Abnormal cube ");
        Pdr_SetPrint(stdout, pCube, Aig_ManRegNum(p->pAig), NULL);
        Abc_Print(1, "\n");
    }
    //    sat_solver_setnvars( Pdr_ManSolver(p, k), iVarMax + 1 );
    p->tCnf += Abc_Clock() - clk;
    return p->vLits;
}

/**Function*************************************************************

  Synopsis    [Sets the property output to 0 (sat) forever.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManSetPropertyOutput(Pdr_Man_t *p, int k)
{
    sat_solver *pSat;
    Aig_Obj_t *pObj;
    int Lit, RetValue, i;
    if (!p->pPars->fUsePropOut)
        return;
    pSat = Pdr_ManSolver(p, k);
    Saig_ManForEachPo(p->pAig, pObj, i)
    {
        // skip solved outputs
        if (p->vCexes && Vec_PtrEntry(p->vCexes, i))
            continue;
        // skip timedout outputs
        if (p->pPars->vOutMap && Vec_IntEntry(p->pPars->vOutMap, i) == -1)
            continue;
        Lit = Abc_Var2Lit(Pdr_ObjSatVar(p, k, 1, pObj), 1); // neg literal
        RetValue = sat_solver_addclause(pSat, &Lit, &Lit + 1);
        assert(RetValue == 1);
    }
    sat_solver_compress(pSat);
}

/**Function*************************************************************

  Synopsis    [Adds one clause in terms of ROs to the k-th SAT solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManSolverAddClause(Pdr_Man_t *p, int k, Pdr_Set_t *pCube)
{
    sat_solver *pSat;
    Vec_Int_t *vLits;
    int RetValue;
    pSat = Pdr_ManSolver(p, k);
    vLits = Pdr_ManCubeToLits(p, k, pCube, 1, 0);
    RetValue = sat_solver_addclause(pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits));
    assert(RetValue == 1);
    sat_solver_compress(pSat);
}

/**Function*************************************************************

  Synopsis    [Collects values of the RO/RI variables in k-th SAT solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr_ManCollectValues(Pdr_Man_t *p, int k, Vec_Int_t *vObjIds, Vec_Int_t *vValues)
{
    sat_solver *pSat;
    Aig_Obj_t *pObj;
    int iVar, i;
    Vec_IntClear(vValues);
    pSat = Pdr_ManSolver(p, k);
    Aig_ManForEachObjVec(vObjIds, p->pAig, pObj, i)
    {
        iVar = Pdr_ObjSatVar(p, k, 3, pObj);
        assert(iVar >= 0);
        Vec_IntPush(vValues, sat_solver_var_value(pSat, iVar));
    }
}

/**Function*************************************************************

  Synopsis    [Checks if the cube holds (UNSAT) in the given timeframe.]

  Description [Return 1/0 if cube or property are proved to hold/fail
  in k-th timeframe.  Returns the predecessor bad state in ppPred.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManCheckCubeCs(Pdr_Man_t *p, int k, Pdr_Set_t *pCube)
{
    sat_solver *pSat;
    Vec_Int_t *vLits;
    abctime Limit;
    int RetValue;
    pSat = Pdr_ManFetchSolver(p, k);
    vLits = Pdr_ManCubeToLits(p, k, pCube, 0, 0);
    Limit = sat_solver_set_runtime_limit(pSat, Pdr_ManTimeLimit(p));
    RetValue = sat_solver_solve(pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), 0, 0, 0, 0);
    sat_solver_set_runtime_limit(pSat, Limit);
    if (RetValue == l_Undef)
        return -1;
    return (RetValue == l_False);
}

/**Function*************************************************************

  Synopsis    [Checks if the cube holds (UNSAT) in the given timeframe.]

  Description [Return 1/0 if cube or property are proved to hold/fail
  in k-th timeframe.  Returns the predecessor bad state in ppPred.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr_ManCheckCube(Pdr_Man_t *p, int k, Pdr_Set_t *pCube, Pdr_Set_t **ppPred, int nConfLimit, int fTryConf, int fUseLit)
{
    // int fUseLit = 0;
    int fLitUsed = 0;
    sat_solver *pSat;
    Vec_Int_t *vLits;
    int Lit, RetValue;
    int iVar;
    Aig_Obj_t *pObj;
    abctime clk, Limit;
    p->nCalls++;
    // Abc_Print(1, "Fetch Solver\n");
    pSat = Pdr_ManFetchSolver(p, k);
    // Abc_Print(1, "Solver Fetched\n");
    Vec_Int_t *vSilenceClause = Vec_IntStart(2);
    if (pCube == NULL) // solve the property
    // This is checking whether !P && R_k is satisfiable, it does not involve transition relation
    {
        clk = Abc_Clock();
        vLits = Vec_IntStart(p->nSilenced + 1);
        if (p->pPars->fIncrPred && p->nSilenced > 0)
            {
                for (int i = 0; i < p->vSilenceCube->nLits; i++)
                {
                    if (p->vSilenceCube->Lits[i] == -1)
                    {
                        continue;
                    }
                    pObj = Saig_ManLo(p->pAig, Abc_Lit2Var(p->vSilenceCube->Lits[i]));
                    iVar = Pdr_ObjSatVar(p, k, 3, pObj);
                    vSilenceClause->pArray[1] = Abc_Var2Lit(iVar, 0);
                    RetValue = sat_solver_addclause(pSat, Vec_IntArray(vSilenceClause), Vec_IntArray(vSilenceClause) + 2);
                    assert(RetValue == 1);
                }
                // Abc_Print(1, "adding silenced lits to vLits\n");
            }
        vLits->pArray[0] = Abc_Var2Lit(Pdr_ObjSatVar(p, k, 2, Aig_ManCo(p->pAig, p->iOutCur)), 0); // pos literal (property fails)
        Limit = sat_solver_set_runtime_limit(pSat, Pdr_ManTimeLimit(p));
        RetValue = sat_solver_solve(pSat, vLits->pArray, vLits->pArray + vLits->nSize, nConfLimit, 0, 0, 0);
        sat_solver_set_runtime_limit(pSat, Limit);
        if (RetValue == l_Undef)
            return -1;
    }
    else // check relative containment in terms of next states
    // This is check that for a given cube c, whehter !c && R_k && Tr && c is satisfiable
    {
        if (fUseLit)
        {
            fLitUsed = 1;
            Vec_IntAddToEntry(p->vActVars, k, 1);
            // add the cube in terms of current state variables
            vLits = Pdr_ManCubeToLits(p, k, pCube, 1, 0);

            // add activation literal
            Lit = Abc_Var2Lit(Pdr_ManFreeVar(p, k), 0);
            // add activation literal
            Vec_IntPush(vLits, Lit);
            RetValue = sat_solver_addclause(pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits));
            assert(RetValue == 1);

            
            // add the cube of silenced predicates to the assumed literals
            if (p->pPars->fIncrPred && p->nSilenced > 0)
            {
                vSilenceClause->pArray[0] = Lit;
                for (int i = 0; i < p->vSilenceCube->nLits; i++)
                {
                    if (p->vSilenceCube->Lits[i] == -1)
                    {
                        continue;
                    }
                    pObj = Saig_ManLo(p->pAig, Abc_Lit2Var(p->vSilenceCube->Lits[i]));
                    iVar = Pdr_ObjSatVar(p, k, 3, pObj);
                    vSilenceClause->pArray[1] = Abc_Var2Lit(iVar, 0);
                    RetValue = sat_solver_addclause(pSat, Vec_IntArray(vSilenceClause), Vec_IntArray(vSilenceClause) + 2);
                    assert(RetValue == 1);
                }
                // Abc_Print(1, "adding silenced lits to vLits\n");
            }

            sat_solver_compress(pSat);
            // create assumptions
            vLits = Pdr_ManCubeToLits(p, k, pCube, 0, 1);
            // add activation literal
            Vec_IntPush(vLits, Abc_LitNot(Lit));
        }
        else
            vLits = Pdr_ManCubeToLits(p, k, pCube, 0, 1);
        
        


        // solve
        clk = Abc_Clock();
        Limit = sat_solver_set_runtime_limit(pSat, Pdr_ManTimeLimit(p));
        
        // for(int i = 0; i < p->nSilenced; i++){
        //     Vec_IntPush(vLits, Abc_Var2Lit(Pdr_ObjSatVar(p, k, 3, Saig_ManLo(p->pAig, p->vPredicatesSilence->pArray[i])), 0));
        // }
        RetValue = sat_solver_solve(pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), fTryConf ? p->pPars->nConfGenLimit : nConfLimit, 0, 0, 0);
        sat_solver_set_runtime_limit(pSat, Limit);
        if (RetValue == l_Undef)
        {
            if (fTryConf && p->pPars->nConfGenLimit)
                RetValue = l_True;
            else
                return -1;
        }
    }
    clk = Abc_Clock() - clk;
    p->tSat += clk;
    assert(RetValue != l_Undef);
    if (RetValue == l_False)
    {
        p->tSatUnsat += clk;
        p->nCallsU++;
        if (ppPred)
            *ppPred = NULL;
        RetValue = 1;
    }
    else // if ( RetValue == l_True )
    {
        p->tSatSat += clk;
        p->nCallsS++;
        if (ppPred)
        {
            abctime clk = Abc_Clock();
            if (p->pPars->fNewXSim)
                *ppPred = Txs3_ManTernarySim(p->pTxs3, k, pCube);
            else
                *ppPred = Pdr_ManTernarySim(p, k, pCube);
            p->tTsim += Abc_Clock() - clk;
            p->nXsimLits += (*ppPred)->nLits;
            p->nXsimRuns++;
        }
        RetValue = 0;
    }

    /* // for some reason, it does not work...
        if ( fLitUsed )
        {
            int RetValue;
            Lit = Abc_LitNot(Lit);
            RetValue = sat_solver_addclause( pSat, &Lit, &Lit + 1 );
            assert( RetValue == 1 );
            sat_solver_compress( pSat );
        }
    */
    return RetValue;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
