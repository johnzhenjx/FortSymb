module SymbolicPath where

import What4.Interface
import What4.Expr.Builder
import Language.Fortran.Util.Position (SrcSpan)

import Types
import Solver

addPathConditionAndKeepIfFeasible ::
    ExprBuilder t st fs ->
    Pred (ExprBuilder t st fs) ->
    SymState (ExprBuilder t st fs) a ->
    IO (Maybe (SymState (ExprBuilder t st fs) a))
addPathConditionAndKeepIfFeasible sym predicate state = do
    let newState = state { pathCond = predicate : pathCond state }
    feasible <- checkStateFeasibility sym newState
    if feasible
        then pure (Just newState)
        else pure Nothing


addObligationAndAssume ::
    ExprBuilder t st fs ->
    ObligationKind ->
    SrcSpan ->
    Pred (ExprBuilder t st fs) ->
    SymState (ExprBuilder t st fs) a ->
    IO (SymState (ExprBuilder t st fs) a)

addObligationAndAssume sym kind span predicate state = do
    let obligation = Obligation
                { obligationKind = kind
                , obligationSpan = span
                , obligationPredicate = predicate
                , obligationPath = pathCond state
                }

        stateWithObligation = state { obligations = obligation : obligations state }

    maybeContinuingState <-
        addPathConditionAndKeepIfFeasible sym predicate stateWithObligation

    case maybeContinuingState of
        Just continuingState -> pure continuingState
        Nothing ->
            pure stateWithObligation
                { executionStatus = ExecutionHalted (ObligationCannotHold kind span) }
