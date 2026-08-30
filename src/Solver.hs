module Solver where

import qualified Data.Map as Map

import What4.Interface
import What4.Expr.Builder
import What4.Expr
         ( ExprRangeBindings, GroundEvalFn, groundEval )

import What4.Solver
         (defaultLogData, withZ3, SatResult(..))
import What4.Protocol.SMTLib2
         (assume, sessionWriter, runCheckSat)

import Prelude hiding (EQ, LT, GT)

import Paths_FortSymb (getDataFileName)
import Types

import Control.Monad (filterM)


-- Converts a list of What4 predicates into their conjunction.
predicateOfCondList ::
    IsExprBuilder sym =>
    sym ->
    [Pred sym] ->
    IO (Pred sym)
predicateOfCondList sym conditions =
    case conditions of
        [] ->
            pure (truePred sym)

        predicate : remainingConditions -> do
            remainingPredicate <- predicateOfCondList sym remainingConditions
            andPred sym predicate remainingPredicate


z3Executable :: IO FilePath
z3Executable = getDataFileName "z3/bin/z3.exe"

--runs a solver query and handles the result while the Z3 session is open
--
--this is important because GroundEvalFn is only valid inside the withZ3 callback
withSolverResult ::
    ExprBuilder t st fs ->
    BoolExpr t ->
    (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a) -> --takes function for evaluating model
    IO a
withSolverResult sym predicate handleResult = do
    z3Path <- z3Executable
    withZ3 sym z3Path defaultLogData $ \session -> do
        assume (sessionWriter session) predicate
        runCheckSat session handleResult


--checks whether one symbolic state has satisfiable path condition list
checkStateFeasibility ::
    ExprBuilder t st fs ->
    SymState (ExprBuilder t st fs) a ->
    IO Bool
checkStateFeasibility sym state = do
    pathPred <- predicateOfCondList sym (pathCond state)

    withSolverResult sym pathPred $ \solverResult ->
        case solverResult of
            Sat _ -> pure True
            Unsat _ -> pure False
            Unknown -> error "Solver returned unknown while checking path feasibility"


--filters out states whose path conditions are unsatisfiable
keepFeasibleStates ::
    ExprBuilder t st fs ->
    [SymState (ExprBuilder t st fs) a] ->
    IO [SymState (ExprBuilder t st fs) a]
keepFeasibleStates sym states = do
    filterM (checkStateFeasibility sym) states



evaluateAllStateObligations ::
    ExprBuilder t st fs ->
    [SymState (ExprBuilder t st fs) a] ->
    IO
        [ [ ( Obligation (ExprBuilder t st fs)
            , ObligationResult
            )
          ]
        ]
evaluateAllStateObligations sym states =
    case states of
        [] -> pure []
        state : remainingStates -> do
            stateResults <- evaluateStateObligations sym state
            remainingResults <-  evaluateAllStateObligations sym remainingStates
            pure (stateResults : remainingResults)


evaluateStateObligations ::
    ExprBuilder t st fs ->
    SymState (ExprBuilder t st fs) a ->
    IO
        [ ( Obligation (ExprBuilder t st fs)
          , ObligationResult
          )
        ]
evaluateStateObligations sym state = do
    let orderedObligations = reverse (obligations state)
    mapM
        (\obligation -> do
            obligationResult <- evaluateOneObligation sym state obligation
            pure (obligation, obligationResult)
        )
        orderedObligations

evaluateOneObligation ::
    ExprBuilder t st fs ->
    SymState (ExprBuilder t st fs) a ->
    Obligation (ExprBuilder t st fs) ->
    IO ObligationResult
evaluateOneObligation sym state obligation = do
    obligationPathPred <- predicateOfCondList sym (obligationPath obligation)
    negatedObligation <- notPred sym (obligationPredicate obligation)
    counterexampleQuery <- andPred sym obligationPathPred negatedObligation

    withSolverResult sym counterexampleQuery $ \solverResult ->
        case solverResult of
            Unsat _ -> pure ObligationValid
            Sat (ge, _) -> do
                counterexample <- extractCounterexample ge state
                pure (ObligationInvalid counterexample)
            Unknown -> error "Solver returned unknown while checking an obligation"


extractCounterexample ::
    GroundEvalFn t ->
    SymState (ExprBuilder t st fs) a ->
    IO Counterexample
extractCounterexample ge state = extractVariableValues ge (Map.toList (env state))
    where
        extractVariableValues ::
            GroundEvalFn t ->
            [(VarName, VarBinding (ExprBuilder t st fs))] ->
            IO Counterexample
        extractVariableValues ge variables =
            case variables of
                [] ->
                    pure Map.empty

                (name, binding) : remainingVariables -> do
                    concreteValue <-
                        case varValue binding of
                            Nothing ->
                                pure Nothing

                            Just symbolicValue -> do
                                evaluatedValue <-
                                    groundEvalSomeExpr ge symbolicValue

                                pure (Just evaluatedValue)

                    remainingValues <-
                        extractVariableValues
                            ge
                            remainingVariables

                    pure
                        (Map.insert
                            name
                            concreteValue
                            remainingValues
                        )


groundEvalSomeExpr ::
    GroundEvalFn t ->
    SomeExpr (ExprBuilder t st fs) ->
    IO String
groundEvalSomeExpr ge expression =
    case expression of
        SomeInt e -> do
            value <- groundEval ge e
            pure (show value)

        SomeReal e -> do
            value <- groundEval ge e
            pure (show value)

        SomeBool e -> do
            value <- groundEval ge e
            pure (show value)

        SomeIntArray arrayRecord ->
            pure $
                "<integer array, rank "
                    ++ show (length (arrayDimensions arrayRecord))
                    ++ ">"

        SomeRealArray arrayRecord ->
            pure $
                "<real array, rank "
                    ++ show (length (arrayDimensions arrayRecord))
                    ++ ">"

        SomeBoolArray arrayRecord ->
            pure $
                "<logical array, rank "
                    ++ show (length (arrayDimensions arrayRecord))
                    ++ ">"

