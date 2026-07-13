module Solver
    ( predicateOfCondList
    , z3exe
    , withSolverResult
    , checkStateFeasibility
    , keepFeasibleStates
    , evaluateAllStateObligations
    , evaluateStateObligations
    , evaluateOneObligation
    , extractCounterexample
    ) where

import qualified Data.ByteString.Char8 as B

import Data.Map (Map)  
import qualified Data.Map as Map

import Language.Fortran.Parser
import Language.Fortran.Version
import Language.Fortran.AST
import qualified Language.Fortran.AST.Literal.Real as ASTReal

import What4.Interface
import What4.BaseTypes
import What4.Expr.Builder
import What4.Symbol
import What4.Expr
         ( ExprRangeBindings, GroundEvalFn, groundEval )

import What4.Solver
         (defaultLogData, z3Options, withZ3, SatResult(..))
import What4.Protocol.SMTLib2
         (assume, sessionWriter, runCheckSat)


import Prelude hiding (EQ, LT, GT)

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
            remainingPredicate <-
                predicateOfCondList sym remainingConditions

            andPred sym predicate remainingPredicate


z3exe :: FilePath
z3exe =
    "z3-4.8.12-x86-win/bin/z3.exe"

-- Runs a solver query and handles the result while the Z3 session is open.
--
-- This is important because GroundEvalFn is only valid inside the
-- withZ3 callback.
withSolverResult ::
    ExprBuilder t st fs ->
    BoolExpr t ->
    (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a) -> --takes function for evaluating model
    IO a
withSolverResult sym predicate handleResult =
    withZ3 sym z3exe defaultLogData $ \session -> do
        assume (sessionWriter session) predicate
        runCheckSat session handleResult


-- checks whether one symbolic state has satisfiable path condition list.
checkStateFeasibility ::
    ExprBuilder t st fs ->
    SymState (ExprBuilder t st fs) ->
    IO Bool
checkStateFeasibility sym state = do
    pathPred <- predicateOfCondList sym (pathCond state)

    withSolverResult sym pathPred $ \solverResult ->
        case solverResult of
            Sat _ -> pure True
            Unsat _ -> pure False
            Unknown -> error "Solver failed to determine path feasibility."


-- filters out states whose path conditions are unsatisfiable.
-- currently has logger attached - bad!
keepFeasibleStates ::
    ExprBuilder t st fs ->
    [SymState (ExprBuilder t st fs)] ->
    IO [SymState (ExprBuilder t st fs)]
keepFeasibleStates sym states = do
    feasibleNumberedStates <-
        filterM isFeasible (zip [(1 :: Int) ..] states)
    pure (map snd feasibleNumberedStates)
    where
        isFeasible (stateNumber, state) = do
            feasible <- checkStateFeasibility sym state
            if feasible then do
                putStrLn $
                    show stateNumber ++ ". Satisfiable pathCond"
                pure True
            else do
                putStrLn $
                    show stateNumber ++ ". Unsatisfiable pathCond"
                pure False



evaluateAllStateObligations ::
    ExprBuilder t st fs ->
    [SymState (ExprBuilder t st fs)] ->
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
    SymState (ExprBuilder t st fs) ->
    IO
        [ ( Obligation (ExprBuilder t st fs)
          , ObligationResult
          )
        ]
evaluateStateObligations sym state = do
    let noPreviousObligations = truePred sym
    let orderedObligations = reverse (obligations state)
    evaluateStateObligationsRecurse sym state noPreviousObligations orderedObligations
    where
        evaluateStateObligationsRecurse ::
            ExprBuilder t st fs ->
            SymState (ExprBuilder t st fs) ->
            Pred (ExprBuilder t st fs) ->
            [Obligation (ExprBuilder t st fs)] ->
            IO
                [ ( Obligation (ExprBuilder t st fs)
                , ObligationResult
                )
                ]
        evaluateStateObligationsRecurse sym state previousObligationsPred remainingObligations =
            case remainingObligations of
                [] -> pure []

                obligation : laterObligations -> do
                    obligationResult <- evaluateOneObligation sym state previousObligationsPred obligation

                    updatedPreviousObligationsPred <- andPred sym previousObligationsPred (obligationPredicate obligation)

                    laterResults <- evaluateStateObligationsRecurse sym state updatedPreviousObligationsPred laterObligations

                    pure
                        ( (obligation, obligationResult)
                        : laterResults
                        )

evaluateOneObligation ::
    ExprBuilder t st fs ->
    SymState (ExprBuilder t st fs) ->
    Pred (ExprBuilder t st fs) ->
    Obligation (ExprBuilder t st fs) ->
    IO ObligationResult
evaluateOneObligation sym state previousObligationsPred obligation = do
    obligationPathPred <- predicateOfCondList sym (obligationPath obligation)
    andSection <- andPred sym obligationPathPred previousObligationsPred
    negatedObligation <- notPred sym (obligationPredicate obligation)
    counterexampleQuery <- andPred sym andSection negatedObligation

    withSolverResult sym counterexampleQuery $ \solverResult ->
        case solverResult of
            Unsat _ -> pure ObligationValid
            Sat (ge, _) -> do
                counterexample <- extractCounterexample ge state
                pure (ObligationInvalid counterexample)
            Unknown -> error "Solver failed to determine obligation validity"


extractCounterexample ::
    GroundEvalFn t ->
    SymState (ExprBuilder t st fs) ->
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