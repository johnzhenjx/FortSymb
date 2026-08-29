module Designators where

import qualified Data.Map as Map

import Language.Fortran.AST
import Language.Fortran.Util.Position (SrcSpan)

import What4.Expr.Builder
import What4.Interface

import Arrays
import {-# SOURCE #-} EvalExpr
    ( bindValueOutcomes
    , coerceArrayOnAssignment
    , coerceOnAssignment
    )
import Types
import SymbolicPath


evalArrayDesignator ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> Expression a
    -> [Index a]
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (EvaluatedDesignator (ExprBuilder t st fs))]
evalArrayDesignator sym flags span baseExpr indexExprs state = do
    arrayName <-
        case baseExpr of
            ExpValue _ann _span (ValVariable name) -> pure name
            _ -> error "Unsupported array designator base expression"

    arrayValue <- lookupInitialisedValue arrayName state
    let dimensions = someArrayDimensions arrayValue

    bindValueOutcomes
        (evalArraySubscripts sym flags dimensions indexExprs state)
        (\(subscripts, state1) ->
            pure
                [ ValueAndStateProduced
                    (ArraySubscriptDesignator span arrayName subscripts)
                    state1
                ]
        )
        (\haltedState -> pure [ValueComputationHaltedState haltedState])


readDesignator ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> EvaluatedDesignator (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
readDesignator sym flags designator state =
    case designator of
        VariableDesignator span name -> do
            binding <- lookupBinding name state
            case varValue binding of
                Nothing -> do
                    haltedState <- addObligationAndAssume sym UninitialisedRead span (falsePred sym) state
                    pure [ValueComputationHaltedState haltedState]
                Just value ->
                    pure [ValueAndStateProduced value state]

        ArraySubscriptDesignator span name subscripts -> do
            arrayValue <- lookupInitialisedValue name state
            if hasArraySection subscripts
                then createArraySection sym flags span arrayValue subscripts state
                else
                    lookupSomeArray
                        sym
                        flags
                        span
                        arrayValue
                        (scalarIndices subscripts)
                        state


-- e.g. call set_value(array(i)) needs to verify that i is within bounds
validateDesignator ::
    ExprBuilder t st fs
    -> EvaluatedDesignator (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a ()]
validateDesignator sym designator state =
    case designator of
        VariableDesignator {} ->
            pure [ValueAndStateProduced () state]

        ArraySubscriptDesignator span name subscripts -> do
            arrayValue <- lookupInitialisedValue name state
            let dimensions = someArrayDimensions arrayValue
            inBounds <- arraySubscriptsInBounds sym dimensions subscripts
            state1 <- addObligationAndAssume sym ArrayBounds span inBounds state
            case executionStatus state1 of
                ExecutionHalted _ -> pure [ValueComputationHaltedState state1]
                ExecutionComplete -> pure [ValueAndStateProduced () state1]


writeDesignator ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> EvaluatedDesignator (ExprBuilder t st fs)
    -> SomeExpr (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]
writeDesignator sym flags designator sourceValue state =
    case designator of
        VariableDesignator span name -> do
            binding <- lookupBinding name state
            ensureBindingWritable name binding
            case varType binding of
                VarArray _ _ -> do
                    targetValue <- lookupInitialisedValue name state
                    case sourceValue of
                        SomeIntArray _ -> copyWholeArray span name binding targetValue
                        SomeRealArray _ -> copyWholeArray span name binding targetValue
                        SomeBoolArray _ -> copyWholeArray span name binding targetValue
                        _ -> do
                            coercedValue <- coerceOnAssignment sym (arrayElementType targetValue) sourceValue
                            filledArray <- createConstantArray sym (someArrayDimensions targetValue) coercedValue
                            pure [replaceBindingValue name binding filledArray state]

                targetType -> do
                    coercedValue <- coerceOnAssignment sym targetType sourceValue
                    pure [replaceBindingValue name binding coercedValue state]

        ArraySubscriptDesignator span name subscripts -> do
            binding <- lookupBinding name state
            ensureBindingWritable name binding
            targetArray <- lookupInitialisedValue name state
            coercedSource <-
                case sourceValue of
                    SomeIntArray _ -> pure sourceValue
                    SomeRealArray _ -> pure sourceValue
                    SomeBoolArray _ -> pure sourceValue
                    _ ->
                        coerceOnAssignment
                            sym
                            (arrayElementType targetArray)
                            sourceValue

            bindValueOutcomes
                (if hasArraySection subscripts
                    then updateArraySection sym flags span targetArray subscripts coercedSource state
                    else updateSomeArray sym flags span targetArray (scalarIndices subscripts) coercedSource state
                )
                (\(updatedArray, state1) ->
                    pure [replaceBindingValue name binding updatedArray state1]
                )
                (\haltedState -> pure [haltedState])
    where
        copyWholeArray span name binding targetValue =
            bindValueOutcomes
                (coerceArrayOnAssignment
                    sym flags span targetValue sourceValue state)
                (\(coercedValue, state1) ->
                    pure [replaceBindingValue name binding coercedValue state1]
                )
                (\haltedState -> pure [haltedState])


clearDesignator ::
    ExprBuilder t st fs
    -> EvaluatedDesignator (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]
--scalars get varValue = Nothing;
--array element/section has the corresponding initialisation-mask entries cleared
clearDesignator sym designator state =
    case designator of
        VariableDesignator _span name -> do
            binding <- lookupBinding name state
            ensureBindingWritable name binding
            pure
                [ state
                    { env =
                        Map.insert
                            name
                            (binding { varValue = Nothing })
                            (env state)
                    }
                ]

        ArraySubscriptDesignator span name subscripts -> do
            binding <- lookupBinding name state
            ensureBindingWritable name binding
            targetArray <- lookupInitialisedValue name state
            bindValueOutcomes
                (if hasArraySection subscripts
                    then clearArraySection sym span targetArray subscripts state
                    else clearSomeArrayElement sym span targetArray (scalarIndices subscripts) state
                )
                (\(updatedArray, state1) ->
                    pure [replaceBindingValue name binding updatedArray state1]
                )
                (\haltedState -> pure [haltedState])


ensureBindingWritable :: VarName -> VarBinding sym -> IO ()
ensureBindingWritable name binding =
    case varIntent binding of
        Just In -> error $ "Cannot define INTENT(IN) variable: " ++ name
        _ -> pure ()


lookupBinding ::
    VarName
    -> SymState sym a
    -> IO (VarBinding sym)
lookupBinding name state =
    case Map.lookup name (env state) of
        Nothing -> error $ "Designator variable is not declared: " ++ name
        Just binding -> pure binding


lookupInitialisedValue ::
    VarName
    -> SymState sym a
    -> IO (SomeExpr sym)
lookupInitialisedValue name state = do
    binding <- lookupBinding name state
    case varValue binding of
        Nothing -> error $ "Designator variable is uninitialised: " ++ name
        Just value -> pure value


replaceBindingValue ::
    VarName
    -> VarBinding sym
    -> SomeExpr sym
    -> SymState sym a
    -> SymState sym a
replaceBindingValue name binding value state =
    state
        { env =
            Map.insert
                name
                (binding { varValue = Just value })
                (env state)
        }


scalarIndices ::
    [EvaluatedArraySubscript sym]
    -> [SymExpr sym BaseIntegerType]
scalarIndices subscripts =
    case subscripts of
        [] -> []
        ScalarSubscript index : remaining ->
            index : scalarIndices remaining
        SectionSubscript {} : _ ->
            error "Section passed to scalar array operation"
