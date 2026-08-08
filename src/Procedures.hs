module Procedures where

import Language.Fortran.AST
import Language.Fortran.Util.Position (SrcSpan)
import What4.Interface
import What4.Expr.Builder

import Types

import Data.Maybe (mapMaybe)
import Data.Map (Map)  
import qualified Data.Map as Map

import {-# SOURCE #-} EvalExpr (evalExpr, bindBranches, bindValueOutcomes, coerceArrayOnAssignment, coerceOnAssignment)

extractProcedureDef :: ProgramUnit a -> Maybe (String, ProcedureDef a) 
extractProcedureDef programUnit =
    case programUnit of
        --no subprograms or recursion for now
        PUFunction
            _ann
            _span
            maybeReturnType 
            -- function does not need an explicit return type 
            -- this is only for the case where the return variable is not declared and rather uses the function name itself
            _prefixSuffix
            name
            maybeArgumentExprs
            maybeResultExpr
            body
            _subprograms -> do
                parameterNames <- traverse extractVariableName (maybe [] alistList maybeArgumentExprs)
                resultName <- maybe (Just name) extractVariableName maybeResultExpr --if no explicit return name, the function name is implicitly used
                pure
                    ( name
                    , FunctionDef
                        { functionParameters = parameterNames
                        , functionResult = resultName
                        , functionBody = body
                        , functionMaybeReturnTypeSpec = maybeReturnType
                        }
                    )

        PUSubroutine
            _ann
            _span
            _prefixSuffix
            name
            maybeArgumentExprs
            body
            _subprograms -> do
                parameterNames <- traverse extractVariableName (maybe [] alistList maybeArgumentExprs)
                pure
                    ( name
                    , SubroutineDef
                        { subroutineParameters = parameterNames
                        , subroutineBody = body
                        }
                    )

        _ -> Nothing

    where
        extractVariableName :: Expression a -> Maybe VarName
        extractVariableName expression = case expression of {ExpValue _ann _span (ValVariable name) -> Just name; _ -> Nothing}

buildProcedureEnv :: [ProgramUnit a] -> ProcedureEnv a
buildProcedureEnv = Map.fromList . mapMaybe extractProcedureDef


-- evalFunctionArguments :: IsSymExprBuilder sym 
--     => sym 
--     -> ExecutorFlags 
--     -> [Expression a] 
--     -> SymState sym
--     -> IO ([SomeExpr sym], SymState sym)
-- evalFunctionArguments sym flags argumentExprs initialState =
--     go argumentExprs initialState
--     where
--         go [] state = pure ([], state)
--         go (argumentExpr : remainingArguments) state = do
--             (argumentValue, state1) <- evalExpr sym flags argumentExpr state
--             (remainingValues, state2) <- go remainingArguments state1
--             pure (argumentValue : remainingValues, state2)


evalMatchedFunctionArguments :: 
    ExprBuilder t st fs
    -> ExecutorFlags 
    -> [(VarName, Expression a)] 
    -> SymState (ExprBuilder t st fs) a 
    -> IO [(Maybe [(VarName, SrcSpan, SomeExpr (ExprBuilder t st fs))], SymState (ExprBuilder t st fs) a)]
evalMatchedFunctionArguments sym flags matchedArguments initialState =
    go matchedArguments initialState
    where
        go args state = case args of
            [] -> pure [(Just [], state)]

            (parameterName, expression) : remainingArguments ->
                bindValueOutcomes
                    (evalExpr sym flags expression state)
                    (\(value, state1) ->
                        bindBranches
                            (go remainingArguments state1)
                            (\(maybeRemainingValues, state2) ->
                                case maybeRemainingValues of
                                    Nothing -> pure [(Nothing, state2)]
                                    Just remainingValues -> pure [(Just ((parameterName, expressionSpan expression, value) : remainingValues), state2)]
                            )
                    )
                    (\haltedState -> pure [(Nothing, haltedState)])

-- subroutines may pass uninitialised variables inside and assign to them inside the call
-- thus we need to wrap evaluated expressions inside Maybe
evalMatchedSubroutineArguments ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> [(VarName, Expression a)]
    -> SymState (ExprBuilder t st fs) a
    -> IO [(Maybe [(VarName, SrcSpan, Maybe (SomeExpr (ExprBuilder t st fs)))], SymState (ExprBuilder t st fs) a)]
evalMatchedSubroutineArguments sym flags matchedArguments initialState =
    go matchedArguments initialState
    where
        go args state = case args of
            [] -> pure [(Just [], state)]

            (parameterName, expression) : remainingArguments ->
                case expression of
                    ExpValue _ann span (ValVariable argumentName) -> do
                        argumentValue <-
                            case Map.lookup argumentName (env state) of
                                Nothing -> error $ "Subroutine argument is not declared: " ++ argumentName
                                Just binding -> pure (varValue binding)

                        bindBranches
                            (go remainingArguments state)
                            (\(maybeRemainingValues, state1) ->
                                case maybeRemainingValues of
                                    Nothing -> pure [(Nothing, state1)]
                                    Just remainingValues ->
                                        pure [(Just ((parameterName, span, argumentValue) : remainingValues), state1)]
                            )

                    _ ->
                        bindValueOutcomes
                            (evalExpr sym flags expression state)
                            (\(value, state1) ->
                                bindBranches
                                    (go remainingArguments state1)
                                    (\(maybeRemainingValues, state2) ->
                                        case maybeRemainingValues of
                                            Nothing -> pure [(Nothing, state2)]
                                            Just remainingValues -> pure [(Just ((parameterName, expressionSpan expression, Just value) : remainingValues), state2)]
                                    )
                            )
                            (\haltedState -> pure [(Nothing, haltedState)])


argumentToExpr :: Argument a -> Expression a
argumentToExpr argument = case argumentExpr argument of {ArgExpr expr -> expr; _ -> error "Unsupported function arg"}

expressionSpan :: Expression a -> SrcSpan
expressionSpan expression =
    case expression of
        ExpValue _ span _ -> span
        ExpBinary _ span _ _ _ -> span
        ExpUnary _ span _ _ -> span
        ExpSubscript _ span _ _ -> span
        ExpFunctionCall _ span _ _ -> span
        _ -> error "Unsupported procedure argument expression"


-- matchProcedureArguments matches each formal parameter with the original argument expression from the caller:
-- e.g. foo(x, y+1) where foo is declared as foo(a, b) has matchProcedureArguments
--     [ ("a", x)
--     , ("b", y + 1)
--     ]
-- taking into account positional and named arguments

matchProcedureArguments :: [VarName] -> [Argument a] -> [(VarName, Expression a)]
matchProcedureArguments parameterNames arguments = do
    let matched = go 0 False Map.empty arguments 
        --keep track of next index to fill in by positional, then increment if a positional is seen
        --disallow positionals after named

    let missingParameters = filter (\name -> Map.notMember name matched) parameterNames

    case missingParameters of
        [] ->
            --for each parameter name, get the corresponding expression from the matched map
            map
            (\parameterName ->
                let expression = matched Map.! parameterName
                in (parameterName, expression)
            )
            parameterNames

        _ -> error $ "Missing function arguments: " ++ show missingParameters
    where
        go :: Int -> Bool -> Map VarName (Expression a) -> [Argument a] -> Map VarName (Expression a)
        go nextPos seenNamed matched args = case args of
            [] -> matched
            (argument : remainingArguments) -> do
                let expression = argumentToExpr argument

                case argumentName argument of
                    Nothing ->
                        if seenNamed then error "A positional argument cannot follow a named argument"
                        else
                            --index at nextPos
                            case drop nextPos parameterNames of
                                [] -> error "Too many positional arguments"
                                parameterName : _ -> do
                                    let matched1 = insertArgument parameterName expression matched
                                    go (nextPos + 1) False matched1 remainingArguments

                    Just parameterName ->
                        if notElem parameterName parameterNames then error $ "Unknown named argument: " ++ parameterName
                        else do
                            let matched1 = insertArgument parameterName expression matched 
                            go nextPos True matched1 remainingArguments

        insertArgument :: VarName -> Expression a -> Map VarName (Expression a) -> Map VarName (Expression a)
        insertArgument parameterName expression matchedArguments =
            if Map.member parameterName matchedArguments
                then error $ "Duplicate argument for parameter: " ++ parameterName
                else Map.insert parameterName expression matchedArguments



--after declaration blocks, bind input values to their corrosponding variable bindings in local scope
bindFunctionParameters :: ExprBuilder t st fs
    -> ExecutorFlags 
    -> [(VarName, SrcSpan, SomeExpr (ExprBuilder t st fs))]
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]
bindFunctionParameters sym flags argumentValues initialState =
    go initialState argumentValues
    where
        go state argPairs = case argPairs of
            [] -> pure [state]
            (parameterName, span, argumentValue) : rest -> do
                case Map.lookup parameterName (env state) of
                    Nothing -> error $ "Function parameter is not declared: " ++ parameterName
                    Just binding ->
                        bindValueOutcomes
                            (coerceParameterValue sym flags span binding argumentValue state)
                            (\(boundValue, state1) ->
                                let updatedBinding = binding { varValue = Just boundValue }
                                    state2 = state1 { env = Map.insert parameterName updatedBinding (env state1) }
                                in go state2 rest
                            )
                            (\haltedState -> pure [haltedState])


--now this also takes Maybe (SomeExpr sym)
bindSubroutineParameters :: ExprBuilder t st fs
    -> ExecutorFlags 
    -> [(VarName, SrcSpan, Maybe (SomeExpr (ExprBuilder t st fs)))]
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]
bindSubroutineParameters sym flags argumentValues initialState =
    go initialState argumentValues
    where
        go state argPairs = case argPairs of
            [] -> pure [state]
            (parameterName, span, maybeArgumentValue) : rest -> do
                case Map.lookup parameterName (env state) of
                    Nothing -> error $ "Function parameter is not declared: " ++ parameterName
                    Just binding -> do
                        case maybeArgumentValue of
                            Nothing -> do
                                let updatedBinding = binding { varValue = Nothing }
                                    state1 = state { env = Map.insert parameterName updatedBinding (env state) }
                                go state1 rest

                            Just argumentValue ->
                                bindValueOutcomes
                                    (coerceParameterValue sym flags span binding argumentValue state)
                                    (\(boundValue, state1) ->
                                        let updatedBinding = binding { varValue = Just boundValue }
                                            state2 = state1 { env = Map.insert parameterName updatedBinding (env state1) }
                                        in go state2 rest
                                    )
                                    (\haltedState -> pure [haltedState])
                        

coerceParameterValue :: ExprBuilder t st fs -> ExecutorFlags -> SrcSpan -> VarBinding (ExprBuilder t st fs) -> SomeExpr (ExprBuilder t st fs) -> SymState (ExprBuilder t st fs) a -> IO [ValueOutcome (ExprBuilder t st fs) a]
coerceParameterValue sym flags span binding argumentValue state =
    case (varType binding, argumentValue) of
        -- Array parameter with array argument
        (VarArray _ _, SomeIntArray{}) ->
            case varValue binding of
                Nothing -> error "Array parameter has no declared array value"
                Just targetArray -> coerceArrayOnAssignment sym flags span targetArray argumentValue state

        (VarArray _ _, SomeRealArray{}) ->
            case varValue binding of
                Nothing -> error "Array parameter has no declared array value"
                Just targetArray -> coerceArrayOnAssignment sym flags span targetArray argumentValue state

        (VarArray _ _, SomeBoolArray{}) ->
            case varValue binding of
                Nothing -> error "Array parameter has no declared array value"
                Just targetArray -> coerceArrayOnAssignment sym flags span targetArray argumentValue state

        -- Array parameter with scalar argument
        (VarArray _ _, _) -> error "Scalar argument passed to array parameter"

        -- Scalar parameter with array argument
        (_, SomeIntArray{}) -> error "Array argument passed to scalar parameter"
        (_, SomeRealArray{}) -> error "Array argument passed to scalar parameter"
        (_, SomeBoolArray{}) -> error "Array argument passed to scalar parameter"

        -- Scalar parameter with scalar argument
        _ -> do
            coercedValue <- coerceOnAssignment sym (varType binding) argumentValue
            pure [ValueAndStateProduced coercedValue state]


