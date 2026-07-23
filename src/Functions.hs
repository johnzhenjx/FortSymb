module Functions where

import Language.Fortran.AST
import What4.Interface

import Types

import Data.Maybe (mapMaybe)
import Data.Map (Map)  
import qualified Data.Map as Map

import {-# SOURCE #-} EvalExpr (evalExpr, bindBranches)

extractFunctionDef :: ProgramUnit a -> Maybe (String, ProcedureDef a) 
extractFunctionDef programUnit =
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
buildProcedureEnv = Map.fromList . mapMaybe extractFunctionDef


-- evalFunctionArguments :: IsSymExprBuilder sym 
--     => sym 
--     -> ObligationFlags 
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


evalMatchedArguments :: IsSymExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> [(VarName, Expression a)] 
    -> SymState sym a 
    -> IO [([(VarName, SomeExpr sym)], SymState sym a)]
evalMatchedArguments sym flags matchedArguments initialState =
    go matchedArguments initialState
  where
    go args state = case args of
        [] -> pure [([], state)]

        (parameterName, expression) : remainingArguments ->
            bindBranches
                (evalExpr sym flags expression state)
                (\value state1 ->
                    bindBranches
                        (go remainingArguments state1)
                        (\remainingValues state2 ->
                            pure [ ( (parameterName, value) : remainingValues, state2 ) ]
                        )
                )


argumentToExpr :: Argument a -> Expression a
argumentToExpr argument = case argumentExpr argument of {ArgExpr expr -> expr; _ -> error "Unsupported function arg"}


matchFunctionArguments :: [VarName] -> [Argument a] -> [(VarName, Expression a)]
matchFunctionArguments parameterNames arguments = do
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




            