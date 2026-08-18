module Procedures where

import Language.Fortran.AST
import Language.Fortran.Util.Position (SrcSpan)
import What4.Interface
import What4.Expr.Builder

import Types
import Arrays
import Designators
import Attributes (attributeIntent)
import SymbolicPath (addObligationAndAssume)

import Data.Maybe (mapMaybe)
import Data.Map (Map)  
import qualified Data.Map as Map

import {-# SOURCE #-} EvalExpr
    ( bindBranches
    , bindValueOutcomes
    , coerceArrayOnAssignment
    , coerceOnAssignment
    , evalExpr
    )

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


data EvaluatedProcedureArgument sym
    = ProcedureDesignatorArgument
        VarName
        SrcSpan
        (Maybe Intent)
        (EvaluatedDesignator sym)
        (Maybe (SomeExpr sym))
    | ProcedureExpressionArgument
        VarName
        SrcSpan
        (Maybe Intent)
        (SomeExpr sym)


procedureParameterIntents :: ProcedureDef a -> Map VarName Intent
procedureParameterIntents procedureDef =
    Map.fromList
        [ nameAndIntent
        | block <- body
        , nameAndIntent <- blockIntents block
        ]
    where
        body =
            case procedureDef of
                FunctionDef { functionBody = functionBlocks } -> functionBlocks
                SubroutineDef { subroutineBody = subroutineBlocks } -> subroutineBlocks

        blockIntents block =
            case block of
                BlStatement _ann _span _label statement ->
                    case statement of
                        StDeclaration _ _ _ maybeAttributesInfo declarationsInfo ->
                            case attributeIntent (maybe [] alistList maybeAttributesInfo) of
                                Nothing -> []
                                Just intent ->
                                    [ (name, intent)
                                    | declaration <- alistList declarationsInfo
                                    , ExpValue _ _ (ValVariable name) <- [declaratorVariable declaration]
                                    ]

                        StIntent _ _ intent variablesInfo ->
                            [ (name, intent)
                            | ExpValue _ _ (ValVariable name) <- alistList variablesInfo
                            ]

                        _ -> []

                _ -> []


--procedures may receive an uninitialised designator and assign it in the call
evalMatchedProcedureArguments ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> Map VarName Intent
    -> [(VarName, Expression a)]
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a [EvaluatedProcedureArgument (ExprBuilder t st fs)]]
evalMatchedProcedureArguments sym flags parameterIntents matchedArguments initialState =
    go matchedArguments initialState
    where
        go args state = case args of
            [] -> pure [ValueAndStateProduced [] state]

            (parameterName, expression) : remainingArguments ->
                let intent = Map.lookup parameterName parameterIntents
                in
                case expression of
                    ExpValue _ann span (ValVariable argumentName) -> do
                        let designator = VariableDesignator span argumentName
                        case intent of
                            Just Out -> continueWithDesignator parameterName span intent designator Nothing remainingArguments state
                            Just In -> readAndContinue parameterName span intent designator remainingArguments state
                            Just InOut -> readAndContinue parameterName span intent designator remainingArguments state
                            Nothing -> do
                                argumentValue <-
                                    case Map.lookup argumentName (env state) of
                                        Nothing -> error $ "Procedure argument is not declared: " ++ argumentName
                                        Just binding -> pure (varValue binding)
                                continueWithDesignator parameterName span intent designator argumentValue remainingArguments state

                    ExpSubscript _ann span baseExpr indicesInfo ->
                        bindValueOutcomes
                            (evalArrayDesignator
                                sym
                                flags
                                span
                                baseExpr
                                (alistList indicesInfo)
                                state
                            )
                            (\(designator, state1) ->
                                case intent of
                                    Just Out ->
                                        bindValueOutcomes
                                            (validateDesignator sym designator state1)
                                            (\((), state2) ->
                                                continueWithDesignator parameterName span intent designator Nothing remainingArguments state2)
                                            (\haltedState -> pure [ValueComputationHaltedState haltedState])
                                    _ ->
                                        readAndContinue parameterName span intent designator remainingArguments state1
                            )
                            (\haltedState -> pure [ValueComputationHaltedState haltedState])

                    _ ->
                        case intent of
                            Just Out -> error $ "INTENT(OUT) parameter " ++ parameterName ++ " requires a writable designator"
                            Just InOut -> error $ "INTENT(INOUT) parameter " ++ parameterName ++ " requires a writable designator"
                            _ ->
                                bindValueOutcomes
                                    (evalExpr sym flags expression state)
                                    (\(value, state1) ->
                                        bindValueOutcomes
                                            (go remainingArguments state1)
                                            (\(remainingValues, state2) ->
                                                pure
                                                    [ ValueAndStateProduced
                                                        ( ProcedureExpressionArgument
                                                            parameterName
                                                            (expressionSpan expression)
                                                            intent
                                                            value
                                                            : remainingValues
                                                        )
                                                        state2
                                                    ]
                                            )
                                            (\haltedState -> pure [ValueComputationHaltedState haltedState])
                                    )
                                    (\haltedState -> pure [ValueComputationHaltedState haltedState])

        readAndContinue parameterName span intent designator remainingArguments state =
            bindValueOutcomes
                (readDesignator sym flags designator state)
                (\(value, state1) ->
                    continueWithDesignator parameterName span intent designator (Just value) remainingArguments state1)
                (\haltedState -> pure [ValueComputationHaltedState haltedState])

        continueWithDesignator parameterName span intent designator argumentValue remainingArguments state =
            bindValueOutcomes
                (go remainingArguments state)
                (\(remainingValues, state1) ->
                    pure
                        [ ValueAndStateProduced
                            ( ProcedureDesignatorArgument
                                parameterName
                                span
                                intent
                                designator
                                argumentValue
                                : remainingValues
                            )
                            state1
                        ]
                )
                (\haltedState -> pure [ValueComputationHaltedState haltedState])


argumentToExpr :: Argument a -> Expression a
argumentToExpr argument = case argumentExpr argument of {ArgExpr expr -> expr; _ -> error "Unsupported procedure argument"}

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

        _ -> error $ "Missing procedure arguments: " ++ show missingParameters
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



bindProcedureParameters :: ExprBuilder t st fs
    -> ExecutorFlags 
    -> [EvaluatedProcedureArgument (ExprBuilder t st fs)]
    -> SymState (ExprBuilder t st fs) a
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]
bindProcedureParameters sym flags argumentValues callerState initialState =
    go initialState argumentValues
    where
        go state argPairs = case argPairs of
            [] -> pure [state]
            argument : rest -> do
                let (parameterName, span, intent, maybeArgumentValue) =
                        case argument of
                            ProcedureDesignatorArgument name argumentSpan argumentIntent _ value ->
                                (name, argumentSpan, argumentIntent, value)
                            ProcedureExpressionArgument name argumentSpan argumentIntent value ->
                                (name, argumentSpan, argumentIntent, Just value)
                case Map.lookup parameterName (env state) of
                    Nothing -> error $ "Procedure parameter is not declared: " ++ parameterName
                    Just binding ->
                        case intent of
                            Just Out ->
                                case argument of
                                    ProcedureExpressionArgument {} ->
                                        error $ "INTENT(OUT) parameter " ++ parameterName ++ " requires a writable designator"
                                    ProcedureDesignatorArgument _ _ _ designator _ -> do
                                        state1 <- validateOutputAssociation sym span parameterName binding designator callerState state
                                        case executionStatus state1 of
                                            ExecutionHalted _ -> pure [state1]
                                            ExecutionComplete ->
                                                let outputValue =
                                                        case varType binding of
                                                            VarArray _ _ -> varValue binding
                                                            _ -> Nothing
                                                    updatedBinding = binding { varValue = outputValue }
                                                    state2 = state1 { env = Map.insert parameterName updatedBinding (env state1) }
                                                in go state2 rest

                            Just In -> bindInputParameter parameterName span binding maybeArgumentValue rest state
                            Just InOut -> bindInputParameter parameterName span binding maybeArgumentValue rest state

                            Nothing ->
                                case maybeArgumentValue of
                                    Nothing ->
                                        let updatedBinding = binding { varValue = Nothing }
                                            state1 = state { env = Map.insert parameterName updatedBinding (env state) }
                                        in go state1 rest
                                    Just _ ->
                                        bindInputParameter parameterName span binding maybeArgumentValue rest state

        bindInputParameter parameterName span binding maybeArgumentValue rest state =
            case maybeArgumentValue of
                Nothing ->
                    error $ "Input parameter " ++ parameterName ++ " received an uninitialised argument"
                Just argumentValue ->
                    bindValueOutcomes
                        (coerceParameterValue sym flags span binding argumentValue state)
                        (\(boundValue, state1) ->
                            let updatedBinding = binding { varValue = Just boundValue }
                                state2 = state1 { env = Map.insert parameterName updatedBinding (env state1) }
                            in go state2 rest
                        )
                        (\haltedState -> pure [haltedState])


copyProcedureArgumentsBack ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> [EvaluatedProcedureArgument (ExprBuilder t st fs)]
    -> SymState (ExprBuilder t st fs) a
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]
copyProcedureArgumentsBack sym flags arguments localState initialCallerState =
    go initialCallerState arguments
    where
        go state remainingArguments =
            case executionStatus state of
                ExecutionHalted _ -> pure [state]
                ExecutionComplete ->
                    case remainingArguments of
                        [] -> pure [state]
                        argument : rest -> do
                            let parameterName =
                                    case argument of
                                        ProcedureDesignatorArgument name _ _ _ _ -> name
                                        ProcedureExpressionArgument name _ _ _ -> name

                            parameterBinding <-
                                case Map.lookup parameterName (env localState) of
                                    Nothing -> error $ "Procedure parameter is not declared: " ++ parameterName
                                    Just binding -> pure binding

                            let argumentIntent =
                                    case argument of
                                        ProcedureDesignatorArgument _ _ intent _ _ -> intent
                                        ProcedureExpressionArgument _ _ intent _ -> intent

                            case argumentIntent of
                                Just In ->
                                    go state rest

                                _ ->
                                    case argument of
                                        ProcedureExpressionArgument _ _ _ _ ->
                                            error $
                                                "Procedure argument for parameter "
                                                    ++ parameterName
                                                    ++ " is not a writable designator"

                                        ProcedureDesignatorArgument _ _ _ designator _ ->
                                            case varValue parameterBinding of
                                                Nothing ->
                                                    bindBranches
                                                        (clearDesignator sym designator state)
                                                        (\state1 -> go state1 rest)

                                                Just parameterValue ->
                                                    bindBranches
                                                        (writeDesignator
                                                            sym
                                                            flags
                                                            designator
                                                            parameterValue
                                                            state
                                                        )
                                                        (\state1 -> go state1 rest)


validateOutputAssociation ::
    ExprBuilder t st fs
    -> SrcSpan
    -> VarName
    -> VarBinding (ExprBuilder t st fs)
    -> EvaluatedDesignator (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> SymState (ExprBuilder t st fs) a
    -> IO (SymState (ExprBuilder t st fs) a)
--checks that an actual argument is compatible with an intent output dummy
validateOutputAssociation sym span parameterName parameterBinding designator callerState localState = do
    (actualType, maybeActualDimensions) <- designatorTypeAndDimensions designator callerState
    let parameterType = varType parameterBinding
    case (parameterType, actualType) of
        (VarArray parameterElementType _, VarArray actualElementType _)
            | parameterElementType /= actualElementType ->
                error $ "Array type mismatch for INTENT(OUT) parameter: " ++ parameterName
            | otherwise -> do
                parameterDimensions <-
                    case varValue parameterBinding of
                        Just (SomeIntArray record) -> pure (arrayDimensions record)
                        Just (SomeRealArray record) -> pure (arrayDimensions record)
                        Just (SomeBoolArray record) -> pure (arrayDimensions record)
                        _ -> error $ "Array parameter has no declared shape: " ++ parameterName
                actualDimensions <-
                    case maybeActualDimensions of
                        Just dimensions -> pure dimensions
                        Nothing -> error $ "Array actual has no shape: " ++ parameterName
                shapeMatches <- arrayShapesEqual sym parameterDimensions actualDimensions
                addObligationAndAssume sym ArrayShape span shapeMatches localState

        (VarArray _ _, _) -> error $ "Scalar argument passed to INTENT(OUT) array parameter: " ++ parameterName

        (_, VarArray _ _) -> error $ "Array argument passed to INTENT(OUT) scalar parameter: " ++ parameterName

        _
            | scalarTypesAssignmentCompatible actualType parameterType -> pure localState
            | otherwise -> error $ "Type mismatch for INTENT(OUT) parameter: " ++ parameterName
    where
        designatorTypeAndDimensions currentDesignator currentCallerState =
            case currentDesignator of
                VariableDesignator _ name -> do
                    binding <- lookupCallerBinding name currentCallerState
                    dimensions <- bindingDimensions binding
                    pure (varType binding, dimensions)

                ArraySubscriptDesignator _ name subscripts -> do
                    binding <- lookupCallerBinding name currentCallerState
                    elementType <-
                        case varType binding of
                            VarArray currentElementType _ -> pure currentElementType
                            _ -> error $ "Subscripted argument is not an array: " ++ name
                    if hasArraySection subscripts
                        then do
                            dimensions <- sectionDimensions sym subscripts
                            pure (VarArray elementType (length dimensions), Just dimensions)
                        else pure (elementType, Nothing)

        lookupCallerBinding name currentCallerState =
            case Map.lookup name (env currentCallerState) of
                Nothing -> error $ "Procedure argument is not declared: " ++ name
                Just binding -> pure binding

        bindingDimensions binding =
            case varValue binding of
                Just (SomeIntArray record) -> pure (Just (arrayDimensions record))
                Just (SomeRealArray record) -> pure (Just (arrayDimensions record))
                Just (SomeBoolArray record) -> pure (Just (arrayDimensions record))
                _ -> pure Nothing

        scalarTypesAssignmentCompatible targetType sourceType =
            case (targetType, sourceType) of
                (VarInt, VarInt) -> True
                (VarInt, VarReal) -> True
                (VarReal, VarInt) -> True
                (VarReal, VarReal) -> True
                (VarBool, VarBool) -> True
                _ -> False
                        

coerceParameterValue :: ExprBuilder t st fs -> ExecutorFlags -> SrcSpan -> VarBinding (ExprBuilder t st fs) -> SomeExpr (ExprBuilder t st fs) -> SymState (ExprBuilder t st fs) a -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
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
