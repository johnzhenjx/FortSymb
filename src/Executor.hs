module Executor where

import qualified Data.Map as Map

import Language.Fortran.AST
import Language.Fortran.Util.Position

import What4.Interface
import What4.Expr.Builder

import Types
import {-# SOURCE #-} EvalExpr (getVarType, evalExpr, coerceOnAssignment, coerceArrayOnAssignment, bindBranches, bindValueOutcomes)
import Arrays
import Attributes
import Procedures
import SymbolicPath

import qualified Data.List.NonEmpty as NonEmpty

import Control.Monad (forM_, filterM, foldM)

-- preserveHaltedState :: SymState sym a -> SymState sym a
-- preserveHaltedState state =
--     case executionStatus state of
--         ExecutionHalted _ -> state
--         ExecutionComplete ->
--             error "ValueComputationHaltedState contained an ExecutionComplete state"


execProgramFile ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    ProgramFile a ->
    IO [SymState (ExprBuilder t st fs) a]
execProgramFile sym flags pf = 
    case programFileProgramUnits pf of
        [pu] -> execProgramUnit sym flags pu
        _  -> error "Only single program unit is supported for now"
        -- fmap concat ( mapM (execProgramUnit sym) (programFileProgramUnits pf) )


execProgramUnit ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    ProgramUnit a ->
    IO [SymState (ExprBuilder t st fs) a]

execProgramUnit sym flags pu =
    case pu of 
        PUMain _ann _span _name blocks maybeInternalProcedures -> do
            let procedureEnv = buildProcedureEnv (maybe [] id maybeInternalProcedures)
            execBlocks sym flags blocks (emptyState procedureEnv)
        _ -> error "Bad"


execBlocks ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    [Block a] ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]

execBlocks sym flags blocks state =
    case executionStatus state of
        ExecutionHalted _ ->
            pure [state]

        ExecutionComplete ->
            case blocks of
                [] -> pure [state]

                block : remainingBlocks ->
                    bindBranches
                        (execBlock sym flags block state)
                        (\state1 -> execBlocks sym flags remainingBlocks state1)



execBlock ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    Block a ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]

execBlock sym flags block state = 
    case block of 
        BlStatement _ann _span _label statement -> execStatement sym flags statement state

        --nEcondAndBlocks is a NonEmpty of tuples of cond (Expression) and Block list representing if and else if clauses
        BlIf 
            _ann 
            _span 
            _label 
            _name 
            nEcondAndBlocks
            maybeElseBlocks 
            _endIfLabel -> 
                execIfClauses sym flags (NonEmpty.toList nEcondAndBlocks) maybeElseBlocks state


        -- outer: do i = 1, 10
        --     ...
        -- end do outer

        -- here, maybeName = Just "outer"
        -- allows you to specify which layer of the loop to cycle/exit
        
        -- DoSpecification	 
        --  doSpecAnno :: a	 
        --  doSpecSpan :: SrcSpan	 
        --  doSpecInitial :: Statement a	- Guaranteed to be StExpressionAssign
        --  doSpecLimit :: Expression a	 
        --  doSpecIncrement :: Maybe (Expression a)	 

        BlDo 
            _ann 
            span 
            _label 
            maybeName 
            _terminationLabel 
            maybeSpec 
            body 
            _maybeEndDo ->
                execDoBlock sym flags span maybeName maybeSpec body state



        BlComment _ann _span _comment -> pure [state]

        _ -> error "Unsupproted Bl"
        -- ...


extractDoSpecification :: DoSpecification a -> (VarName, Expression a, Expression a, Maybe (Expression a))
extractDoSpecification doSpec =
    case doSpecInitial doSpec of
        StExpressionAssign _ _ lhs initialExpr ->
            case lhs of
                ExpValue _ _ (ValVariable loopVariable) ->
                    ( loopVariable
                    , initialExpr
                    , doSpecLimit doSpec
                    , doSpecIncrement doSpec
                    )
                _ -> error "DO loop variable must be a variable"
        _ -> error "Expected assignment in DO specification"

execDoBlock ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    SrcSpan ->
    Maybe String ->
    Maybe (DoSpecification a) ->
    [Block a] ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]

execDoBlock sym flags span maybeName maybeSpec body state =
    case maybeSpec of
        Nothing -> error "Do block without specification (infinite loop) is not supported"
        Just doSpec -> do
            let (loopVarName, initialExpr, limitExpr, maybeIncrementExpr ) = extractDoSpecification doSpec

            bindValueOutcomes
                (evalExpr sym flags initialExpr state)
                (\(initialValue, state1) ->
                    bindValueOutcomes
                        (evalExpr sym flags limitExpr state1)
                        (\(limitValue, state2) -> do
                            let incrementBranches = case maybeIncrementExpr of
                                    Nothing -> do
                                        one <- intLit sym 1
                                        pure [ValueAndStateProduced (SomeInt one) state2]
                                    Just incrementExpr -> evalExpr sym flags incrementExpr state2

                            bindValueOutcomes
                                incrementBranches
                                (\(incrementValue, state3) ->
                                    case (initialValue, limitValue, incrementValue) of
                                            ( SomeInt initialInt, SomeInt limitInt, SomeInt incrementInt ) -> do
                                                state4 <- addIncrementStepNonZeroObligation sym incrementInt state3
                                                -- the increment expression’s value is fixed when the DO loop begins
                                                case executionStatus state4 of
                                                    ExecutionHalted _ -> pure [state4]
                                                    ExecutionComplete ->
                                                        runDoLoop
                                                            sym
                                                            flags
                                                            span
                                                            0
                                                            maybeName
                                                            loopVarName
                                                            initialInt
                                                            limitInt
                                                            incrementInt
                                                            body
                                                            state4

                                            _ -> error "DO loop initial value, limit, and increment must be integers"
                                )
                                (\haltedState -> pure [haltedState])
                        )
                        (\haltedState -> pure [haltedState])
                )
                (\haltedState -> pure [haltedState])

    where 
        addIncrementStepNonZeroObligation sym increment state = do
            zero <- intLit sym 0
            incrementIsNonZero <- notPred sym =<< intEq sym increment zero
            if isObligationEnabled flags IncrementStepNonZero
                then addObligationAndAssume sym IncrementStepNonZero incrementIsNonZero state
                else pure state


        runDoLoop
            sym
            flags
            span
            unrollCount
            maybeName
            loopVarName
            currentValue
            limitValue
            incrementValue
            body
            state = do
                stateWithIterator <- assignIntegerValue loopVarName currentValue state

                continuePredicate <- makeDoContinuePredicate sym currentValue limitValue incrementValue
                exitPredicate <- notPred sym continuePredicate

                maybeContinueState <- addPathConditionAndKeepIfFeasible sym continuePredicate stateWithIterator 
                maybeExitState <- addPathConditionAndKeepIfFeasible sym exitPredicate stateWithIterator

                continuingStates <- 
                    case maybeContinueState of 
                        Nothing -> pure []
                        Just continueState 
                            | unrollCount >= maxDoLoopUnroll flags -> 
                                pure
                                    [ continueState
                                        { executionStatus =
                                            ExecutionHalted
                                                LoopUnrollLimitReached
                                                    { incompleteLoopSpan = span
                                                    , incompleteUnrollCount = unrollCount
                                                    }
                                        }
                                    ]

                            | otherwise -> do
                                nextValue <- intAdd sym currentValue incrementValue
                                bindBranches
                                    (execBlocks sym flags body continueState)
                                    (\bodyState ->
                                        case executionStatus bodyState of
                                            ExecutionHalted _ -> pure [bodyState]
                                            ExecutionComplete ->
                                                runDoLoop
                                                    sym
                                                    flags
                                                    span
                                                    (unrollCount + 1)
                                                    maybeName
                                                    loopVarName
                                                    nextValue
                                                    limitValue
                                                    incrementValue
                                                    body
                                                    bodyState
                                    )

                let exitStates =
                        case maybeExitState of
                            Nothing -> []
                            Just exitState -> [exitState]

                pure (exitStates ++ continuingStates)


        assignIntegerValue name value state =
            case Map.lookup name (env state) of
                Nothing -> error $ "Undeclared variable in doloop (wtf): " ++ name

                Just binding ->
                    case varType binding of
                        VarInt ->
                            pure state
                                { env = Map.insert 
                                    name 
                                    (binding { varValue = Just (SomeInt value) }) 
                                    (env state) 
                                }

                        _ -> error $ "Expected integer variable in doloop (wtf): " ++ name
        
        -- (increment > 0 && currentValue <= limitValue)
        -- ||
        -- (increment < 0 && currentValue >= limitValue)
        makeDoContinuePredicate sym current limit increment = do
            zero <- intLit sym 0

            incrementPositive <- intLt sym zero increment
            incrementNegative <- intLt sym increment zero

            withinPositiveLimit <- intLe sym current limit
            withinNegativeLimit <- intLe sym limit current

            continuePositive <- andPred sym incrementPositive withinPositiveLimit
            continueNegative <- andPred sym incrementNegative withinNegativeLimit

            orPred sym continuePositive continueNegative



execStatement ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    Statement a ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]

execStatement sym flags statement state = 
    case statement of
        StDeclaration _ann _span typeSpec maybeAttributesInfo declsInfo -> do
            let attributes = maybe [] alistList maybeAttributesInfo
            declareVars sym flags typeSpec attributes (alistList declsInfo) state
        StExpressionAssign _ann _span lhs rhs ->
            execAssign sym flags lhs rhs state
        StRead2 _ann _span _format maybeReadList -> do
            newState <- execRead2s sym maybeReadList state --don't include StRead for now
            pure [newState]
        StIfLogical _ann _span cond stmt -> execIfLogical sym flags cond stmt state --one-line if, ie if(cond) stmt
        
        StCall _ann _span procedureExpr argumentsInfo ->
            case procedureExpr of
                ExpValue _ann _span (ValVariable "fortsymb_assert") ->
                    execAssertionArguments sym flags (alistList argumentsInfo) state --assume this will be array of states
                _ -> 
                    evalSubroutineCall sym flags procedureExpr (alistList argumentsInfo) state

        --array allocations only for now, hence specifies Nothings
        StAllocate _ann _span Nothing allocationObjectsInfo Nothing -> do
            execAllocate sym flags (alistList allocationObjectsInfo) state


        StImplicit{} -> pure [state]

        _ -> error "Unsupported statement type"


execAllocate :: 
    ExprBuilder t st fs
    -> ExecutorFlags
    -> [Expression a]
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]

execAllocate sym flags allocationObjects initialState = allocateObjects allocationObjects [initialState]
    where
        allocateObjects objects states = case objects of
            [] -> pure states

            allocationObject : remainingObjects -> do
                nestedStates <-
                    mapM
                        (allocateObject allocationObject)
                        states

                allocateObjects remainingObjects (concat nestedStates)


        allocateObject allocationObject state =
            case executionStatus state of
                ExecutionHalted _ -> pure [state]
                ExecutionComplete ->
                    case allocationObject of
                        ExpSubscript _ann _span baseExpr indicesInfo ->
                            case baseExpr of
                                ExpValue _baseAnn _baseSpan (ValVariable name) ->
                                    allocateArray name (alistList indicesInfo) state

                                _ -> error "Unsupported allocation object"

                        _ -> error "Only array allocation is currently supported"


        allocateArray name indexExprs state =
            case Map.lookup name (env state) of
                Nothing -> error $ "Allocation of undeclared array: " ++ name

                Just binding ->
                    case varType binding of
                        VarArray elementType rank ->
                            case varValue binding of
                                Just _ -> error $ "Array is already allocated: " ++ name

                                Nothing ->
                                    bindBranches
                                        (evalAllocationDimensionIxs indexExprs state)
                                        (\outcome ->
                                            case outcome of
                                                (Nothing, haltedState) -> pure [haltedState]
                                                (Just dimensions, state1) ->
                                                    if length dimensions /= rank then error $ "Allocation rank does not match declaration: " ++ name

                                                    else do
                                                        arrayExpr <- createUninitialisedArray sym name elementType dimensions
                                                        let updatedBinding = binding { varValue = Just arrayExpr }
                                                        pure [state1 { env = Map.insert name updatedBinding (env state1) }]
                                        )

                        _ -> error $ "Variable is not an array: " ++ name


        evalAllocationDimensionIxs indexExprs state =
            case indexExprs of
                [] -> pure [(Just [], state)]

                indexExpr : remainingExprs ->
                    bindBranches
                        (evalAllocationDimensionIx indexExpr state)
                        (\outcome ->
                            case outcome of
                                (Nothing, haltedState) -> pure [(Nothing, haltedState)]
                                (Just dimension, state1) ->
                                    bindBranches
                                        (evalAllocationDimensionIxs remainingExprs state1)
                                        (\(maybeRemainingDimensions, finalState) ->
                                            case maybeRemainingDimensions of
                                                Nothing -> pure [(Nothing, finalState)]
                                                Just remainingDimensions -> pure [(Just (dimension : remainingDimensions), finalState)]
                                        )
                        )

        evalAllocationDimensionIx indexExpr state =
            case indexExpr of
                IxSingle _ann _span _name upperExpr -> do
                    lowerBound <- intLit sym 1

                    bindValueOutcomes
                        (evalExpr sym flags upperExpr state)
                        (\(upperValue, state1) ->
                            case upperValue of
                                SomeInt upperBound ->
                                    pure [(Just (ArrayDimension { dimensionLower = lowerBound, dimensionUpper = upperBound }), state1)]
                                _ -> error "Allocation upper bound must be an integer"
                        )
                        (\haltedState -> pure [(Nothing, haltedState)])

                IxRange _ann _span maybeLowerExpr maybeUpperExpr Nothing ->
                    bindValueOutcomes
                        (case maybeLowerExpr of
                            Nothing -> do
                                defaultLower <- intLit sym 1
                                pure [ValueAndStateProduced (SomeInt defaultLower) state]

                            Just lowerExpr ->
                                evalExpr sym flags lowerExpr state
                        )
                        (\(lowerValue, state1) ->
                            case lowerValue of
                                SomeInt lowerBound ->
                                    case maybeUpperExpr of
                                        Nothing -> error "Allocation upper bound is required"

                                        Just upperExpr ->
                                            bindValueOutcomes
                                                (evalExpr sym flags upperExpr state1)
                                                (\(upperValue, state2) ->
                                                    case upperValue of
                                                        SomeInt upperBound ->
                                                            pure [(Just (ArrayDimension { dimensionLower = lowerBound, dimensionUpper = upperBound }), state2)]
                                                        _ -> error "Allocation upper bound must be an integer"
                                                )
                                                (\haltedState -> pure [(Nothing, haltedState)])
                                _ -> error "Allocation lower bound must be an integer"
                        )
                        (\haltedState -> pure [(Nothing, haltedState)])

                IxRange _ann _span _lower _upper (Just _stride) -> error "Allocation strides are not supported"


declareVars ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> TypeSpec a
    -> [Attribute a]
    -> [Declarator a]
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]

declareVars sym flags typeSpec attributes decls state =
    case executionStatus state of
        ExecutionHalted _ -> pure [state]
        ExecutionComplete ->
            case decls of
                [] -> pure [state]
                declaration : remainingDeclarations -> do
                    bindBranches
                        (declareVar sym flags typeSpec attributes declaration state)
                        (\state1 -> declareVars sym flags typeSpec attributes remainingDeclarations state1)


declareVar ::
    ExprBuilder t st fs
    -> ExecutorFlags 
    -> TypeSpec a 
    -> [Attribute a]
    -> Declarator a 
    -> SymState (ExprBuilder t st fs) a 
    -> IO [SymState (ExprBuilder t st fs) a]
declareVar sym flags typeSpec attributes decl state =
    case declaratorVariable decl of
        ExpValue _ann _span (ValVariable name) ->
            case declaratorType decl of  --need to add "dimension" annotator
                ScalarDecl ->
                    case attributeDimensions attributes of
                        Just dimensionListInfo ->
                            declareArrayVar sym flags typeSpec attributes name dimensionListInfo (declaratorInitial decl) state
                        Nothing ->
                            declareScalarVar sym flags typeSpec name (declaratorInitial decl) state
                ArrayDecl dimensionListInfo ->
                    declareArrayVar sym flags typeSpec attributes name dimensionListInfo (declaratorInitial decl) state
        _ -> error "Declaration target is not a variable"


declareScalarVar ::
    ExprBuilder t st fs
    -> ExecutorFlags 
    -> TypeSpec a 
    -> VarName 
    -> Maybe (Expression a) 
    -> SymState (ExprBuilder t st fs) a 
    -> IO [SymState (ExprBuilder t st fs) a]
declareScalarVar sym flags typeSpec name maybeInitial state =
    case maybeInitial of
        Nothing ->
            pure [ state 
                    { env = 
                        Map.insert 
                            name 
                            (VarBinding (getVarType typeSpec) Nothing) 
                            (env state) 
                    }
                ]
        Just initialExpr ->
            bindValueOutcomes
                (evalExpr sym flags initialExpr state)
                (\(valueBeforeCoercion, state1) -> do
                    valueAfterCoercion <- coerceOnAssignment sym (getVarType typeSpec) valueBeforeCoercion

                    pure [ state1
                            { env =
                                Map.insert
                                    name
                                    (VarBinding (getVarType typeSpec) (Just valueAfterCoercion))
                                    (env state1)
                            }
                          ]
                )
                (\haltedState -> pure [haltedState])


--reshape not accepted yet -- scary
declareArrayVar ::
    ExprBuilder t st fs 
    -> ExecutorFlags 
    -> TypeSpec a 
    -> [Attribute a]
    -> VarName
    -> AList DimensionDeclarator a
    -> Maybe (Expression a) 
    -> SymState (ExprBuilder t st fs) a 
    -> IO [SymState (ExprBuilder t st fs) a]

declareArrayVar sym flags typeSpec attributes name dimensionListInfo maybeInitial state
    | isAllocatable attributes = 
        pure [ state { env = Map.insert name (VarBinding arrayType Nothing) (env state) } ]

    | otherwise = do
        bindBranches
            (evalArrayDimensions sym flags (alistList dimensionListInfo) state)
            (\outcome ->
                case outcome of
                    (Nothing, haltedState) -> pure [haltedState]
                    (Just dimensions, state1) ->
                        case maybeInitial of
                            Nothing -> do
                                arrayValue <- createUninitialisedArray sym name (getVarType typeSpec) dimensions
                                pure [state1 { env = Map.insert name (VarBinding arrayType (Just arrayValue)) (env state1) }]

                            Just (ExpInitialisation _ann _span elementsInfo) ->
                                bindValueOutcomes
                                    (createArrayFromConstructor
                                        sym
                                        flags
                                        name
                                        (getVarType typeSpec)
                                        dimensions
                                        (alistList elementsInfo)
                                        state1
                                    )
                                    (\(arrayValue, state2) ->
                                        pure [ state2 { env = Map.insert name (VarBinding arrayType (Just arrayValue)) (env state2) }]
                                    )
                                    (\haltedState -> pure [haltedState])

                            Just initExpr ->
                                bindValueOutcomes
                                    (evalExpr sym flags initExpr state1)
                                    (\(initValue, state2) -> do
                                        coercedValue <- coerceOnAssignment sym (getVarType typeSpec) initValue
                                        arrayValue <- createConstantArray sym dimensions coercedValue
                                        pure [ state2 { env = Map.insert name (VarBinding arrayType (Just arrayValue)) (env state2) }]
                                    )
                                    (\haltedState -> pure [haltedState])
            )
    where
        arrayType = VarArray (getVarType typeSpec) (length (alistList dimensionListInfo))



execAssign ::
  ExprBuilder t st fs 
  -> ExecutorFlags
  -> Expression a
  -> Expression a
  -> SymState (ExprBuilder t st fs) a
  -> IO [SymState (ExprBuilder t st fs) a]

execAssign sym flags lhs rhs state =
    case lhs of
        ExpValue _ann _span (ValVariable name) -> 
            execVariableAssign sym flags name rhs state

        ExpSubscript _ann _span baseExpr indicesInfo ->
            execArrayElementAssign sym flags baseExpr (alistList indicesInfo) rhs state


        _ -> error "Left-hand side of assignment must be a variable"


execVariableAssign ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    VarName ->
    Expression a ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]
execVariableAssign sym flags name rhs state =
    case Map.lookup name (env state) of
        Nothing ->
            error $ "Assignment to undeclared variable: " ++ name

        Just binding ->
            case varType binding of
                VarArray _ _ ->
                    case varValue binding of
                        Nothing -> error $ "Assignment to unallocated array: " ++ name
                        Just _ -> execWholeArrayAssign sym flags name binding rhs state

                _ -> execScalarAssign sym flags name binding rhs state


execScalarAssign ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> VarName
    -> VarBinding (ExprBuilder t st fs)
    -> Expression a
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]
execScalarAssign sym flags name binding rhs state = do
    bindValueOutcomes
        (evalExpr sym flags rhs state)
        (\(rhsBeforeCoerce, state1) -> do
            rhsAfterCoerce <- coerceOnAssignment sym (varType binding) rhsBeforeCoerce

            pure [state1 { env = Map.insert name (VarBinding (varType binding) (Just rhsAfterCoerce)) (env state1) }]
        )
        (\haltedState -> pure [haltedState])
                    

-- only supports single element assigns for now
execArrayElementAssign ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> Expression a
    -> [Index a]
    -> Expression a
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]

execArrayElementAssign sym flags baseExpr indexExprs rhs state = do
    name <-
        case baseExpr of
            ExpValue _ann _span (ValVariable arrayName) -> pure arrayName
            _ -> error "Unsupported array assignment target"

    case Map.lookup name (env state) of
        Nothing -> error $ "Assignment to undeclared array: " ++ name
        Just _ -> pure ()

    bindBranches
        (evalArrayIndices sym flags indexExprs state)
        (\outcome ->
            case outcome of
                (Nothing, haltedState) -> pure [haltedState]
                (Just indices, state1) ->
                    bindValueOutcomes
                        (evalExpr sym flags rhs state1)
                        (\(rhsBeforeCoerce, state2) -> do
                            currentBinding <-
                                case Map.lookup name (env state2) of
                                    Nothing -> error $ "Array disappeared during evaluation: " ++ name
                                    Just binding -> pure binding

                            currentArray <-
                                case varValue currentBinding of
                                    Nothing -> error $ "Assignment to uninitialised array: " ++ name
                                    Just value -> pure value

                            rhsAfterCoerce <- coerceOnAssignment sym (arrayElementType currentArray) rhsBeforeCoerce

                            bindValueOutcomes
                                (updateSomeArray sym flags currentArray indices rhsAfterCoerce state2)
                                (\(updatedArrayValue, state3) ->
                                    let updatedBinding = currentBinding { varValue = Just updatedArrayValue }
                                        finalState = state3 { env = Map.insert name updatedBinding (env state3) }
                                    in pure [finalState]
                                )
                                (\haltedState -> pure [haltedState])
                        )
                        (\haltedState -> pure [haltedState])
        )
    


execWholeArrayAssign ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    VarName ->
    VarBinding (ExprBuilder t st fs) ->
    Expression a ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]
execWholeArrayAssign sym flags name binding initExpr state = do
    arrayExpr <-
        case varValue binding of
            Nothing -> error $ "Assignment to uninitialised array: " ++ name
            Just value -> pure value

    let dimensions =
            case arrayExpr of
                SomeIntArray record -> arrayDimensions record
                SomeRealArray record -> arrayDimensions record
                SomeBoolArray record -> arrayDimensions record
                _ -> error $ "Expected array expression: " ++ name

        elementType =
            case varType binding of
                VarArray ty _ -> ty
                _ -> error $ "Expected array binding: " ++ name

    case initExpr of
        -- e.g. vec = [1, 2, 3]
        ExpInitialisation _ann _span elementsInfo ->
            bindValueOutcomes
                (createArrayFromConstructor
                    sym
                    flags
                    name
                    elementType
                    dimensions
                    (alistList elementsInfo)
                    state
                )
                (\(arrayValue, state1) ->
                    pure [state1 { env = Map.insert name (binding {varValue = Just arrayValue}) (env state1) }]
                )
                (\haltedState -> pure [haltedState])

        _ ->
            bindValueOutcomes
                (evalExpr sym flags initExpr state)
                (\(initValue, state1) ->
                    case initValue of
                        --array copy assign
                        SomeIntArray _ -> do
                            bindValueOutcomes
                                (coerceArrayOnAssignment sym flags arrayExpr initValue state1)
                                (\(arrayValue, state2) -> pure [state2 { env = Map.insert name (binding {varValue = Just arrayValue}) (env state2) }])
                                (\haltedState -> pure [haltedState])
                        SomeRealArray _ -> do
                            bindValueOutcomes
                                (coerceArrayOnAssignment sym flags arrayExpr initValue state1)
                                (\(arrayValue, state2) -> pure [state2 { env = Map.insert name (binding {varValue = Just arrayValue}) (env state2) }])
                                (\haltedState -> pure [haltedState])
                        SomeBoolArray _ -> do
                            bindValueOutcomes
                                (coerceArrayOnAssignment sym flags arrayExpr initValue state1)
                                (\(arrayValue, state2) -> pure [state2 { env = Map.insert name (binding {varValue = Just arrayValue}) (env state2) }])
                                (\haltedState -> pure [haltedState])

                        _ -> do --constant array assign (every element filled with expr)
                            coercedValue <- coerceOnAssignment sym elementType initValue
                            arrayValue <- createConstantArray sym dimensions coercedValue
                            pure [state1 { env = Map.insert name (binding {varValue = Just arrayValue}) (env state1) }]
                )
                (\haltedState -> pure [haltedState])



execRead2s :: IsSymExprBuilder sym
    => sym
    -> Maybe (AList Expression a)
    -> SymState sym a
    -> IO (SymState sym a)

execRead2s sym maybeReadList state =
    case maybeReadList of
        Nothing -> pure state
        Just readList -> execRead2Vars sym (readTargetNames (alistList readList)) state --strip readList into a Stringlist of variable names
    where
        readTargetNames :: [Expression a] -> [VarName]
        readTargetNames = map readTargetName

        readTargetName :: Expression a -> VarName
        readTargetName expr =
            case expr of
                ExpValue _ann _span (ValVariable name) ->  name
                _ -> error "Non-variable read target"

execRead2Vars :: IsSymExprBuilder sym
    => sym
    -> [VarName]
    -> SymState sym a
    -> IO (SymState sym a)

execRead2Vars sym names state =
    case names of
        [] -> pure state
        name:rest -> do
            newState <- execRead2Var sym name state
            execRead2Vars sym rest newState

execRead2Var :: IsSymExprBuilder sym
    => sym
    -> VarName
    -> SymState sym a
    -> IO (SymState sym a)

execRead2Var sym name state =
    case Map.lookup name (env state) of
        Nothing -> error ("Read into undeclared variable: " ++ name)
        Just binding -> do
            let n = freshCount state
                inputName = name ++ "_input_" ++ show n

            freshVal <- freshInputForType sym inputName (varType binding)
            let newBinding = VarBinding (varType binding) (Just freshVal)
            pure state { env = Map.insert name newBinding (env state), freshCount = n+1 }

freshInputForType :: IsSymExprBuilder sym
    => sym
    -> String
    -> VarType
    -> IO (SomeExpr sym)

freshInputForType sym inputName varTy =
    case varTy of
        VarInt -> do
            x <- freshConstant sym (safeSymbol inputName) BaseIntegerRepr
            pure (SomeInt x)
        VarReal -> do
            x <- freshConstant sym (safeSymbol inputName) BaseRealRepr
            pure (SomeReal x)
        VarBool -> do
            x <- freshConstant sym (safeSymbol inputName) BaseBoolRepr
            pure (SomeBool x)




execIfLogical ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    Expression a ->
    Statement a ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]
execIfLogical sym flags cond stmt state = 
    bindValueOutcomes
        (evalExpr sym flags cond state)
        (\(condVal, state1) ->
            case condVal of
                SomeBool p -> do
                    notP <- notPred sym p

                    maybeThenState <-
                        addPathConditionAndKeepIfFeasible sym p state1

                    maybeElseState <-
                        addPathConditionAndKeepIfFeasible sym notP state1

                    thenResults <-
                        maybe
                            (pure [])
                            (execStatement sym flags stmt)
                            maybeThenState

                    let elseResults = maybe [] pure maybeElseState

                    pure (thenResults ++ elseResults)

                _ ->
                    error "Logical IF condition must evaluate to logical"
        )
        (\haltedState -> pure [haltedState])


--take argument list from preprocessed call, convert to predicate and add to user obligations
execAssertionArguments :: 
    ExprBuilder t st fs
    -> ExecutorFlags
    -> [Argument a]
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]
execAssertionArguments sym flags arguments state =
    case arguments of
        [Argument _ann _span Nothing (ArgExpr expr)] -> execAssertionExpr sym flags expr state
        _ ->
            error "fortsymb_assert expects exactly one argument"

execAssertionExpr :: 
    ExprBuilder t st fs
    -> ExecutorFlags
    -> Expression a
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]
execAssertionExpr sym flags assertionExpr state =
    bindValueOutcomes
        (evalExpr sym flags assertionExpr state)
        (\(assertionValue, newState) ->
            case assertionValue of
                SomeBool predicate -> do
                    stateAfterCheck <-
                        if isObligationEnabled flags UserAssertions
                            then addObligationAndAssume sym UserAssertions predicate newState
                            else pure newState
                    pure [stateAfterCheck]

                _ -> error "Assertion is not a logical predicate"
        )
        (\haltedState -> pure [haltedState])


execIfClauses ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    [(Expression a, [Block a])] ->
    Maybe [Block a] ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]
execIfClauses sym flags condAndBlocks maybeElseBlocks state =
    case condAndBlocks of
        [] ->
            maybe
                (pure [state])
                (\elseBlocks ->
                    execBlocks sym flags elseBlocks state
                )
                maybeElseBlocks

        (cond, blocks) : restClauses -> do
            bindValueOutcomes
                (evalExpr sym flags cond state)
                (\(condVal, state1) ->
                    case condVal of
                        SomeBool p -> do
                            notP <- notPred sym p
                            maybeThenState <- addPathConditionAndKeepIfFeasible sym p state1
                            maybeElseState <- addPathConditionAndKeepIfFeasible sym notP state1

                            thenResults <-
                                maybe
                                    (pure [])
                                    (execBlocks sym flags blocks)
                                    maybeThenState

                            restResults <-
                                maybe
                                    (pure [])
                                    (\elseState ->
                                        execIfClauses sym flags restClauses maybeElseBlocks elseState
                                    )
                                    maybeElseState

                            pure (thenResults ++ restResults)

                        _ -> error "Logical IF condition must evaluate to logical"
                )
                (\haltedState -> pure [haltedState])


evalFunctionCall :: 
    ExprBuilder t st fs
    -> ExecutorFlags
    -> Expression a
    -> [Argument a]
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a]
evalFunctionCall sym flags functionExpr arguments callerState = do
    functionName <-
        case functionExpr of
            ExpValue _ann _span (ValVariable name) -> pure name
            _ -> error "Unsupported function designator"

    functionDef <-
            case Map.lookup functionName (procedureEnv callerState) of
                Just def -> pure def
                Nothing -> error $ "Unknown function: " ++ functionName

    let matchedArguments = matchProcedureArguments (functionParameters functionDef) arguments
    bindBranches
        (evalMatchedFunctionArguments sym flags matchedArguments callerState)
        (\outcome ->
            case outcome of
                (Nothing, haltedState) -> pure [ValueComputationHaltedState haltedState]
                (Just evaluatedArguments, callerState1) ->
                    execFunctionDefinition
                        sym
                        flags
                        functionName
                        functionDef
                        evaluatedArguments
                        callerState1
        )


execFunctionDefinition :: 
    ExprBuilder t st fs
    -> ExecutorFlags 
    -> String 
    -> ProcedureDef a 
    -> [(VarName, SomeExpr (ExprBuilder t st fs))] 
    -> SymState (ExprBuilder t st fs) a 
    -> IO [ValueOutcome (ExprBuilder t st fs) a]

execFunctionDefinition sym flags functionName functionDef argumentValues callerState =
    case functionDef of
        FunctionDef {
            functionResult = resultName, 
            functionBody = body, 
            functionMaybeReturnTypeSpec = maybeReturnTypeSpec
        } -> do
            -- need a fresh env for local scope
            let initialLocalState = callerState { env = Map.empty }

            -- first split blocks into declaration blocks and other blocks
            --      "span, applied to a predicate p and a list xs, returns a tuple where 
            --      first element is longest prefix (possibly empty) of xs of elements 
            --      that satisfy p and second element is the remainder of the list"
            let (declarationBlocks, executableBlocks) =
                    span 
                    (\block -> case block of
                        BlStatement _ann _span _label StDeclaration{} -> True
                        BlStatement _ann _span _label StImplicit{} -> True
                        _ -> False
                    ) 
                    body

            bindBranches
                (execBlocks sym flags declarationBlocks initialLocalState)
                (\declaredLocalState ->
                    case executionStatus declaredLocalState of
                        ExecutionHalted _ -> pure [ValueComputationHaltedState (restoreCallerState callerState declaredLocalState)]
                        ExecutionComplete ->
                            bindBranches
                                (bindFunctionParameters sym flags argumentValues declaredLocalState)
                                (\boundLocalState ->
                                    case executionStatus boundLocalState of
                                        ExecutionHalted _ -> pure [ValueComputationHaltedState (restoreCallerState callerState boundLocalState)]
                                        ExecutionComplete -> do
                                            returnBindingLocalState <-
                                                case maybeReturnTypeSpec of
                                                    Nothing -> pure boundLocalState
                                                    Just returnTypeSpec -> do
                                                        let returnBinding = VarBinding (getVarType returnTypeSpec) Nothing
                                                        pure boundLocalState { env = Map.insert resultName returnBinding (env boundLocalState) }

                                            bindBranches
                                                (execBlocks sym flags executableBlocks returnBindingLocalState)
                                                (\localState ->
                                                    case executionStatus localState of
                                                        ExecutionHalted _ -> pure [ValueComputationHaltedState (restoreCallerState callerState localState)]
                                                        ExecutionComplete -> do
                                                            result <- returnFunctionResult resultName callerState localState
                                                            pure [result]
                                                )
                                )
                )

        _ -> error $ "Not a function: " ++ functionName


    where
        restoreCallerState callerState localState =
            callerState
                { pathCond = pathCond localState
                , obligations = obligations localState
                , freshCount = freshCount localState
                , executionStatus = executionStatus localState
                }

        returnFunctionResult :: 
            VarName -> 
            SymState (ExprBuilder t st fs) a -> 
            SymState (ExprBuilder t st fs) a -> 
            IO (ValueOutcome (ExprBuilder t st fs) a)
        returnFunctionResult resultName callerState localState =
            case Map.lookup resultName (env localState) of
                Nothing -> error $ "Function result variable is not declared: " ++ resultName

                Just binding ->
                    case varValue binding of
                        Nothing -> error $ "Function result variable is uninitialised: " ++ resultName
                        Just resultValue ->
                            --remove env in local scope, but pathCond, freshCount and obligations need to survive
                            pure
                                ( ValueAndStateProduced
                                    resultValue
                                    ( callerState
                                        { pathCond = pathCond localState
                                        , obligations = obligations localState
                                        , freshCount = freshCount localState
                                        }
                                    )
                                )


                            
evalSubroutineCall :: 
    ExprBuilder t st fs
    -> ExecutorFlags
    -> Expression a
    -> [Argument a]
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]

evalSubroutineCall sym flags subroutineExpr arguments callerState = do
    subroutineName <-
        case subroutineExpr of
            ExpValue _ann _span (ValVariable name) -> pure name
            _ -> error "Unsupported subroutine designator"

    subroutineDef <-
        case Map.lookup subroutineName (procedureEnv callerState) of
            Just def -> pure def
            Nothing -> error $ "Unknown subroutine: " ++ subroutineName

    let matchedArguments = matchProcedureArguments (subroutineParameters subroutineDef) arguments
    bindBranches
        (evalMatchedSubroutineArguments sym flags matchedArguments callerState)
        (\outcome ->
            case outcome of
                (Nothing, haltedState) -> pure [haltedState]
                (Just evaluatedArguments, callerState1) ->
                    execSubroutineDefinition
                        sym
                        flags
                        subroutineName
                        subroutineDef
                        matchedArguments
                        evaluatedArguments
                        callerState1
        )



execSubroutineDefinition :: 
    ExprBuilder t st fs 
    -> ExecutorFlags 
    -> String 
    -> ProcedureDef a 
    -> [(VarName, Expression a)] 
    -> [(VarName, Maybe (SomeExpr (ExprBuilder t st fs)))]
    -> SymState (ExprBuilder t st fs) a 
    -> IO [SymState (ExprBuilder t st fs) a]

execSubroutineDefinition sym flags subroutineName subroutineDef matchedArguments argumentValues callerState = 
    case subroutineDef of
        SubroutineDef { subroutineBody = body } -> do
            let initialLocalState = callerState { env = Map.empty }

            let (declarationBlocks, executableBlocks) =
                    span 
                    (\block -> case block of
                        BlStatement _ann _span _label StDeclaration{} -> True
                        BlStatement _ann _span _label StImplicit{} -> True
                        _ -> False
                    ) 
                    body

            bindBranches
                (execBlocks sym flags declarationBlocks initialLocalState)
                (\declaredLocalState ->
                    case executionStatus declaredLocalState of
                        ExecutionHalted _ -> pure [restoreCallerState callerState declaredLocalState]
                        ExecutionComplete ->
                            bindBranches
                                (bindSubroutineParameters sym flags argumentValues declaredLocalState)
                                (\boundLocalState ->
                                    case executionStatus boundLocalState of
                                        ExecutionHalted _ -> pure [restoreCallerState callerState boundLocalState]
                                        ExecutionComplete ->
                                            bindBranches
                                                (execBlocks sym flags executableBlocks boundLocalState)
                                                (\finalLocalState ->
                                                    case executionStatus finalLocalState of
                                                        ExecutionHalted _ -> pure [restoreCallerState callerState finalLocalState]
                                                        ExecutionComplete -> do
                                                            returnedState <- returnSubroutineState matchedArguments callerState finalLocalState
                                                            pure [returnedState]
                                                )
                                )
                )

        _ -> error $ "Not a subroutine: " ++ subroutineName

    where
        restoreCallerState callerState localState =
            callerState
                { pathCond = pathCond localState
                , obligations = obligations localState
                , freshCount = freshCount localState
                , executionStatus = executionStatus localState
                }

        returnSubroutineState matchedArguments callerState localState = do
            updatedCallerEnv <- copyArgumentsBack (env callerState) matchedArguments
            pure callerState
                { env = updatedCallerEnv
                , pathCond = pathCond localState
                , obligations = obligations localState
                , freshCount = freshCount localState
                }

            where
                copyArgumentsBack callerEnv argumentPairs =
                    case argumentPairs of
                        [] -> pure callerEnv
                        (parameterName, argumentExpr) : rest -> do
                            argumentName <-
                                case argumentExpr of
                                    ExpValue _ann _span (ValVariable name) -> pure name
                                    _ -> error $ "Subroutine argument for parameter " ++ parameterName ++ " must currently be a variable, cannot do e.g. call foo(x+11)"
                            
                            parameterBinding <-
                                case Map.lookup parameterName (env localState) of
                                    Nothing -> error $ "Subroutine parameter is not declared: " ++ parameterName
                                    Just binding -> pure binding
                            
                            callerBinding <-
                                case Map.lookup argumentName callerEnv of
                                    Nothing -> error $ "Subroutine argument is not declared in caller: " ++ argumentName
                                    Just binding -> pure binding

                            let updatedCallerEnv = Map.insert argumentName (callerBinding { varValue = varValue parameterBinding }) callerEnv
                            copyArgumentsBack updatedCallerEnv rest


