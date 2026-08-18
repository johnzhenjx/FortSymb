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
import Designators
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

        BlCase
            _ann
            _span
            _label
            _name
            selector
            cases
            maybeDefaultBlocks
            _endSelectLabel ->
                -- fortran-src 0.16.9 stores the CASE DEFAULT body in
                -- reverse source order, unlike the ordinary CASE bodies.
                execSelectCase sym flags selector cases (reverse <$> maybeDefaultBlocks) state


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

        BlDoWhile
            _ann
            span
            _label
            maybeName
            _terminationLabel
            condition
            body
            _maybeEndDo ->
                execDoWhileBlock sym flags span maybeName condition body state



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
                                                state4 <- addIncrementStepNonZeroObligation sym span incrementInt state3
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
        addIncrementStepNonZeroObligation sym obligationSpan increment state = do
            zero <- intLit sym 0
            incrementIsNonZero <- notPred sym =<< intEq sym increment zero
            addObligationAndAssume sym IncrementStepNonZero obligationSpan incrementIsNonZero state


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
                    do
                        ensureBindingWritable name binding
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


execDoWhileBlock ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    SrcSpan ->
    Maybe String ->
    Expression a ->
    [Block a] ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]
execDoWhileBlock sym flags span maybeName condition body state =
    runDoWhileLoop sym flags span 0 maybeName condition body state


runDoWhileLoop ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    SrcSpan ->
    Int ->
    Maybe String ->
    Expression a ->
    [Block a] ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]
runDoWhileLoop sym flags span unrollCount maybeName condition body state =
    bindValueOutcomes
        (evalExpr sym flags condition state)
        (\(conditionValue, state1) ->
            case conditionValue of
                SomeBool conditionPredicate -> do
                    exitPredicate <- notPred sym conditionPredicate
                    maybeContinueState <- addPathConditionAndKeepIfFeasible sym conditionPredicate state1
                    maybeExitState <- addPathConditionAndKeepIfFeasible sym exitPredicate state1

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
                                | otherwise ->
                                    bindBranches
                                        (execBlocks sym flags body continueState)
                                        (\bodyState ->
                                            case executionStatus bodyState of
                                                ExecutionHalted _ -> pure [bodyState]
                                                ExecutionComplete ->
                                                    runDoWhileLoop
                                                        sym
                                                        flags
                                                        span
                                                        (unrollCount + 1)
                                                        maybeName
                                                        condition
                                                        body
                                                        bodyState
                                        )

                    let exitStates =
                            case maybeExitState of
                                Nothing -> []
                                Just exitState -> [exitState]

                    pure (exitStates ++ continuingStates)

                _ -> error "DO WHILE condition must evaluate to logical"
        )
        (\haltedState -> pure [haltedState])



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
        StIntent _ann _span intent variablesInfo ->
            setVariableIntents intent (alistList variablesInfo) state
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


setVariableIntents ::
    Intent
    -> [Expression a]
    -> SymState sym a
    -> IO [SymState sym a]
setVariableIntents intent variables state =
    case variables of
        [] -> pure [state]
        variable : remaining -> do
            name <-
                case variable of
                    ExpValue _ann _span (ValVariable variableName) ->
                        pure variableName
                    _ -> error "INTENT target must be a variable"

            binding <-
                case Map.lookup name (env state) of
                    Nothing -> error $ "INTENT target is not declared: " ++ name
                    Just existingBinding -> pure existingBinding

            let state1 =
                    state
                        { env =
                            Map.insert
                                name
                                (binding { varIntent = Just intent })
                                (env state)
                        }
            setVariableIntents intent remaining state1


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
                nestedStates <- mapM (allocateObject allocationObject) states
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

                Just binding -> do
                    ensureBindingWritable name binding
                    case varType binding of
                        VarArray elementType rank ->
                            case varValue binding of
                                Just _ -> error $ "Array is already allocated: " ++ name

                                Nothing ->
                                    bindValueOutcomes
                                        (evalAllocationDimensionIxs indexExprs state)
                                        (\(dimensions, state1) ->
                                            if length dimensions /= rank then error $ "Allocation rank does not match declaration: " ++ name

                                            else do
                                                arrayExpr <- createUninitialisedArray sym name elementType dimensions
                                                let updatedBinding = binding { varValue = Just arrayExpr }
                                                pure [state1 { env = Map.insert name updatedBinding (env state1) }]
                                        )
                                        (\haltedState -> pure [haltedState])

                        _ -> error $ "Variable is not an array: " ++ name


        evalAllocationDimensionIxs indexExprs state =
            case indexExprs of
                [] -> pure [ValueAndStateProduced [] state]

                indexExpr : remainingExprs ->
                    bindValueOutcomes
                        (evalAllocationDimensionIx indexExpr state)
                        (\(dimension, state1) ->
                            bindValueOutcomes
                                (evalAllocationDimensionIxs remainingExprs state1)
                                (\(remainingDimensions, finalState) ->
                                    pure [ValueAndStateProduced (dimension : remainingDimensions) finalState]
                                )
                                (\haltedState -> pure [ValueComputationHaltedState haltedState])
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])

        evalAllocationDimensionIx indexExpr state =
            case indexExpr of
                IxSingle _ann _span _name upperExpr -> do
                    lowerBound <- intLit sym 1

                    bindValueOutcomes
                        (evalExpr sym flags upperExpr state)
                        (\(upperValue, state1) ->
                            case upperValue of
                                SomeInt upperBound ->
                                    pure
                                        [ ValueAndStateProduced
                                            (ArrayDimension { dimensionLower = lowerBound, dimensionUpper = upperBound })
                                            state1
                                        ]
                                _ -> error "Allocation upper bound must be an integer"
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])

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
                                                            pure
                                                                [ ValueAndStateProduced
                                                                    (ArrayDimension { dimensionLower = lowerBound, dimensionUpper = upperBound })
                                                                    state2
                                                                ]
                                                        _ -> error "Allocation upper bound must be an integer"
                                                )
                                                (\haltedState -> pure [ValueComputationHaltedState haltedState])
                                _ -> error "Allocation lower bound must be an integer"
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])

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
                            declareScalarVar sym flags typeSpec attributes name (declaratorInitial decl) state
                ArrayDecl dimensionListInfo ->
                    declareArrayVar sym flags typeSpec attributes name dimensionListInfo (declaratorInitial decl) state
        _ -> error "Declaration target is not a variable"


declareScalarVar ::
    ExprBuilder t st fs
    -> ExecutorFlags 
    -> TypeSpec a 
    -> [Attribute a]
    -> VarName 
    -> Maybe (Expression a) 
    -> SymState (ExprBuilder t st fs) a 
    -> IO [SymState (ExprBuilder t st fs) a]
declareScalarVar sym flags typeSpec attributes name maybeInitial state =
    case maybeInitial of
        Nothing ->
            pure [ state 
                    { env = 
                        Map.insert 
                            name 
                            (VarBinding (getVarType typeSpec) Nothing (attributeIntent attributes))
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
                                    (VarBinding (getVarType typeSpec) (Just valueAfterCoercion) (attributeIntent attributes))
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
        pure [ state { env = Map.insert name (VarBinding arrayType Nothing (attributeIntent attributes)) (env state) } ]

    | otherwise = do
        bindValueOutcomes
            (evalArrayDimensions sym flags (alistList dimensionListInfo) state)
            (\(dimensions, state1) ->
                case maybeInitial of
                    Nothing -> do
                        arrayValue <- createUninitialisedArray sym name (getVarType typeSpec) dimensions
                        pure [state1 { env = Map.insert name (VarBinding arrayType (Just arrayValue) (attributeIntent attributes)) (env state1) }]

                    Just (ExpInitialisation _ann span elementsInfo) ->
                        bindValueOutcomes
                            (createArrayFromConstructor
                                sym
                                flags
                                span
                                name
                                (getVarType typeSpec)
                                dimensions
                                (alistList elementsInfo)
                                state1
                            )
                            (\(arrayValue, state2) ->
                                pure [ state2 { env = Map.insert name (VarBinding arrayType (Just arrayValue) (attributeIntent attributes)) (env state2) }]
                            )
                            (\haltedState -> pure [haltedState])

                    Just initExpr ->
                        bindValueOutcomes
                            (evalExpr sym flags initExpr state1)
                            (\(initValue, state2) -> do
                                coercedValue <- coerceOnAssignment sym (getVarType typeSpec) initValue
                                arrayValue <- createConstantArray sym dimensions coercedValue
                                pure [ state2 { env = Map.insert name (VarBinding arrayType (Just arrayValue) (attributeIntent attributes)) (env state2) }]
                            )
                            (\haltedState -> pure [haltedState])
            )
            (\haltedState -> pure [haltedState])
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
        ExpValue _ann span (ValVariable name) ->
            execVariableAssign sym flags span name rhs state

        ExpSubscript _ann span baseExpr indicesInfo ->
            execArraySubscriptAssign sym flags span baseExpr (alistList indicesInfo) rhs state


        _ -> error "Left-hand side of assignment must be a variable"


execVariableAssign ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    SrcSpan ->
    VarName ->
    Expression a ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]
execVariableAssign sym flags span name rhs state =
    case Map.lookup name (env state) of
        Nothing ->
            error $ "Assignment to undeclared variable: " ++ name

        Just binding ->
            do
                ensureBindingWritable name binding
                case varType binding of
                    VarArray _ _ ->
                        case varValue binding of
                            Nothing -> error $ "Assignment to unallocated array: " ++ name
                            Just _ -> execWholeArrayAssign sym flags span name binding rhs state

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

            pure [state1 { env = Map.insert name (binding { varValue = Just rhsAfterCoerce }) (env state1) }]
        )
        (\haltedState -> pure [haltedState])
                    

--supports scalar element and array-section assignment targets
execArraySubscriptAssign ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> Expression a
    -> [Index a]
    -> Expression a
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]

execArraySubscriptAssign sym flags span baseExpr indexExprs rhs state = do
    bindValueOutcomes
        (evalArrayDesignator sym flags span baseExpr indexExprs state)
        (\(designator, state1) ->
            bindValueOutcomes
                (evalExpr sym flags rhs state1)
                (\(rhsValue, state2) ->
                    writeDesignator sym flags designator rhsValue state2)
                (\haltedState -> pure [haltedState])
        )
        (\haltedState -> pure [haltedState])


execWholeArrayAssign ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    SrcSpan ->
    VarName ->
    VarBinding (ExprBuilder t st fs) ->
    Expression a ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]
execWholeArrayAssign sym flags span name binding initExpr state = do
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
        ExpInitialisation _ann constructorSpan elementsInfo ->
            bindValueOutcomes
                (createArrayFromConstructor
                    sym
                    flags
                    constructorSpan
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
                                (coerceArrayOnAssignment sym flags span arrayExpr initValue state1)
                                (\(arrayValue, state2) -> pure [state2 { env = Map.insert name (binding {varValue = Just arrayValue}) (env state2) }])
                                (\haltedState -> pure [haltedState])
                        SomeRealArray _ -> do
                            bindValueOutcomes
                                (coerceArrayOnAssignment sym flags span arrayExpr initValue state1)
                                (\(arrayValue, state2) -> pure [state2 { env = Map.insert name (binding {varValue = Just arrayValue}) (env state2) }])
                                (\haltedState -> pure [haltedState])
                        SomeBoolArray _ -> do
                            bindValueOutcomes
                                (coerceArrayOnAssignment sym flags span arrayExpr initValue state1)
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
            ensureBindingWritable name binding
            let n = freshCount state
                inputName = name ++ "_input_" ++ show n

            freshVal <- freshInputForType sym inputName (varType binding)
            let newBinding = VarBinding (varType binding) (Just freshVal) (varIntent binding)
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
        [Argument _ann span Nothing (ArgExpr expr)] -> execAssertionExpr sym flags span expr state
        _ ->
            error "fortsymb_assert expects exactly one argument"

execAssertionExpr :: 
    ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> Expression a
    -> SymState (ExprBuilder t st fs) a
    -> IO [SymState (ExprBuilder t st fs) a]
execAssertionExpr sym flags span assertionExpr state =
    bindValueOutcomes
        (evalExpr sym flags assertionExpr state)
        (\(assertionValue, newState) ->
            case assertionValue of
                SomeBool predicate -> do
                    stateAfterCheck <-
                        if userAssertionEnabled flags
                            then addObligationAndAssume sym UserAssertion span predicate newState
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


execSelectCase ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    Expression a ->
    [(AList Index a, [Block a])] ->
    Maybe [Block a] ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]
execSelectCase sym flags selector cases maybeDefaultBlocks state =
    bindValueOutcomes
        (evalExpr sym flags selector state)
        (\(selectorValue, state1) ->
            case selectorValue of
                SomeInt _ -> execCaseClauses sym flags selectorValue cases maybeDefaultBlocks state1
                SomeBool _ -> execCaseClauses sym flags selectorValue cases maybeDefaultBlocks state1
                _ -> error "SELECT CASE selector must be an integer or logical scalar"
        )
        (\haltedState -> pure [haltedState])


execCaseClauses ::
    ExprBuilder t st fs ->
    ExecutorFlags ->
    SomeExpr (ExprBuilder t st fs) ->
    [(AList Index a, [Block a])] ->
    Maybe [Block a] ->
    SymState (ExprBuilder t st fs) a ->
    IO [SymState (ExprBuilder t st fs) a]
execCaseClauses sym flags selectorValue cases maybeDefaultBlocks state =
    case cases of
        [] ->
            maybe
                (pure [state])
                (\defaultBlocks -> execBlocks sym flags defaultBlocks state)
                maybeDefaultBlocks

        (caseSelectorsInfo, caseBlocks) : remainingCases ->
            bindValueOutcomes
                (evalCaseSelectors sym flags selectorValue (alistList caseSelectorsInfo) state)
                (\(casePredicateValue, state1) ->
                    case casePredicateValue of
                        SomeBool casePredicate -> do
                            notCasePredicate <- notPred sym casePredicate
                            maybeMatchingState <- addPathConditionAndKeepIfFeasible sym casePredicate state1
                            maybeRemainingState <- addPathConditionAndKeepIfFeasible sym notCasePredicate state1

                            matchingResults <-
                                maybe
                                    (pure [])
                                    (execBlocks sym flags caseBlocks)
                                    maybeMatchingState

                            remainingResults <-
                                maybe
                                    (pure [])
                                    (execCaseClauses sym flags selectorValue remainingCases maybeDefaultBlocks)
                                    maybeRemainingState

                            pure (matchingResults ++ remainingResults)

                        _ -> error "Internal error: CASE selector list did not produce a logical predicate"
                )
                (\haltedState -> pure [haltedState])

    where
        -- select case (x)
        -- case (1, 3:5)
        --     y = 10
        -- case (6:)
        --     y = 20
        -- case default
        --     y = 30
        -- end select

        -- is parsed as

        -- BlCase
        --     ...
        --     x
        --     [ ( AList
        --           [ IxSingle ... 1
        --           , IxRange ... (Just 3) (Just 5) Nothing
        --           ]
        --       , [y = 10]
        --       )
        --     , ( AList
        --           [ IxRange ... (Just 6) Nothing Nothing ]
        --       , [y = 20]
        --       )
        --     ]
        --     (Just [y = 30])
        --     ...

        evalCaseSelectors ::
            ExprBuilder t st fs ->
            ExecutorFlags ->
            SomeExpr (ExprBuilder t st fs) ->
            [Index a] ->
            SymState (ExprBuilder t st fs) a ->
            IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
        evalCaseSelectors sym flags selectorValue caseSelectors state =
            case caseSelectors of
                [] -> pure [ValueAndStateProduced (SomeBool (falsePred sym)) state]

                caseSelector : remainingSelectors ->
                    bindValueOutcomes
                        (evalCaseSelector sym flags selectorValue caseSelector state)
                        (\(selectorPredicateValue, state1) ->
                            case selectorPredicateValue of
                                SomeBool selectorPredicate ->
                                    bindValueOutcomes
                                        (evalCaseSelectors sym flags selectorValue remainingSelectors state1)
                                        (\(remainingPredicateValue, state2) ->
                                            case remainingPredicateValue of
                                                SomeBool remainingPredicate -> do
                                                    combinedPredicate <- orPred sym selectorPredicate remainingPredicate
                                                    pure [ ValueAndStateProduced (SomeBool combinedPredicate) state2 ]
                                                _ -> error "CASE selector list did not produce a logical predicate"
                                        )
                                        (\haltedState -> pure [ValueComputationHaltedState haltedState])

                                _ -> error "CASE selector did not produce a logical predicate"
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])


        evalCaseSelector ::
            ExprBuilder t st fs ->
            ExecutorFlags ->
            SomeExpr (ExprBuilder t st fs) ->
            Index a ->
            SymState (ExprBuilder t st fs) a ->
            IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
        evalCaseSelector sym flags selectorValue caseSelector state =
            case caseSelector of
                IxSingle _ann _span _name caseExpr ->
                    bindValueOutcomes
                        (evalExpr sym flags caseExpr state)
                        (\(caseValue, state1) -> do
                            predicate <- caseValuesEqual sym selectorValue caseValue
                            pure [ValueAndStateProduced (SomeBool predicate) state1]
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])

                IxRange _ann _span maybeLowerExpr maybeUpperExpr maybeStride ->
                    case maybeStride of
                        Just _ -> error "CASE ranges with a stride are not valid Fortran SELECT CASE selectors"
                        Nothing -> evalCaseRange sym flags selectorValue maybeLowerExpr maybeUpperExpr state


        caseValuesEqual ::
            IsSymExprBuilder sym =>
            sym ->
            SomeExpr sym ->
            SomeExpr sym ->
            IO (Pred sym)
        caseValuesEqual sym selectorValue caseValue =
            case (selectorValue, caseValue) of
                (SomeInt selectorInteger, SomeInt caseInteger) -> intEq sym selectorInteger caseInteger
                (SomeBool selectorPredicate, SomeBool casePredicate) -> eqPred sym selectorPredicate casePredicate
                _ -> error "CASE value must have the same integer or logical type as the SELECT CASE selector"


        evalCaseRange ::
            ExprBuilder t st fs ->
            ExecutorFlags ->
            SomeExpr (ExprBuilder t st fs) ->
            Maybe (Expression a) ->
            Maybe (Expression a) ->
            SymState (ExprBuilder t st fs) a ->
            IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
        evalCaseRange sym flags selectorValue maybeLowerExpr maybeUpperExpr state =
            case selectorValue of
                SomeInt selectorInteger -> evalLowerBound selectorInteger state
                _ -> error "CASE ranges require an integer selector"
            where
                evalLowerBound selectorInteger state1 =
                    case maybeLowerExpr of
                        Nothing -> evalUpperBound selectorInteger (truePred sym) state1
                        Just lowerExpr ->
                            bindValueOutcomes
                                (evalExpr sym flags lowerExpr state1)
                                (\(lowerValue, state2) ->
                                    case lowerValue of
                                        SomeInt lowerInteger -> do
                                            lowerPredicate <- intLe sym lowerInteger selectorInteger
                                            evalUpperBound selectorInteger lowerPredicate state2
                                        _ -> error "CASE range bounds must be integer expressions"
                                )
                                (\haltedState -> pure [ValueComputationHaltedState haltedState])

                evalUpperBound selectorInteger lowerPredicate state1 =
                    case maybeUpperExpr of
                        Nothing -> pure [ValueAndStateProduced (SomeBool lowerPredicate) state1]
                        Just upperExpr ->
                            bindValueOutcomes
                                (evalExpr sym flags upperExpr state1)
                                (\(upperValue, state2) ->
                                    case upperValue of
                                        SomeInt upperInteger -> do
                                            upperPredicate <- intLe sym selectorInteger upperInteger
                                            rangePredicate <- andPred sym lowerPredicate upperPredicate
                                            pure [ValueAndStateProduced (SomeBool rangePredicate) state2]
                                        _ -> error "CASE range bounds must be integer expressions"
                                )
                                (\haltedState -> pure [ValueComputationHaltedState haltedState])



evalFunctionCall :: 
    ExprBuilder t st fs
    -> ExecutorFlags
    -> Expression a
    -> [Argument a]
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
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
        parameterIntents = procedureParameterIntents functionDef
    bindValueOutcomes
        (evalMatchedProcedureArguments sym flags parameterIntents matchedArguments callerState)
        (\(evaluatedArguments, callerState1) ->
            execFunctionDefinition
                sym
                flags
                functionName
                functionDef
                evaluatedArguments
                callerState1
        )
        (\haltedState -> pure [ValueComputationHaltedState haltedState])


execFunctionDefinition :: 
    ExprBuilder t st fs
    -> ExecutorFlags 
    -> String 
    -> ProcedureDef a 
    -> [EvaluatedProcedureArgument (ExprBuilder t st fs)]
    -> SymState (ExprBuilder t st fs) a 
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]

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
                        BlStatement _ann _span _label StIntent{} -> True
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
                                (bindProcedureParameters sym flags argumentValues callerState declaredLocalState)
                                (\boundLocalState ->
                                    case executionStatus boundLocalState of
                                        ExecutionHalted _ -> pure [ValueComputationHaltedState (restoreCallerState callerState boundLocalState)]
                                        ExecutionComplete -> do
                                            returnBindingLocalState <-
                                                case maybeReturnTypeSpec of
                                                    Nothing -> pure boundLocalState
                                                    Just returnTypeSpec -> do
                                                        let returnBinding = VarBinding (getVarType returnTypeSpec) Nothing Nothing
                                                        pure boundLocalState { env = Map.insert resultName returnBinding (env boundLocalState) }

                                            bindBranches
                                                (execBlocks sym flags executableBlocks returnBindingLocalState)
                                                (\localState ->
                                                    case executionStatus localState of
                                                        ExecutionHalted _ -> pure [ValueComputationHaltedState (restoreCallerState callerState localState)]
                                                        ExecutionComplete -> do
                                                            returnFunctionResult
                                                                resultName
                                                                argumentValues
                                                                callerState
                                                                localState
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

        returnFunctionResult resultName evaluatedArguments callerState localState =
            case Map.lookup resultName (env localState) of
                Nothing -> error $ "Function result variable is not declared: " ++ resultName

                Just binding ->
                    case varValue binding of
                        Nothing -> error $ "Function result variable is uninitialised: " ++ resultName
                        Just resultValue ->
                            bindBranches
                                (copyProcedureArgumentsBack
                                    sym
                                    flags
                                    evaluatedArguments
                                    localState
                                    ( callerState
                                        { pathCond = pathCond localState
                                        , obligations = obligations localState
                                        , freshCount = freshCount localState
                                        }
                                    )
                                )
                                (\state ->
                                    case executionStatus state of
                                        ExecutionHalted _ ->
                                            pure [ValueComputationHaltedState state]
                                        ExecutionComplete ->
                                            pure [ValueAndStateProduced resultValue state]
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
        parameterIntents = procedureParameterIntents subroutineDef
    bindValueOutcomes
        (evalMatchedProcedureArguments sym flags parameterIntents matchedArguments callerState)
        (\(evaluatedArguments, callerState1) ->
            execSubroutineDefinition
                sym
                flags
                subroutineName
                subroutineDef
                evaluatedArguments
                callerState1
        )
        (\haltedState -> pure [haltedState])



execSubroutineDefinition :: 
    ExprBuilder t st fs 
    -> ExecutorFlags 
    -> String 
    -> ProcedureDef a 
    -> [EvaluatedProcedureArgument (ExprBuilder t st fs)]
    -> SymState (ExprBuilder t st fs) a 
    -> IO [SymState (ExprBuilder t st fs) a]

execSubroutineDefinition sym flags subroutineName subroutineDef argumentValues callerState =
    case subroutineDef of
        SubroutineDef { subroutineBody = body } -> do
            let initialLocalState = callerState { env = Map.empty }

            let (declarationBlocks, executableBlocks) =
                    span 
                    (\block -> case block of
                        BlStatement _ann _span _label StDeclaration{} -> True
                        BlStatement _ann _span _label StImplicit{} -> True
                        BlStatement _ann _span _label StIntent{} -> True
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
                                (bindProcedureParameters sym flags argumentValues callerState declaredLocalState)
                                (\boundLocalState ->
                                    case executionStatus boundLocalState of
                                        ExecutionHalted _ -> pure [restoreCallerState callerState boundLocalState]
                                        ExecutionComplete ->
                                            bindBranches
                                                (execBlocks sym flags executableBlocks boundLocalState)
                                                (\finalLocalState ->
                                                    case executionStatus finalLocalState of
                                                        ExecutionHalted _ -> pure [restoreCallerState callerState finalLocalState]
                                                        ExecutionComplete -> returnSubroutineStates argumentValues callerState finalLocalState
                                                )
                                )
                )

        _ -> error $ "Not a subroutine: " ++ subroutineName

    where
        --don't carry over envs from localState back to callerState
        restoreCallerState callerState localState =
            callerState
                { pathCond = pathCond localState
                , obligations = obligations localState
                , freshCount = freshCount localState
                , executionStatus = executionStatus localState
                }

        returnSubroutineStates evaluatedArguments callerState localState =
            copyProcedureArgumentsBack
                sym
                flags
                evaluatedArguments
                localState
                (callerState
                    { pathCond = pathCond localState
                    , obligations = obligations localState
                    , freshCount = freshCount localState
                    }
                )

