module Executor where

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
         ( ExprBuilder,  FloatModeRepr(..), newExprBuilder
         , BoolExpr, GroundValue, groundEval
		 , EmptyExprBuilderState(..), GroundEvalFn, ExprRangeBindings )

import What4.Config (extendConfig)
import What4.Solver
         (defaultLogData, z3Options, withZ3, SatResult(..))
import What4.Protocol.SMTLib2
         (assume, sessionWriter, runCheckSat)

         
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some

import Data.Ratio ((%))

import Prettyprinter

import Prelude hiding (EQ, LT, GT)

import Types
import {-# SOURCE #-} EvalExpr (getVarType, evalExpr, coerceOnAssignment)
import Printer
import Solver
import Arrays
import Attributes
import Functions

import qualified Data.List.NonEmpty as NonEmpty

import Control.Monad (forM_, filterM, foldM)

import Data.Char (isSpace)
import Data.List (dropWhileEnd, stripPrefix)



execProgramFile :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> ProgramFile a
    -> IO [SymState sym a]
execProgramFile sym flags pf = 
    case programFileProgramUnits pf of
        [pu] -> execProgramUnit sym flags pu
        _  -> error "Only single program unit is supported for now"
        -- fmap concat ( mapM (execProgramUnit sym) (programFileProgramUnits pf) )


execProgramUnit :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> ProgramUnit a
    -> IO [SymState sym a]

execProgramUnit sym flags pu =
    case pu of 
        PUMain _ann _span _name blocks maybeInternalProcedures -> do
            let procedureEnv = buildProcedureEnv (maybe [] id maybeInternalProcedures)
            execBlocks sym flags blocks (emptyState procedureEnv)
        _ -> error "Bad"


execBlocks :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> [Block a]
    -> SymState sym a
    -> IO [SymState sym a]

execBlocks sym flags blocks state =
    case blocks of
        [] -> pure [state]
        b:bs -> do
            statesAfterBlock <- execBlock sym flags b state 
                -- ^generate new IO state list after execBlock sym b state
            fmap concat ( mapM (execBlocks sym flags bs) statesAfterBlock )
                -- ^for statesAfterBlock = IO [s1,s2,...], this yields IO [execBlocks sym bs s1, execBlocks sym bs s2, ...]
                --  then flattens overall result to get type IO [SymState sym a]


execBlock :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> Block a
    -> SymState sym a
    -> IO [SymState sym a]

execBlock sym flags block state = 
    case block of 
        BlStatement _ann _span _label statement -> execStatement sym flags statement state
        --nEcondAndBlocks is a NonEmpty of tuples of cond (Expression) and Block list representing if and else if clauses
        BlIf _ann _span _label _name nEcondAndBlocks maybeElseBlocks _endIfLabel -> 
            execIfClauses sym flags (NonEmpty.toList nEcondAndBlocks) maybeElseBlocks state
        -- BlComment _ann _span comment -> execComment sym flags comment state
        BlComment _ann _span comment -> pure [state]
        -- ...

execStatement :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> Statement a
    -> SymState sym a
    -> IO [SymState sym a]

execStatement sym flags statement state = 
    case statement of
        StDeclaration _ann _span typeSpec maybeAttributesInfo declsInfo -> do
            let attributes = maybe [] alistList maybeAttributesInfo
            newState <- declareVars sym flags typeSpec attributes (alistList declsInfo) state
            pure [newState]
        StExpressionAssign _ann _span lhs rhs -> do
            newState <- execAssign sym flags lhs rhs state
            pure [newState]
        StRead2 _ann _span _format maybeReadList -> do
            newState <- execRead2s sym maybeReadList state --don't include StRead for now
            pure [newState]
        StIfLogical _ann _span cond stmt -> execIfLogical sym flags cond stmt state --one-line if, ie if(cond) stmt
        
        StCall _ann _span procedureExpr argumentsInfo ->
            case procedureExpr of
                ExpValue _ann _span (ValVariable "fortsymb_assert") ->
                    execAssertionArguments sym flags (alistList argumentsInfo) state --assume this will be array of states
                _ -> error "StCall currently unsupported"

        --array allocations only for now, hence specifies Nothings
        StAllocate _ann _span Nothing allocationObjectsInfo Nothing -> do
            newState <- execAllocate sym flags (alistList allocationObjectsInfo) state
            pure [newState]


        StImplicit{} -> pure [state]

        _ -> error "Unsupported statement type"


execAllocate :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> [Expression a]
    -> SymState sym a
    -> IO (SymState sym a)
execAllocate sym flags allocationObjects state = do
    foldM allocateObject state allocationObjects

    where
        allocateObject state allocationObject =
            case allocationObject of
                ExpSubscript _ann _span baseExpr indicesInfo ->
                    case baseExpr of
                        ExpValue _ann _span (ValVariable name) ->
                            allocateArray name (alistList indicesInfo) state
                        _ -> error "Unsupported allocation object"
                _ -> error "Only array allocation is currently supported"

        allocateArray name indicesExpr state =
            case Map.lookup name (env state) of
                Nothing -> error $ "Alloc of undeclared array: " ++ name
                Just binding ->
                    case varType binding of
                        VarArray elementType rank ->
                            case varValue binding of
                                Just _ -> error $ "Array is already allocated: " ++ name
                                Nothing -> do
                                    --allocation object is
                                    -- ExpSubscript
                                    --     ()
                                    --     (3:14)-(3:18)
                                    --     (ExpValue () ... (ValVariable "a"))
                                    --     (AList
                                    --         { alistList =
                                    --             [ IxSingle
                                    --                 ()
                                    --                 (3:16)-(3:17)
                                    --                 Nothing
                                    --                 (ExpValue () ... (ValInteger "10" Nothing))
                                    --               , ...
                                    --             ]
                                    --         }
                                    --     )
                                    -- or IxRange with no stride for lower + upper

                                    (dimensions, state1) <- evalAllocationDimensionsIx sym flags indicesExpr state
                                    if length dimensions /= rank then 
                                        error $ "Allocation rank does not match declaration: " ++ name
                                    else do
                                        arrayExpr <- createUninitialisedArray sym name elementType dimensions
                                        let updatedBinding = binding { varValue = Just arrayExpr }
                                        pure state1 { env = Map.insert name updatedBinding (env state1) }

                        _ -> error $ "Variable is not an array: " ++ name          

        evalAllocationDimensionsIx sym flags indexExprs state =
            case indexExprs of
                [] -> pure ([], state)
                indexExpr : remainingExprs -> do
                    (dimension, state1) <- evalAllocationDimensionIx sym flags indexExpr state
                    (remainingDimensions, finalState) <- evalAllocationDimensionsIx sym flags remainingExprs state1
                    pure ( dimension : remainingDimensions, finalState )
        
        evalAllocationDimensionIx sym flags indexExpr state =
            case indexExpr of
                --upper only
                IxSingle _ann _span _name upperExpr -> do
                    lower <- intLit sym 1

                    (upperValue, state1) <- evalExpr sym flags upperExpr state
                    upper <-
                        case upperValue of
                            SomeInt value -> pure value
                            _ -> error "Allocation upper bound must be an integer"

                    pure ( ArrayDimension { dimensionLower = lower, dimensionUpper = upper }, state1 )

                IxRange _ann _span maybeLowerExpr maybeUpperExpr Nothing -> do
                    (lower, state1) <-
                        case maybeLowerExpr of
                            Nothing -> do
                                defaultLower <- intLit sym 1
                                pure (defaultLower, state)

                            Just lowerExpr -> do
                                (lowerValue, stateAfterLower) <- evalExpr sym flags lowerExpr state
                                case lowerValue of
                                    SomeInt value -> pure (value, stateAfterLower)
                                    _ -> error "Allocation lower bound must be an integer"

                    (upper, state2) <-
                        case maybeUpperExpr of
                            Nothing -> error "Allocation upper bound is required"

                            Just upperExpr -> do
                                (upperValue, stateAfterUpper) <- evalExpr sym flags upperExpr state1
                                case upperValue of
                                    SomeInt value -> pure (value, stateAfterUpper)
                                    _ -> error "Allocation upper bound must be an integer"

                    pure ( ArrayDimension { dimensionLower = lower, dimensionUpper = upper } , state2 )
                
                _ -> error "Unsupported allocation dimension"


declareVars :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> TypeSpec a
    -> [Attribute a]
    -> [Declarator a]
    -> SymState sym a
    -> IO (SymState sym a)

declareVars sym flags typeSpec attributes decls state =
    case decls of
        [] -> pure state
        d:ds -> do
            newState <- declareVar sym flags typeSpec attributes d state 
            declareVars sym flags typeSpec attributes ds newState


declareVar :: IsSymExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> TypeSpec a 
    -> [Attribute a]
    -> Declarator a 
    -> SymState sym a 
    -> IO (SymState sym a)
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


declareScalarVar :: IsSymExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> TypeSpec a 
    -> VarName 
    -> Maybe (Expression a) 
    -> SymState sym a 
    -> IO (SymState sym a)
declareScalarVar sym flags typeSpec name maybeInitial state =
    case maybeInitial of
        Nothing ->
            pure state { env = Map.insert name (VarBinding (getVarType typeSpec) Nothing) (env state) }
        Just initialExpr -> do
            (valueBeforeCoercion, state1) <- evalExpr sym flags initialExpr state
            valueAfterCoercion <- coerceOnAssignment sym (getVarType typeSpec) valueBeforeCoercion
            pure state1 { env = Map.insert name (VarBinding (getVarType typeSpec) (Just valueAfterCoercion)) (env state1) }


--reshape not accepted yet -- scary
declareArrayVar :: IsSymExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> TypeSpec a 
    -> [Attribute a]
    -> VarName
    -> AList DimensionDeclarator a
    -> Maybe (Expression a) 
    -> SymState sym a 
    -> IO (SymState sym a)

declareArrayVar sym flags typeSpec attributes name dimensionListInfo maybeInitial state
    | isAllocatable attributes = pure state { env = Map.insert name (VarBinding arrayType Nothing) (env state) }

    | otherwise = do
        (dimensions, state1) <- evalArrayDimensions sym flags (alistList dimensionListInfo) state
        case maybeInitial of
            Nothing -> do
                arrayValue <- createUninitialisedArray sym name (getVarType typeSpec) dimensions
                pure state1 { env = Map.insert name (VarBinding arrayType (Just arrayValue)) (env state1) }

            Just initExpr ->
                case initExpr of
                    ExpInitialisation _ann _span elementsInfo -> do
                        (arrayValue, state2) <-
                            createArrayFromConstructor
                                sym flags name
                                (getVarType typeSpec)
                                dimensions
                                (alistList elementsInfo)
                                state1
                        pure state2 { env = Map.insert name (VarBinding arrayType (Just arrayValue)) (env state2) }

                    _ -> do
                        (initValue, state2) <- evalExpr sym flags initExpr state1
                        coercedValue <- coerceOnAssignment sym (getVarType typeSpec) initValue
                        arrayValue <- createConstantArray sym dimensions coercedValue
                        pure state2 { env = Map.insert name (VarBinding arrayType (Just arrayValue)) (env state2) }
    where
        arrayType = VarArray (getVarType typeSpec) (length (alistList dimensionListInfo))



execAssign :: IsSymExprBuilder sym
  => sym
  -> ObligationFlags
  -> Expression a
  -> Expression a
  -> SymState sym a
  -> IO (SymState sym a)

execAssign sym flags lhs rhs state =
    case lhs of
        ExpValue _ann _span (ValVariable name) -> 
            execVariableAssign sym flags name rhs state

        ExpSubscript _ann _span baseExpr indicesInfo ->
            execArrayElementAssign sym flags baseExpr (alistList indicesInfo) rhs state


        _ -> error "Left-hand side of assignment must be a variable"


execVariableAssign ::
    IsSymExprBuilder sym =>
    sym ->
    ObligationFlags ->
    VarName ->
    Expression a ->
    SymState sym a ->
    IO (SymState sym a)
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


execScalarAssign :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> VarName
    -> VarBinding sym
    -> Expression a
    -> SymState sym a
    -> IO (SymState sym a)
execScalarAssign sym flags name binding rhs state = do
    (rhsBeforeCoerce, state1) <- evalExpr sym flags rhs state
    rhsAfterCoerce <- coerceOnAssignment sym (varType binding) rhsBeforeCoerce
    pure state1 { env = Map.insert name (VarBinding (varType binding) (Just rhsAfterCoerce)) (env state1) }
                    

-- only supports single element assigns for now
execArrayElementAssign :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> Expression a
    -> [Index a]
    -> Expression a
    -> SymState sym a
    -> IO (SymState sym a)

execArrayElementAssign sym flags baseExpr indexExprs rhs state = do
    name <-
        case baseExpr of
            ExpValue _ann _span (ValVariable arrayName) -> pure arrayName
            _ -> error "Unsupported array assignment target"

    binding <-
        case Map.lookup name (env state) of
            Nothing -> error ("Assignment to undeclared array: " ++ name)
            Just arrayBinding -> pure arrayBinding

    arrayExpr <-
        case varValue binding of
            Nothing -> error ("(wtf): " ++ name)
            Just value -> pure value

    (indices, state1) <- evalArrayIndices sym flags indexExprs state

    (rhsBeforeCoerce, state2) <- evalExpr sym flags rhs state1
    rhsAfterCoerce <- coerceOnAssignment sym (arrayElementType arrayExpr) rhsBeforeCoerce

    (updatedArray, state3) <- updateSomeArray sym flags arrayExpr indices rhsAfterCoerce state2

    pure state3 { env = Map.insert name (binding { varValue = Just updatedArray }) (env state3)}


execWholeArrayAssign ::
    IsSymExprBuilder sym =>
    sym ->
    ObligationFlags ->
    VarName ->
    VarBinding sym ->
    Expression a ->
    SymState sym a ->
    IO (SymState sym a)
execWholeArrayAssign sym flags name binding initExpr state = do
    arrayExpr <-
        case varValue binding of
            Nothing -> error ("(wtf): " ++ name)
            Just value -> pure value

    let dimensions =
            case arrayExpr of
                SomeIntArray rec -> arrayDimensions rec
                SomeRealArray rec -> arrayDimensions rec
                SomeBoolArray rec -> arrayDimensions rec
                _ -> error $ "Expected array expression: " ++ name

        elementType = case varType binding of {VarArray ty _ -> ty ; _ -> error $ "Expected array binding: " ++ name}

    case initExpr of
            --explicit assign, e.g. vec = [1,2,3]
            ExpInitialisation _ann _span elementsInfo ->  do
                (arrayValue, state1) <- 
                    createArrayFromConstructor sym flags name elementType dimensions (alistList elementsInfo) state
                pure state1 { env = Map.insert name (VarBinding (varType binding) (Just arrayValue)) (env state1) }
                
            _ -> do
                (initValue, state1) <- evalExpr sym flags initExpr state
                (arrayValue, state2) <-
                    case initValue of
                        SomeIntArray _ -> error "array copy not supported yet due to complicated shape obligations"
                        SomeRealArray _ -> error "array copy not supported yet due to complicated shape obligations"
                        SomeBoolArray _ -> error "array copy not supported yet due to complicated shape obligations"
                        _ -> do --constant array assign (every element filled with expr)
                            coercedValue <- coerceOnAssignment sym elementType initValue
                            arrayValue <- createConstantArray sym dimensions coercedValue
                            pure (arrayValue, state1)

                pure state2 { env = Map.insert name (VarBinding (varType binding) (Just arrayValue)) (env state2) }

    -- where
    --     copyWholeArray :: SomeExpr sym -> SomeExpr sym -> SomeExpr sym
    --     copyWholeArray destination source =
    --         case (destination, source) of
    --             (SomeIntArray destinationRec, SomeIntArray sourceRec) ->
    --                 SomeIntArray
    --                     destinationRec
    --                         { arrayContents = arrayContents sourceRec
    --                         , arrayInitMask = arrayInitMask sourceRec
    --                         }

    --             (SomeRealArray destinationRec, SomeRealArray sourceRec) ->
    --                 SomeRealArray
    --                     destinationRec
    --                         { arrayContents = arrayContents sourceRec
    --                         , arrayInitMask = arrayInitMask sourceRec
    --                         }

    --             (SomeBoolArray destinationRec, SomeBoolArray sourceRec) ->
    --                 SomeBoolArray
    --                     destinationRec
    --                         { arrayContents = arrayContents sourceRec
    --                         , arrayInitMask = arrayInitMask sourceRec
    --                         }

    --             (SomeIntArray _, _) ->
    --                 error "Expected an integer array"

    --             (SomeRealArray _, _) ->
    --                 error "Expected a real array"

    --             (SomeBoolArray _, _) ->
    --                 error "Expected a logical array"

    --             _ ->
    --                 error "Expected destination array"


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
            let newState = state { env = Map.insert name (VarBinding (varType binding) (Just freshVal)) (env state), freshCount = n+1 }
            pure newState

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



execIfLogical :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> Expression a
    -> Statement a
    -> SymState sym a
    -> IO [SymState sym a]

execIfLogical sym flags cond stmt state = do
    (condVal, state1) <- evalExpr sym flags cond state
    case condVal of
        SomeBool p -> do
            notP <- notPred sym p

            let thenState = state1 { pathCond = p : pathCond state1 }
                elseState = state1 { pathCond = notP : pathCond state1 }

            thenResults <- execStatement sym flags stmt thenState
            pure (thenResults ++ [elseState])

        _ -> error "logical if condition must evaluate to logical"



--take argument list from preprocessed call, convert to predicate and add to user obligations
execAssertionArguments :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> [Argument a]
    -> SymState sym a
    -> IO [SymState sym a]
execAssertionArguments sym flags arguments state =
    case arguments of
        [Argument _ann _span Nothing (ArgExpr expr)] -> execAssertionExpr sym flags expr state
        _ ->
            error "fortsymb_assert expects exactly one argument"

execAssertionExpr :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> Expression a
    -> SymState sym a
    -> IO [SymState sym a]
execAssertionExpr sym flags assertionExpr state = do
    (assertionValue, newState) <- evalExpr sym flags assertionExpr state

    case assertionValue of
        SomeBool predicate -> do
            let obligation = Obligation
                    { obligationKind = UserAssertions
                    , obligationPredicate = predicate
                    , obligationPath = pathCond newState
                    }

                finalState = newState { obligations = obligation : obligations newState }
            pure [finalState]

        _ -> error "Assertion is not a logical predicate"



execIfClauses :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> [(Expression a, [Block a])] --condAndBlocks
    -> Maybe [Block a] --maybeElseBlocks
    -> SymState sym a
    -> IO [SymState sym a]

execIfClauses sym flags condAndBlocks maybeElseBlocks state =
    case condAndBlocks of
        [] ->
            case maybeElseBlocks of
                Nothing -> pure [state]
                Just elseBlocks -> execBlocks sym flags elseBlocks state
        (cond, blocks) : restClauses -> do
            (condVal, state1) <- evalExpr sym flags cond state
            case condVal of
                SomeBool p -> do
                    notP <- notPred sym p

                    let thenState = state1 { pathCond = p : pathCond state1 }
                        elseState = state1 { pathCond = notP : pathCond state1 }

                    thenResults <- execBlocks sym flags blocks thenState
                    restResults <- execIfClauses sym flags restClauses maybeElseBlocks elseState
                    
                    pure (thenResults ++ restResults)

                _ -> error "logical if condition must evaluate to logical"


execFunctionDefinition :: IsSymExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> String 
    -> ProcedureDef a 
    -> [(VarName, SomeExpr sym)] 
    -> SymState sym a 
    -> IO (SomeExpr sym, SymState sym a)

execFunctionDefinition sym flags functionName functionDef argumentValues callerState =
    case functionDef of
        FunctionDef {functionResult = resultName, functionBody = body} -> do
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

            declarationStates <- execBlocks sym flags declarationBlocks initialLocalState

            -- expecting only one resulting state from declaration blocks (no branching)
            declaredLocalState <- case declarationStates of
                [state] -> pure state
                [] -> error $ "Function declarations produced no state: " ++ functionName
                _ -> error $ "Function declarations produced multiple states: " ++ functionName

            -- replace uninitialised dummy parameter bindings
            bindedLocalState <- bindFunctionParameters sym argumentValues declaredLocalState
            finalLocalStates <- execBlocks sym flags executableBlocks bindedLocalState

            case finalLocalStates of
                [finalLocalState] -> returnFunctionResult resultName callerState finalLocalState
                [] -> error $ "Function produced no final state: " ++ functionName
                _ -> error $ "Branching functions are not yet supported: " ++ functionName


        SubroutineDef {} -> do
            error $ "Subroutine used as a function: " ++ functionName


    where
        bindFunctionParameters :: IsSymExprBuilder sym 
            => sym 
            -> [(VarName, SomeExpr sym)] 
            -> SymState sym a 
            -> IO (SymState sym a)
        bindFunctionParameters sym argumentValues initialState =
            go initialState argumentValues
            where
                go state argPairs = case argPairs of
                    [] -> pure state
                    (parameterName, argumentValue) : rest -> do
                        case Map.lookup parameterName (env state) of
                            Nothing -> error $ "Function parameter is not declared: " ++ parameterName
                            Just binding -> do
                                coercedValue <- coerceOnAssignment sym (varType binding) argumentValue
                                let updatedBinding = binding { varValue = Just coercedValue }
                                    state1 = state { env = Map.insert parameterName updatedBinding (env state) }
                                go state1 rest
                                

        returnFunctionResult :: VarName -> SymState sym a -> SymState sym a -> IO (SomeExpr sym, SymState sym a)
        returnFunctionResult resultName callerState localState =
            case Map.lookup resultName (env localState) of
                Nothing -> error $ "Function result variable is not declared: " ++ resultName

                Just binding ->
                    case varValue binding of
                        Nothing -> error $ "Function result variable is uninitialised: " ++ resultName
                        Just resultValue ->
                            --remove env in local scope, but pathCond, freshCount and obligations need to survive
                            pure
                                ( resultValue
                                , callerState
                                    { pathCond = pathCond localState
                                    , obligations = obligations localState
                                    , freshCount = freshCount localState
                                    }
                                )