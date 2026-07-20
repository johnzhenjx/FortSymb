module Main (main) where

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
import EvalExpr
import Printer
import Solver
import Arrays

import qualified Data.List.NonEmpty as NonEmpty

import Control.Monad (forM_, filterM)

import Data.Char (isSpace)
import Data.List (dropWhileEnd, stripPrefix)


execProgramFile :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> ProgramFile a
    -> IO [SymState sym]
execProgramFile sym flags pf = 
    case programFileProgramUnits pf of
        [pu] -> execProgramUnit sym flags pu
        _  -> error "Only single program unit is supported for now"
        -- fmap concat ( mapM (execProgramUnit sym) (programFileProgramUnits pf) )


execProgramUnit :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> ProgramUnit a
    -> IO [SymState sym]

execProgramUnit sym flags pu =
    case pu of 
        PUMain _ann _span _name blocks _subp -> execBlocks sym flags blocks emptyState
        _ -> error "Bad"


execBlocks :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> [Block a]
    -> SymState sym
    -> IO [SymState sym]

execBlocks sym flags blocks state =
    case blocks of
        [] -> pure [state]
        b:bs -> do
            statesAfterBlock <- execBlock sym flags b state 
                -- ^generate new IO state list after execBlock sym b state
            fmap concat ( mapM (execBlocks sym flags bs) statesAfterBlock )
                -- ^for statesAfterBlock = IO [s1,s2,...], this yields IO [execBlocks sym bs s1, execBlocks sym bs s2, ...]
                --  then flattens overall result to get type IO [SymState sym]


execBlock :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> Block a
    -> SymState sym
    -> IO [SymState sym]

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
    -> SymState sym
    -> IO [SymState sym]

execStatement sym flags statement state = 
    case statement of
        StDeclaration _ann _span typeSpec _attr declsInfo -> do
            newState <- declareVars sym flags typeSpec (alistList declsInfo) state
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


        _ -> error "Unsupported statement type"



--take argument list from preprocessed call, convert to predicate and add to user obligations
execAssertionArguments :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> [Argument a]
    -> SymState sym
    -> IO [SymState sym]
execAssertionArguments sym flags arguments state =
    case arguments of
        [Argument _ann _span Nothing (ArgExpr expr)] -> execAssertionExpr sym flags expr state
        _ ->
            error "fortsymb_assert expects exactly one argument"

execAssertionExpr :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> Expression a
    -> SymState sym
    -> IO [SymState sym]
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


declareVars :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> TypeSpec a
    -> [Declarator a]
    -> SymState sym
    -> IO (SymState sym)

declareVars sym flags typeSpec decls state =
    case decls of
        [] -> pure state
        d:ds -> do
            newState <- declareVar sym flags typeSpec d state 
            declareVars sym flags typeSpec ds newState


declareVar :: IsSymExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> TypeSpec a 
    -> Declarator a 
    -> SymState sym 
    -> IO (SymState sym)
declareVar sym flags typeSpec decl state =
    case declaratorVariable decl of
        ExpValue _ann _span (ValVariable name) ->
            case declaratorType decl of  --need to add "dimension" annotator
                ScalarDecl ->
                    declareScalarVar sym flags typeSpec name (declaratorInitial decl) state
                ArrayDecl dimensionListInfo ->
                    declareArrayVar sym flags typeSpec name dimensionListInfo (declaratorInitial decl) state
        _ -> error "Declaration target is not a variable"


declareScalarVar :: IsExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> TypeSpec a 
    -> VarName 
    -> Maybe (Expression a) 
    -> SymState sym 
    -> IO (SymState sym)
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
    -> VarName
    -> AList DimensionDeclarator a
    -> Maybe (Expression a) 
    -> SymState sym 
    -> IO (SymState sym)

declareArrayVar sym flags typeSpec name dimensionListInfo maybeInitial state = do
    (dimensions, state1) <- evalArrayDimensions sym flags (alistList dimensionListInfo) state
    case maybeInitial of
        Nothing -> do
            arrayValue <- createUninitialisedArray sym name (getVarType typeSpec) dimensions
            pure state1 { env = Map.insert name (VarBinding (getVarType typeSpec) (Just arrayValue)) (env state1) }
        
        Just initExpr ->
            case initExpr of
                ExpInitialisation _ann _span elementsInfo ->  do
                    (arrayValue, state2) <- createArrayFromConstructor sym flags name (getVarType typeSpec) dimensions (alistList elementsInfo) state1
                    pure state2 { env = Map.insert name (VarBinding (getVarType typeSpec) (Just arrayValue)) (env state2) }
                _ -> do --assumed to be constant array init (every element filled with expr)
                    (initValue, state2) <- evalExpr sym flags initExpr state1
                    coercedValue <- coerceOnAssignment sym (getVarType typeSpec) initValue
                    arrayValue <- createConstantArray sym dimensions coercedValue
                    pure state2 { env = Map.insert name (VarBinding (getVarType typeSpec) (Just arrayValue)) (env state2) }



execAssign :: IsSymExprBuilder sym
  => sym
  -> ObligationFlags
  -> Expression a
  -> Expression a
  -> SymState sym
  -> IO (SymState sym)

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
    SymState sym ->
    IO (SymState sym)
execVariableAssign sym flags name rhs state =
    case Map.lookup name (env state) of
        Nothing ->
            error $ "Assignment to undeclared variable: " ++ name

        Just binding ->
            case varValue binding of
                Just SomeIntArray{} -> execWholeArrayAssign sym flags name binding rhs state
                Just SomeRealArray{} -> execWholeArrayAssign sym flags name binding rhs state
                Just SomeBoolArray{} -> execWholeArrayAssign sym flags name binding rhs state
                _ ->  execScalarAssign sym flags name binding rhs state


execScalarAssign :: IsExprBuilder sym
    => sym
    -> ObligationFlags
    -> VarName
    -> VarBinding sym
    -> Expression a
    -> SymState sym
    -> IO (SymState sym)
execScalarAssign sym flags name binding rhs state = do
    (rhsBeforeCoerce, state1) <- evalExpr sym flags rhs state
    rhsAfterCoerce <- coerceOnAssignment sym (varType binding) rhsBeforeCoerce
    pure state1 { env = Map.insert name (VarBinding (varType binding) (Just rhsAfterCoerce)) (env state1) }
                    

-- only supports single element assigns for now
execArrayElementAssign :: IsExprBuilder sym
    => sym
    -> ObligationFlags
    -> Expression a
    -> [Index a]
    -> Expression a
    -> SymState sym
    -> IO (SymState sym)

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
    SymState sym ->
    IO (SymState sym)
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

    case initExpr of
            --explicit assign, e.g. vec = [1,2,3]
            ExpInitialisation _ann _span elementsInfo ->  do
                (arrayValue, state1) <- 
                    createArrayFromConstructor sym flags name (varType binding) dimensions (alistList elementsInfo) state
                pure state1 { env = Map.insert name (VarBinding (varType binding) (Just arrayValue)) (env state1) }
                
            _ -> do
                (initValue, state1) <- evalExpr sym flags initExpr state
                (arrayValue, state2) <-
                    case initValue of
                        SomeIntArray _ -> error "array copy not supported yet due to complicated shape obligations"
                        SomeRealArray _ -> error "array copy not supported yet due to complicated shape obligations"
                        SomeBoolArray _ -> error "array copy not supported yet due to complicated shape obligations"
                        _ -> do --constant array assign (every element filled with expr)
                            coercedValue <- coerceOnAssignment sym (varType binding) initValue
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
    -> SymState sym
    -> IO (SymState sym)

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
    -> SymState sym
    -> IO (SymState sym)

execRead2Vars sym names state =
    case names of
        [] -> pure state
        name:rest -> do
            newState <- execRead2Var sym name state
            execRead2Vars sym rest newState

execRead2Var :: IsSymExprBuilder sym
    => sym
    -> VarName
    -> SymState sym
    -> IO (SymState sym)

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
    -> SymState sym
    -> IO [SymState sym]

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



execIfClauses :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> [(Expression a, [Block a])] --condAndBlocks
    -> Maybe [Block a] --maybeElseBlocks
    -> SymState sym
    -> IO [SymState sym]

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



-- !@assert [predicate]
preprocessAssertions :: String -> String
preprocessAssertions source =
    unlines (map rewriteLine (lines source))
    where
        rewriteLine line =
            case breakAssertionComment line of
                Just (indentation, predicate) ->
                    indentation --keep indentation to preserve scope
                        ++ "call fortsymb_assert("
                        ++ predicate
                        ++ ")"
                Nothing -> line

        breakAssertionComment :: String -> Maybe (String, String)
        breakAssertionComment line =
            let indentation = takeWhile isSpace line
                content = dropWhile isSpace line
            in
                case stripPrefix "!@assert " content of
                    Just predicate ->  Just (indentation, (dropWhileEnd isSpace . dropWhile isSpace) predicate)
                    Nothing -> Nothing



main :: IO ()
main = do
    let filename = "test3.f90"
    contents <- B.readFile filename

    let transformedSource = B.pack (preprocessAssertions (B.unpack contents))

    case byVer Fortran90 filename transformedSource of
        Left err -> do
            putStrLn "Parse error:"
            print err

        Right ast -> do
            putStrLn "Parsed successfully!"
            print ast

            Some nonceGen <- newIONonceGenerator
            sym <- newExprBuilder FloatRealRepr EmptyExprBuilderState nonceGen
            extendConfig z3Options (getConfiguration sym)

            let flags = Map.fromList
                    [ (UserAssertions, True)
                    , (DivByZero, True)
                    , (ArrayBounds, True)
                    , (ArrayShape, True)
                    ]

            allStates <- execProgramFile sym flags ast
            printStates allStates

            feasibleStates <- keepFeasibleStates sym allStates
            printStates feasibleStates

            obligationResults <- evaluateAllStateObligations sym feasibleStates
            printAllObligationResults obligationResults