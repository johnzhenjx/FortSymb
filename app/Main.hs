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

import qualified Data.List.NonEmpty as NonEmpty

import Control.Monad (filterM)

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
        BlComment _ann _span comment -> execComment sym flags comment state
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
        _ -> error "Unsupported statement type"



declareVars :: IsExprBuilder sym
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

declareVar :: IsExprBuilder sym
    => sym
    -> ObligationFlags
    -> TypeSpec a
    -> Declarator a
    -> SymState sym
    -> IO (SymState sym)

declareVar sym flags typeSpec decl state =
    -- only scalar type for now
    case declaratorVariable decl of
        ExpValue _ann _span (ValVariable name) ->
            case declaratorInitial decl of
                Nothing -> do
                    let newState = state { env = Map.insert name (VBinding (getVarType typeSpec) Nothing) (env state) }
                    pure newState
                Just initExpr -> do
                    (rhsBeforeCoerce, state1) <- evalExpr sym flags initExpr state
                    rhsAfterCoerce <- coerceOnAssignment sym (getVarType typeSpec) rhsBeforeCoerce
                    let newState = state1 { env = Map.insert name (VBinding (getVarType typeSpec) (Just rhsAfterCoerce)) (env state1) }
                    pure newState
        _ -> error "Bad"   



execAssign :: IsExprBuilder sym
  => sym
  -> ObligationFlags
  -> Expression a
  -> Expression a
  -> SymState sym
  -> IO (SymState sym)

execAssign sym flags lhs rhs state =
    case lhs of
        ExpValue _ann _span (ValVariable name) -> do
            (rhsBeforeCoerce, state1) <- evalExpr sym flags rhs state
            case Map.lookup name (env state1) of
                Nothing -> error ("Assignment to undeclared variable: " ++ name)
                Just binding -> do
                    rhsAfterCoerce <- coerceOnAssignment sym (varType binding) rhsBeforeCoerce
                    let newState = state1 { env = Map.insert name (VBinding (varType binding) (Just rhsAfterCoerce)) (env state1) }
                    pure newState
        _ -> error "Left-hand side of assignment must be a variable"



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
            let newState = state { env = Map.insert name (VBinding (varType binding) (Just freshVal)) (env state), freshCount = n+1 }
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
execComment ::
    IsSymExprBuilder sym =>
    sym ->
    ObligationFlags ->
    Comment a ->
    SymState sym ->
    IO [SymState sym]
execComment sym flags (Comment rawComment) state =
    case stripPrefix "@assert " (trim rawComment) of
        Just stmtString
            | isObligationEnabled flags UserAssertions -> execAssertionString sym flags (trim stmtString) state
            | otherwise -> pure [state]
        Nothing -> pure [state]
    where
        trim = dropWhileEnd isSpace . dropWhile isSpace


execAssertionString ::
    IsSymExprBuilder sym =>
    sym ->
    ObligationFlags ->
    String ->
    SymState sym ->
    IO [SymState sym]
execAssertionString sym flags assertionString state = do
    let assertionExpr = parseAssertionExpression assertionString

    (assertionValue, newState) <- evalExpr sym flags assertionExpr state

    case assertionValue of
        SomeBool predicate -> do
            let obligation =
                Obligation
                    { obligationKind = UserAssertions
                    , obligationPredicate = predicate
                    , obligationPath = pathCond newState
                    }
            finalState = newState { obligations = obligation : obligations newState }
            pure [finalState]

        _ -> error "Assertion is not a logical predicate: " ++ assertionString


parseAssertionExpression :: String -> Expression ()
parseAssertionExpression assertionString =
    case byVer Fortran90 "<assertion>" (B.pack assertionProgram) of
        Left parseError ->
            error "Invalid Fortran assertion:\n" ++ assertionString ++ "\n" ++ show parseError
        Right programFile -> extractAssertionExpression programFile
  where
    assertionProgram =
        unlines
            [ "program assertion"
            , "  if (" ++ assertionString ++ ") continue"
            , "end program assertion"
            ]

extractAssertionExpression :: ProgramFile () -> Expression ()
extractAssertionExpression programFile =
    case programFileProgramUnits programFile of
        [PUMain _ann _span _name blocks _subprograms] ->
            findAssertion blocks
        [] -> error "Generated assertion program contains no program unit"
        _ -> error "Generated assertion program has an unexpected structure"
    where
        findAssertion :: [Block ()] -> Expression ()
        findAssertion [] = error "Could not find generated assertion statement"
        findAssertion (block : remainingBlocks) =
            case block of
                BlStatement _ann _span _label statement ->
                    case statement of
                        StIfLogical _ann _span assertionExpr _body ->  assertionExpr
                        _ -> findAssertion remainingBlocks
                _ -> findAssertion remainingBlocks



--converts list of What4 predicates into conjunction of predicates
predicateOfCondList :: IsExprBuilder sym
    => sym
    -> [Pred sym]
    -> IO (Pred sym)
predicateOfCondList sym pathCond = recurseConj pathCond
    where
        recurseConj [] = pure(truePred sym)
        recurseConj (p:ps) = do
            rest <- recurseConj ps
            andPred sym p rest

checkStateFeasibility ::
    ExprBuilder t st fs ->
    SymState (ExprBuilder t st fs) ->
    IO (Maybe (GroundEvalFn t))
checkStateFeasibility sym state = do
    pathPred <- predicateOfCondList sym (pathCond state)
    solverResult <- invokeSolver sym pathPred
    case solverResult of
        Sat (ge, _) -> pure (Just ge) --for now
        Unsat _ -> pure (Nothing)
        Unknown -> error "Solver failed to find a solution."

--has a logger attached for now (bad but oh well)
keepFeasibleStates ::
    ExprBuilder t st fs ->
    [SymState (ExprBuilder t st fs)] ->
    IO [SymState (ExprBuilder t st fs)]
keepFeasibleStates sym states = do
    numberedResults <- filterM isFeasible (zip [(1 :: Int)..] states)
    pure (map snd numberedResults)
    where
        isFeasible (i, state) = do
            result <- checkStateFeasibility sym state
            case result of
                Just _ -> do
                    putStrLn $ show i ++ ". Satisfiable pathCond"
                    pure True
                Nothing -> do
                    putStrLn $ show i ++ ". Unsatisfiable pathCond"
                    pure False


-- checkStateAssertionsValidity ::
--     ExprBuilder t st fs ->
--     SymState (ExprBuilder t st fs) ->
--     Pred (ExprBuilder t st fs) ->
--     IO (Maybe (GroundEvalFn t))

-- checkStateAssertionsValidity sym state = do 
--     pathPred <- predicateOfCondList sym (pathCond state)
--     assertionPred <- predicateOfCondList sym (assertions state)
--     negAssertionPred <- notPred sym assertionPred
--     failurePred <- andPred sym pathPred negAssertionPred --pathPred and not assertionPred, assertions are valid if this is unsat
    
--     solverResult <- invokeSolver sym failurePred
--     case solverResult of
--         Sat (ge, _) -> pure (Just ge) --not valid, ge for counterexample
--         Unsat _ -> pure Nothing
--         Unknown -> error "Solver failed to determine assertion validity."



z3exe :: FilePath
z3exe = "z3-4.8.12-x86-win/bin/z3.exe"

invokeSolver ::
    ExprBuilder t st fs ->
    BoolExpr t ->
    IO (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) ())
invokeSolver sym f = do
    withZ3 sym z3exe defaultLogData $ \session -> do
        assume (sessionWriter session) f
        runCheckSat session $ \result -> pure result




main :: IO ()
main = do
    let filename = "test3.f90"
    contents <- B.readFile filename

    case byVer Fortran90 filename contents of
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
                    ]

            allStates <- execProgramFile sym flags ast
            printStates allStates

            feasibleStates <- keepFeasibleStates sym allStates
            printStates feasibleStates