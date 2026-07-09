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
		 , EmptyExprBuilderState(..) )
         
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some

import Data.Ratio ((%))

import Prettyprinter

import Prelude hiding (EQ, LT, GT)

import Types
import EvalExpr
import Printer


execProgramFile :: IsSymExprBuilder sym
    => sym
    -> ProgramFile a
    -> IO [SymState sym]
execProgramFile sym pf = 
    case programFileProgramUnits pf of
        [pu] -> execProgramUnit sym pu
        _  -> error "Only single program unit is supported for now"
        -- fmap concat ( mapM (execProgramUnit sym) (programFileProgramUnits pf) )


execProgramUnit :: IsSymExprBuilder sym
    => sym
    -> ProgramUnit a
    -> IO [SymState sym]

execProgramUnit sym pu =
    case pu of 
        PUMain _ann _span _name blocks _subp -> execBlocks sym blocks emptyState
        _ -> error "Bad"


execBlocks :: IsSymExprBuilder sym
    => sym
    -> [Block a]
    -> SymState sym
    -> IO [SymState sym]

execBlocks sym blocks state =
    case blocks of
        [] -> pure [state]
        b:bs -> do
            statesAfterBlock <- execBlock sym b state 
                -- ^generate new IO state list after execBlock sym b state
            fmap concat ( mapM (execBlocks sym bs) statesAfterBlock )
                -- ^for statesAfterBlock = IO [s1,s2,...], this yields IO [execBlocks sym bs s1, execBlocks sym bs s2, ...]
                --  then flattens overall result to get type IO [SymState sym]


execBlock :: IsSymExprBuilder sym
    => sym
    -> Block a
    -> SymState sym
    -> IO [SymState sym]

execBlock sym block state = 
    case block of 
        BlStatement _ann _span _label statement -> execStatement sym statement state
        -- ...


execStatement :: IsSymExprBuilder sym
    => sym
    -> Statement a
    -> SymState sym
    -> IO [SymState sym]

execStatement sym statement state = 
    case statement of
        StDeclaration _ann _span typeSpec _attr declsInfo -> do
            newState <- declareVars sym typeSpec (alistList declsInfo) state
            pure [newState]
        StExpressionAssign _ann _span lhs rhs -> do
            newState <- execAssign sym lhs rhs state
            pure [newState]
        StRead2 _ann _span _format maybeReadList -> do
            newState <- execRead2s sym maybeReadList state --don't include StRead for now
            pure [newState]
        StIfLogical _ann _span cond stmt -> execIfLogical sym cond stmt state --one-line if, ie if(cond) stmt
        _ -> error "Unsupported statement type"


execIfLogical :: IsSymExprBuilder sym
    => sym
    -> Expression a
    -> Statement a
    -> SymState sym
    -> IO [SymState sym]

execIfLogical sym cond stmt state = do
    condVal <- evalExpr sym cond state
    case condVal of
        SomeBool p -> do
            notP <- notPred sym p

            let thenState = state { pathCond = p : pathCond state }
                elseState = state { pathCond = notP : pathCond state }

            thenResults <- execStatement sym stmt thenState
            pure (thenResults ++ [elseState])

        _ -> error "logical if condition must evaluate to logical"


declareVars :: IsExprBuilder sym
    => sym
    -> TypeSpec a
    -> [Declarator a]
    -> SymState sym
    -> IO (SymState sym)

declareVars sym typeSpec decls state =
    case decls of
        [] -> pure state
        d:ds -> do
            newState <- declareVar sym typeSpec d state 
            declareVars sym typeSpec ds newState

declareVar :: IsExprBuilder sym
    => sym
    -> TypeSpec a
    -> Declarator a
    -> SymState sym
    -> IO (SymState sym)

declareVar sym typeSpec decl state =
    -- only scalar type for now
    case declaratorVariable decl of
        ExpValue _ann _span (ValVariable name) ->
            case declaratorInitial decl of
                Nothing -> do
                    let newState = state { env = Map.insert name (VBinding (getVarType typeSpec) Nothing) (env state) }
                    pure newState
                Just initExpr -> do
                    rhsBeforeCoerce <- evalExpr sym initExpr state 
                    rhsAfterCoerce <- coerceOnAssignment sym (getVarType typeSpec) rhsBeforeCoerce
                    let newState = state { env = Map.insert name (VBinding (getVarType typeSpec) (Just rhsAfterCoerce)) (env state) }
                    pure newState
        _ -> error "Bad"   



execAssign :: IsExprBuilder sym
  => sym
  -> Expression a
  -> Expression a
  -> SymState sym
  -> IO (SymState sym)

execAssign sym lhs rhs state =
    case lhs of
        ExpValue _ann _span (ValVariable name) -> do
            rhsBeforeCoerce <- evalExpr sym rhs state
            case Map.lookup name (env state) of
                Nothing -> error ("Assignment to undeclared variable: " ++ name)
                Just binding -> do
                    rhsAfterCoerce <- coerceOnAssignment sym (varType binding) rhsBeforeCoerce
                    let newState = state { env = Map.insert name (VBinding (varType binding) (Just rhsAfterCoerce)) (env state) }
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

            states <- execProgramFile sym ast
            printStates states