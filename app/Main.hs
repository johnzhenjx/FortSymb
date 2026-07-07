module Main (main) where

import qualified Data.ByteString.Char8 as B

import Data.Map (Map)  
import qualified Data.Map as Map

import Language.Fortran.Parser
import Language.Fortran.Version
import Language.Fortran.AST

import What4.Interface
import What4.BaseTypes
import What4.Expr.Builder

type VarName = String

data SomeExpr sym where
    SomeReal :: SymExpr sym BaseRealType -> SomeExpr sym
    SomeInt  :: SymExpr sym BaseIntegerType -> SomeExpr sym
    SomeBool :: Pred sym -> SomeExpr sym

data VarType
    = VarReal
    | VarInt
    | VarBool

data VarBinding sym = VBinding
    { 
    varType :: VarType,
    varValue :: Maybe (SomeExpr sym)
    }


data SymState sym = SState
    { 
    env :: Map VarName (VarBinding sym),
    pathCond :: [Pred sym]
    }

-- x ↦ VarBinding VarReal Nothing
-- y ↦ VarBinding VarReal (Just (SomeReal yExpr))
-- i ↦ VarBinding VarInt  Nothing
-- b ↦ VarBinding VarBool (Just (SomeBool bExpr))

emptyState :: SymState sym
emptyState = SState
    { 
    env = Map.empty,
    pathCond = []
    }


execProgramUnit :: 
    IsExprBuilder sym
    => sym
    -> ProgramUnit a
    -> IO [SymState sym]

execProgramUnit sym pu =
    case pu of 
        PUMain _ann _span _name blocks -> execBlocks sym blocks emptyState
        _ -> error "Bad"


execBlocks :: 
    IsExprBuilder sym
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


execBlock :: 
    IsExprBuilder sym
    => sym
    -> Block a
    -> SymState sym
    -> IO [SymState sym]

execBlock sym block state = 
    case block of 
        BlStatement _ann _span _label statement -> do
            singularSt <- execStatement sym statement state
            pure [singularSt]
        -- ...


execStatement :: IsExprBuilder sym
    => sym
    -> Statement a
    -> SymState sym
    -> IO (SymState sym)

execStatement sym statement state = 
    case statement of
        StDeclaration _ann _span typeSpec _attr declsInfo -> declareVars sym typeSpec state (alistList declsInfo)


declareVars :: IsExprBuilder sym
    => sym
    -> TypeSpec a
    -> SymState sym
    -> [Declarator a]
    -> IO (SymState sym)

declareVars sym typeSpec state decls =
    case decls of
        [] -> pure state
        d:ds -> do
            newState <- declareVar sym typeSpec state d
            declareVars sym typeSpec newState ds

declareVar :: IsExprBuilder sym
    => sym
    -> TypeSpec a
    -> SymState sym
    -> Declarator a
    -> IO (SymState sym)
  
declareVar sym typeSpec state decl =
    -- only scalar type for now
    case declaratorVariable decl of
        ExpValue _ann _span (ValVariable name) ->
            case declaratorInitial decl of
                Nothing -> do
                    let newState = state { env = Map.insert name (VBinding (getVarType typeSpec) Nothing) (env state) }
                    pure newState
                Just initExpr -> do
                    -- evaluate initExpr to get SomeExpr sym
                    -- for now, we will just insert Uninit for simplicity
                    let newState = state { env = Map.insert name (VBinding (getVarType typeSpec) Nothing) (env state) }
                    -- let newState = state { env = Map.insert name (VBinding (getVarType typeSpec) (Just initExpr)) (env state) }
                    pure newState
        _ -> error "Bad"   

getVarType :: TypeSpec a -> VarType
getVarType typeSpec =
    case typeSpecBaseType typeSpec of
        TypeReal -> VarReal
        TypeInteger -> VarInt
        TypeLogical -> VarBool
        _ -> error "Unsupported declaration type"



main :: IO ()
main = do
    let filename = "test0.f90"
    contents <- B.readFile "test0.f90"
    case byVer Fortran90 filename contents of
        Left err -> do
            putStrLn "Parse error:"
            print err

        Right ast -> do
            putStrLn "Parsed successfully!"
            -- print ast