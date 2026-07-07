module Main (main) where

import qualified Data.ByteString.Char8 as B

import Data.Map (Map)  
import qualified Data.Map as Map

import Language.Fortran.Parser
import Language.Fortran.Version
import Language.Fortran.AST

import What4.Interface
import What4.Expr.Builder

type VarName = String

data SomeExpr sym where
    SomeReal :: SymExpr sym BaseRealType -> SomeExpr sym
    SomeInt  :: SymExpr sym BaseIntegerType -> SomeExpr sym
    SomeBool :: Pred sym -> SomeExpr sym

data SymState sym = SState
    { 
    env :: Map VarName (SomeExpr sym),
    pathCond :: [Pred sym]
    }

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
        PUMain _ _ _ blocks -> execBlocks sym blocks emptyState
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
        [b:bs] -> do
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
        BlStatement _ _ _ statement -> execStatement sym statement state
        


-- type Var = String

-- data SymbType
--     = TInt
--     | TReal
--     | TBool
--     deriving (Eq, Show)

-- data SymbVar = VVar SymbType Var 
--     deriving (Eq, Show)

-- data SymbExpr -- assume entire program is correctly typed; there are other tools to check this
--     = SConst SymbConst
--     | SVar SymbVar
--     | SAdd SymbExpr SymbExpr
--     | SSub SymbExpr SymbExpr
--     | SMul SymbExpr SymbExpr
--     | SDiv SymbExpr SymbExpr
--     deriving (Eq, Show)

-- data SymbConst
--     = CInt Integer
--     | CReal Double --iffy?
--     | CBool Bool
--     deriving (Eq, Show)

-- data SymbBool --iffy?
--     = SBool Bool
--     | SNot SymbBool
--     | SEq SymbExpr SymbExpr
--     | SNeq SymbExpr SymbExpr
--     | SLt SymbExpr SymbExpr
--     | SLeq SymbExpr SymbExpr
--     | SGt SymbExpr SymbExpr
--     | SGeq SymbExpr SymbExpr
--     | SAnd SymbBool SymbBool
--     | SOr SymbBool SymbBool
--     deriving (Eq, Show)

-- data SymbState = SState 
--     { 
--     env :: Map SymbVar SymbExpr,
--     pathCond :: [SymbBool]
--     -- fresh :: Int --counts number of fresh variables introduced by executor
--     }
--     deriving (Eq, Show)

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