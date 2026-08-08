module EvalExpr where

import Language.Fortran.AST (Expression, TypeSpec)
import What4.Interface (IsSymExprBuilder)
import What4.Expr.Builder

import Types

getVarType :: TypeSpec a -> VarType

bindBranches
    :: Monad m
    => m [a]
    -> (a -> m [b])
    -> m [b]

bindValueOutcomes
    :: Monad m
    => m [ValueOutcome sym a]
    -> ((SomeExpr sym, SymState sym a) -> m [b])
    -> (SymState sym a -> m [b])
    -> m [b]

evalExpr :: ExprBuilder t st fs
    -> ExecutorFlags
    -> Expression a
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a]

coerceOnAssignment :: IsSymExprBuilder sym
    => sym
    -> VarType
    -> SomeExpr sym
    -> IO (SomeExpr sym)

coerceArrayOnAssignment :: ExprBuilder t st fs
    -> ExecutorFlags
    -> SomeExpr (ExprBuilder t st fs)
    -> SomeExpr (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a]
