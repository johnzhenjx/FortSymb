module EvalExpr where

import Language.Fortran.AST (Expression, TypeSpec)
import Language.Fortran.Util.Position (SrcSpan)
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
    => m [ValueOutcome sym a value]
    -> ((value, SymState sym a) -> m [b])
    -> (SymState sym a -> m [b])
    -> m [b]

evalExpr :: ExprBuilder t st fs
    -> ExecutorFlags
    -> Expression a
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]

coerceOnAssignment :: IsSymExprBuilder sym
    => sym
    -> VarType
    -> SomeExpr sym
    -> IO (SomeExpr sym)

coerceArrayOnAssignment :: ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> SomeExpr (ExprBuilder t st fs)
    -> SomeExpr (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
