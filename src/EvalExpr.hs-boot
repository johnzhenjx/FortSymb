module EvalExpr where

import Language.Fortran.AST (Expression)
import What4.Interface (IsExprBuilder)

import Types

evalExpr ::
    IsExprBuilder sym =>
    sym ->
    ObligationFlags ->
    Expression a ->
    SymState sym ->
    IO (SomeExpr sym, SymState sym)