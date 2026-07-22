module EvalExpr where

import Language.Fortran.AST (Expression, TypeSpec)
import What4.Interface (IsSymExprBuilder)

import Types

getVarType :: TypeSpec a -> VarType

evalExpr ::
    IsSymExprBuilder sym =>
    sym ->
    ObligationFlags ->
    Expression a ->
    SymState sym a ->
    IO (SomeExpr sym, SymState sym a)

coerceOnAssignment :: IsSymExprBuilder sym
    => sym
    -> VarType
    -> SomeExpr sym
    -> IO (SomeExpr sym)