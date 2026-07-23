module EvalExpr where

import Language.Fortran.AST (Expression, TypeSpec)
import What4.Interface (IsSymExprBuilder)

import Types

getVarType :: TypeSpec a -> VarType

bindBranches ::
    IO [(x, SymState sym a)] ->
    (x -> SymState sym a -> IO [(y, SymState sym a)]) ->
    IO [(y, SymState sym a)]
    
evalExpr ::
    IsSymExprBuilder sym =>
    sym ->
    ObligationFlags ->
    Expression a ->
    SymState sym a ->
    IO [(SomeExpr sym, SymState sym a)]

coerceOnAssignment :: IsSymExprBuilder sym
    => sym
    -> VarType
    -> SomeExpr sym
    -> IO (SomeExpr sym)