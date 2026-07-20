module EvalExpr where

import qualified Data.Map as Map

import Language.Fortran.AST
import qualified Language.Fortran.AST.Literal.Real as ASTReal

import What4.Interface

import Data.Ratio ((%))

import Prelude hiding (EQ, LT, GT)

import Types
import Arrays


getVarType :: TypeSpec a -> VarType
getVarType typeSpec =
    case typeSpecBaseType typeSpec of
        TypeReal -> VarReal
        TypeInteger -> VarInt
        TypeLogical -> VarBool
        _ -> error "Unsupported declaration type"


--evaluates AST expressions to What4 symbolic expressions
evalExpr :: IsExprBuilder sym
    => sym
    -> ObligationFlags
    -> Expression a
    -> SymState sym
    -> IO (SomeExpr sym, SymState sym)

evalExpr sym flags expr state = 
    case expr of
        ExpValue _ann _span val ->
            evalValue sym val state
        ExpBinary _ann _span op e1 e2 -> do --assumes left to right evaluation
            (v1, state1) <- evalExpr sym flags e1 state
            (v2, state2) <- evalExpr sym flags e2 state1
            (result, state3) <- evalBinary sym flags op v1 v2 state2
            pure (result, state3)
        ExpUnary _ann _span op e -> do
            (v, state1) <- evalExpr sym flags e state
            (result, state2) <- evalUnary sym flags op v state1
            pure (result, state2)

        ExpSubscript _ann _span baseExpr indicesInfo -> evalArraySubscript sym flags baseExpr (alistList indicesInfo) state
        ExpFunctionCall {} ->
            error "Unsupported expression: function call"
        _ ->
            error "Unsupported expression in Fortran subset"


evalArraySubscript :: IsExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> Expression a 
    -> [Index a] 
    -> SymState sym 
    -> IO (SomeExpr sym, SymState sym)

evalArraySubscript sym flags baseExpr indicesExprs state = do
    arrayExpr <-
        case baseExpr of
            ExpValue _ann _span (ValVariable name) ->
                case Map.lookup name (env state) of
                    Just binding ->
                        case varValue binding of
                            Just value -> pure value
                            Nothing -> error $ "(wtf): " ++ name
                    Nothing -> error $ "Unknown array variable: " ++ name
            _ ->
                error "Unsupported array base expression"

    (indices, state1) <- evalArrayIndices sym flags indicesExprs state
    lookupSomeArray sym flags arrayExpr indices state1


evalValue :: IsExprBuilder sym
    => sym
    -> Value a
    -> SymState sym
    -> IO (SomeExpr sym, SymState sym)

evalValue sym val state = 
    case val of
        ValVariable name ->
            case Map.lookup name (env state) of
                Nothing -> error ("Variable not declared: " ++ name)
                Just (VarBinding _ Nothing) -> error ("Variable used before initialisation: " ++ name)
                Just (VarBinding _ (Just e)) -> pure (e, state)
        ValInteger nStr _kind -> do
            e <- intLit sym (read nStr :: Integer)
            pure (SomeInt e, state)
        ValReal rLit _kind -> do
            e <- realLit sym (realAstLitToRational rLit)
            pure (SomeReal e, state)
        ValLogical b _kind ->
            if b then pure (SomeBool (truePred sym), state)
                else pure (SomeBool (falsePred sym), state)
        _ ->
            error "Unsupported expression in Fortran subset"


realAstLitToRational :: ASTReal.RealLit -> Rational
realAstLitToRational rLit =
    let sig = decimalStringToRational (ASTReal.realLitSignificand rLit)
        expn = read (ASTReal.exponentNum (ASTReal.realLitExponent rLit)) :: Integer
    in sig * (10 ^^ expn)
    where
        decimalStringToRational s =
            case break (== '.') s of
                (whole, "") ->
                    read whole % 1
                (whole, '.' : frac) ->
                    let (sign, digits) =
                            case whole of
                                ('-':xs) -> (-1, xs)
                                ('+':xs) -> ( 1, xs)
                                xs       -> ( 1, xs)
                        numerator = sign * read (digits ++ frac)
                        denominator = 10 ^ length frac
                    in numerator % denominator

                    
evalBinary :: IsExprBuilder sym
    => sym
    -> ObligationFlags
    -> BinaryOp
    -> SomeExpr sym
    -> SomeExpr sym
    -> SymState sym
    -> IO (SomeExpr sym, SymState sym)

evalBinary sym flags op v1 v2 state =
    case op of
        Addition -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    z <- intAdd sym x y
                    pure (SomeInt z, state)
                (SomeReal x, SomeReal y) -> do
                    z <- realAdd sym x y
                    pure (SomeReal z, state)

        Subtraction -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    z <- intSub sym x y
                    pure (SomeInt z, state)
                (SomeReal x, SomeReal y) -> do
                    z <- realSub sym x y
                    pure (SomeReal z, state)

        Multiplication -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    z <- intMul sym x y
                    pure (SomeInt z, state)
                (SomeReal x, SomeReal y) -> do
                    z <- realMul sym x y
                    pure (SomeReal z, state)

        Division -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    newState <-
                        if isObligationEnabled flags DivByZero then do
                            zero <- intLit sym 0
                            nonZero <- notPred sym =<< intEq sym y zero
                            let obligation = Obligation
                                    { obligationKind = DivByZero
                                    , obligationPredicate = nonZero
                                    , obligationPath = pathCond state
                                    }
                            pure state { obligations = obligation : obligations state }
                        else pure state
                    z <- intDiv sym x y
                    pure (SomeInt z, newState)

                (SomeReal x, SomeReal y) -> do
                    newState <-
                        if isObligationEnabled flags DivByZero then do
                            zero <- realLit sym 0
                            nonZero <- realNe sym y zero
                            let obligation = Obligation
                                    { obligationKind = DivByZero
                                    , obligationPredicate = nonZero
                                    , obligationPath = pathCond state
                                    }
                            pure state { obligations = obligation : obligations state }
                        else pure state
                    z <- realDiv sym x y
                    pure (SomeReal z, newState)

        EQ ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- eqPred sym p q
                    pure (SomeBool r, state)
                (SomeInt _,  SomeInt _)  -> numericEq
                (SomeInt _,  SomeReal _) -> numericEq
                (SomeReal _, SomeInt _)  -> numericEq
                (SomeReal _, SomeReal _) -> numericEq
                _ -> error "type error"
            where
                numericEq = do
                    (v1p, v2p) <- promoteNumeric sym v1 v2
                    p <- case (v1p, v2p) of
                        (SomeInt  x, SomeInt  y)   -> intEq sym x y
                        (SomeReal x, SomeReal y)   -> realEq sym x y
                    pure (SomeBool p, state)

        NE ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- notPred sym =<< eqPred sym p q
                    pure (SomeBool r, state)
                (SomeInt _,  SomeInt _)  -> numericNe
                (SomeInt _,  SomeReal _) -> numericNe
                (SomeReal _, SomeInt _)  -> numericNe
                (SomeReal _, SomeReal _) -> numericNe
                _ -> error "type error"
            where
                numericNe = do
                    (v1p, v2p) <- promoteNumeric sym v1 v2
                    p <- case (v1p, v2p) of
                        (SomeInt  x, SomeInt y) -> notPred sym =<< intEq sym x y
                        (SomeReal x, SomeReal y) -> realNe sym x y
                    pure (SomeBool p, state)

        LT -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLt sym x y
                (SomeReal x, SomeReal y) -> realLt sym x y
            pure (SomeBool p, state)

        LTE -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLe sym x y
                (SomeReal x, SomeReal y) -> realLe sym x y
            pure (SomeBool p, state)

        GT -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLt sym y x
                (SomeReal x, SomeReal y) -> realLt sym y x
            pure (SomeBool p, state)

        GTE -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLe sym y x
                (SomeReal x, SomeReal y) -> realLe sym y x
            pure (SomeBool p, state)

        And ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- andPred sym p q
                    pure (SomeBool r, state)
                _ -> error ".and. requires logical operands"

        Or ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- orPred sym p q
                    pure (SomeBool r, state)
                _ -> error ".or. requires logical operands"

        XOr -> do
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- notPred sym =<< eqPred sym p q
                    pure (SomeBool r, state)
                _ -> error ".xor. requires logical operands"


        -- skip exponentiated for now

        _ -> error ("Unsupported binary operation: " ++ show op)

            

evalUnary sym flags op v state =
    case op of
        Plus ->
            case v of
                SomeInt _ -> pure (v, state)
                SomeReal _ -> pure (v, state)
                _ -> error "Unary + requires numeric operand"
        Minus ->
            case v of
                SomeInt x -> do
                    r <- intNeg sym x
                    pure (SomeInt r, state)
                SomeReal x -> do
                    r <- realNeg sym x
                    pure (SomeReal r, state)
                _ -> error "Unary - requires numeric operand"
        Not -> 
            case v of
                SomeBool p -> do
                    q <- notPred sym p
                    pure (SomeBool q, state)
                _ ->  error ".not. requires logical operand"


-- enforce numeric type lifting on binary operations between ints and reals
promoteNumeric :: IsExprBuilder sym
    => sym
    -> SomeExpr sym
    -> SomeExpr sym
    -> IO (SomeExpr sym, SomeExpr sym)
promoteNumeric sym v1 v2 =
    case (v1, v2) of
        (SomeInt _, SomeInt _) ->
            pure (v1, v2)
        (SomeReal _, SomeReal _) ->
            pure (v1, v2)
        (SomeInt x, SomeReal y) -> do
            x' <- integerToReal sym x
            pure (SomeReal x', SomeReal y)
        (SomeReal x, SomeInt y) -> do
            y' <- integerToReal sym y
            pure (SomeReal x, SomeReal y')
        _ -> error "Non-numeric terms in arithmetic operation"
        
      
coerceOnAssignment :: IsExprBuilder sym
    => sym
    -> VarType
    -> SomeExpr sym
    -> IO (SomeExpr sym)

coerceOnAssignment sym targetType rhs =
    case (targetType, rhs) of
        (VarInt, SomeInt _) -> pure rhs
        (VarReal, SomeReal _) -> pure rhs
        -- integers can be assigned to reals
        (VarReal, SomeInt x) -> do
            xR <- integerToReal sym x
            pure (SomeReal xR)
        -- must floor reals stored into ints
        (VarInt, SomeReal x) -> do
            xI <- realFloor sym x
            pure (SomeInt xI)
        (VarBool, SomeBool _) ->
            pure rhs
        _ -> error "Bad assignment"

