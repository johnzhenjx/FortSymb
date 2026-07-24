module EvalExpr where

import qualified Data.Map as Map

import Language.Fortran.AST
import qualified Language.Fortran.AST.Literal.Real as ASTReal

import What4.Interface

import Data.Ratio ((%))

import Prelude hiding (EQ, LT, GT)

import Types
import Arrays
import Procedures
import Executor

getVarType :: TypeSpec a -> VarType
getVarType typeSpec =
    case typeSpecBaseType typeSpec of
        TypeReal -> VarReal
        TypeInteger -> VarInt
        TypeLogical -> VarBool
        _ -> error "Unsupported declaration type"


-- bindEval ::
--     IO [(SomeExpr sym, SymState sym a)] ->
--     (SomeExpr sym -> SymState sym a -> IO [(SomeExpr sym, SymState sym a)]) ->
--     IO [(SomeExpr sym, SymState sym a)]
-- --takes list of eval result tuples, and a continuation function, and performs the function on every tuple in the list, then flattens it?
-- bindEval evaluation continuation = do
--     results <- evaluation

--     nestedResults <-
--         mapM
--             (\(value, state) ->
--                 continuation value state)
--             results

--     pure (concat nestedResults)


bindBranches ::
    IO [(x, SymState sym a)] ->
    (x -> SymState sym a -> IO [(y, SymState sym a)]) ->
    IO [(y, SymState sym a)]
bindBranches computation continuation = do
    results <- computation

    nestedResults <-
        mapM
            (\(value, state) ->
                continuation value state)
            results

    pure (concat nestedResults)


--evaluates AST expressions to What4 symbolic expressions
evalExpr :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> Expression a
    -> SymState sym a
    -> IO [(SomeExpr sym, SymState sym a)]

evalExpr sym flags expr state = 
    case expr of
        ExpValue _ann _span val ->
            evalValue sym val state
        ExpBinary _ann _span op e1 e2 ->  --assumes left to right evaluation
            bindBranches
                (evalExpr sym flags e1 state)
                (\v1 state1 ->
                    bindBranches
                        (evalExpr sym flags e2 state1)
                        (\v2 state2 -> evalBinary sym flags op v1 v2 state2)
                )

        ExpUnary _ann _span op e -> 
            bindBranches
                (evalExpr sym flags e state)
                (\value state1 -> evalUnary sym flags op value state1
                )

        ExpSubscript _ann _span baseExpr indicesInfo -> evalArraySubscript sym flags baseExpr (alistList indicesInfo) state
        -- ExpFunctionCall {} ->
        --     error "Unsupported expression: function call"
        ExpFunctionCall _ann _span functionExpr argumentsInfo ->
            evalFunctionCall sym flags functionExpr (alistList argumentsInfo) state
        _ ->
            error "Unsupported expression in Fortran subset"










evalArraySubscript :: IsSymExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> Expression a 
    -> [Index a] 
    -> SymState sym a 
    -> IO [(SomeExpr sym, SymState sym a)]

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

    indexResults <- evalArrayIndices sym flags indicesExprs state
    mapM
        (\(indices, state1) ->
            lookupSomeArray sym flags arrayExpr indices state1
        )
        indexResults



evalValue :: IsSymExprBuilder sym
    => sym
    -> Value a
    -> SymState sym a
    -> IO [(SomeExpr sym, SymState sym a)]

evalValue sym val state = 
    case val of
        ValVariable name ->
            case Map.lookup name (env state) of
                Nothing -> error ("Variable not declared: " ++ name)
                Just (VarBinding _ Nothing) -> error ("Variable used before initialisation: " ++ name)
                Just (VarBinding _ (Just e)) -> pure [(e, state)]
        ValInteger nStr _kind -> do
            e <- intLit sym (read nStr :: Integer)
            pure [(SomeInt e, state)]
        ValReal rLit _kind -> do
            e <- realLit sym (realAstLitToRational rLit)
            pure [(SomeReal e, state)]
        ValLogical b _kind ->
            if b then pure [(SomeBool (truePred sym), state)]
                else pure [(SomeBool (falsePred sym), state)]
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

                    
evalBinary :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> BinaryOp
    -> SomeExpr sym
    -> SomeExpr sym
    -> SymState sym a
    -> IO [(SomeExpr sym, SymState sym a)]

evalBinary sym flags op v1 v2 state =
    case op of
        Addition -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    z <- intAdd sym x y
                    pure [(SomeInt z, state)]
                (SomeReal x, SomeReal y) -> do
                    z <- realAdd sym x y
                    pure [(SomeReal z, state)]

        Subtraction -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    z <- intSub sym x y
                    pure [(SomeInt z, state)]
                (SomeReal x, SomeReal y) -> do
                    z <- realSub sym x y
                    pure [(SomeReal z, state)]

        Multiplication -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    z <- intMul sym x y
                    pure [(SomeInt z, state)]
                (SomeReal x, SomeReal y) -> do
                    z <- realMul sym x y
                    pure [(SomeReal z, state)]

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
                    pure [(SomeInt z, newState)]

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
                    pure [(SomeReal z, newState)]

        EQ ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- eqPred sym p q
                    pure [(SomeBool r, state)]
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
                    pure [(SomeBool p, state)]

        NE ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- notPred sym =<< eqPred sym p q
                    pure [(SomeBool r, state)]
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
                    pure [(SomeBool p, state)]

        LT -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLt sym x y
                (SomeReal x, SomeReal y) -> realLt sym x y
            pure [(SomeBool p, state)]

        LTE -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLe sym x y
                (SomeReal x, SomeReal y) -> realLe sym x y
            pure [(SomeBool p, state)]

        GT -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLt sym y x
                (SomeReal x, SomeReal y) -> realLt sym y x
            pure [(SomeBool p, state)]

        GTE -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLe sym y x
                (SomeReal x, SomeReal y) -> realLe sym y x
            pure [(SomeBool p, state)]

        And ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- andPred sym p q
                    pure [(SomeBool r, state)]
                _ -> error ".and. requires logical operands"

        Or ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- orPred sym p q
                    pure [(SomeBool r, state)]
                _ -> error ".or. requires logical operands"

        XOr -> do
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- notPred sym =<< eqPred sym p q
                    pure [(SomeBool r, state)]
                _ -> error ".xor. requires logical operands"


        -- skip exponentiated for now

        _ -> error ("Unsupported binary operation: " ++ show op)

            

evalUnary :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> UnaryOp
    -> SomeExpr sym
    -> SymState sym a
    -> IO [(SomeExpr sym, SymState sym a)]

evalUnary sym flags op v state =
    case op of
        Plus ->
            case v of
                SomeInt _ -> pure [(v, state)]
                SomeReal _ -> pure [(v, state)]
                _ -> error "Unary + requires numeric operand"
        Minus ->
            case v of
                SomeInt x -> do
                    r <- intNeg sym x
                    pure [(SomeInt r, state)]
                SomeReal x -> do
                    r <- realNeg sym x
                    pure [(SomeReal r, state)]
                _ -> error "Unary - requires numeric operand"
        Not -> 
            case v of
                SomeBool p -> do
                    q <- notPred sym p
                    pure [(SomeBool q, state)]
                _ ->  error ".not. requires logical operand"

        _ -> error "Unsupported/invalid unary operator"


-- enforce numeric type lifting on binary operations between ints and reals
promoteNumeric :: IsSymExprBuilder sym
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
        
      
coerceOnAssignment :: IsSymExprBuilder sym
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

coerceArrayOnAssignment :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> SomeExpr sym
    -> SomeExpr sym
    -> SymState sym a
    -> IO (SomeExpr sym, SymState sym a)
coerceArrayOnAssignment sym flags targetArray sourceValue state =
    case (targetArray, sourceValue) of
        (SomeIntArray targetRecord, SomeIntArray sourceRecord) ->
            copyArray (SomeIntArray sourceRecord) (arrayDimensions targetRecord) (arrayDimensions sourceRecord)
        (SomeRealArray targetRecord, SomeRealArray sourceRecord) ->
            copyArray (SomeRealArray sourceRecord) (arrayDimensions targetRecord) (arrayDimensions sourceRecord)
        (SomeBoolArray targetRecord, SomeBoolArray sourceRecord) ->
            copyArray (SomeBoolArray sourceRecord) (arrayDimensions targetRecord) (arrayDimensions sourceRecord)

        _ -> error "Whole-array assignment target is not an array"

    where
        copyArray sourceArray targetDims sourceDims = do
            shapePredicate <- arrayShapesEqual sym targetDims sourceDims
            let state1 =
                    if isObligationEnabled flags ArrayShape then
                        let obligation = Obligation
                                { obligationKind = ArrayShape
                                , obligationPredicate = shapePredicate
                                , obligationPath = pathCond state
                                }
                        in state { obligations = obligation : obligations state }
                    else state 
            pure (sourceArray, state1)

        arrayShapesEqual sym targetDims sourceDims =
            case (targetDims, sourceDims) of
                ([], []) -> pure (truePred sym)

                (targetDim : remainingTargets, sourceDim : remainingSources) -> do

                    targetExtent <- dimensionExtent sym targetDim
                    sourceExtent <- dimensionExtent sym sourceDim

                    thisDimensionEqual <- intEq sym targetExtent sourceExtent
                    remainingEqual <- arrayShapesEqual sym remainingTargets remainingSources
                    andPred sym thisDimensionEqual remainingEqual

                _ -> pure (falsePred sym)

            
