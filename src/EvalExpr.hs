module EvalExpr where

import qualified Data.Map as Map

import Language.Fortran.AST
import Language.Fortran.Util.Position (SrcSpan)
import qualified Language.Fortran.AST.Literal.Real as ASTReal

import What4.Interface 
import What4.Expr.Builder

import Data.Ratio ((%))

import Prelude hiding (EQ, LT, GT)

import Types
import Arrays
import Designators
import Executor
import SymbolicPath

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


bindBranches
    :: Monad m
    => m [a]
    -> (a -> m [b])
    -> m [b]
bindBranches computation continuation = do
    branches <- computation
    nestedResults <- mapM continuation branches
    pure (concat nestedResults)

bindValueOutcomes
    :: Monad m
    => m [ValueOutcome sym a value]
    -> ((value, SymState sym a) -> m [b])
    -> (SymState sym a -> m [b])
    -> m [b]
bindValueOutcomes computation continuation haltedContinuation =
    bindBranches
        computation
        (\outcome ->
            case outcome of
                ValueAndStateProduced value state ->
                    continuation (value, state)
                ValueComputationHaltedState haltedState ->
                    case executionStatus haltedState of
                        ExecutionHalted _ -> haltedContinuation haltedState
                        ExecutionComplete -> error "Internal error: ValueComputationHaltedState contained an ExecutionComplete state"
        )


--evaluates AST expressions to What4 symbolic expressions
evalExpr :: ExprBuilder t st fs
    -> ExecutorFlags
    -> Expression a
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]

evalExpr sym flags expr state = 
    case expr of
        ExpValue _ann span val -> evalValue sym flags span val state
        ExpBinary _ann span op e1 e2 ->  --assumes left to right evaluation
            bindValueOutcomes
                (evalExpr sym flags e1 state)
                (\(v1, state1) ->
                    bindValueOutcomes
                        (evalExpr sym flags e2 state1)
                        (\(v2, state2) -> evalBinary sym flags span op v1 v2 state2)
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])
                )
                (\haltedState -> pure [ValueComputationHaltedState haltedState])

        ExpUnary _ann _span op e -> 
            bindValueOutcomes
                (evalExpr sym flags e state)
                (\(value, state1) -> evalUnary sym flags op value state1)
                (\haltedState -> pure [ValueComputationHaltedState haltedState])

        ExpSubscript _ann span baseExpr indicesInfo -> evalArraySubscript sym flags span baseExpr (alistList indicesInfo) state
        -- ExpFunctionCall {} ->
        --     error "Unsupported expression: function call"
        ExpFunctionCall _ann _span functionExpr argumentsInfo ->
            evalFunctionCall sym flags functionExpr (alistList argumentsInfo) state
        _ ->
            error "Unsupported expression in Fortran subset"





evalValue :: ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> Value a
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]

evalValue sym _flags span val state =
    case val of
        ValVariable name ->
            case Map.lookup name (env state) of
                Nothing -> error ("Variable not declared: " ++ name)
                Just (VarBinding _ Nothing _) -> do
                    haltedState <- addObligationAndAssume sym UninitialisedRead span (falsePred sym) state
                    pure [ValueComputationHaltedState haltedState]
                Just (VarBinding _ (Just e) _) -> pure [ValueAndStateProduced e state]
        ValInteger nStr _kind -> do
            e <- intLit sym (read nStr :: Integer)
            pure [ValueAndStateProduced (SomeInt e) state]
        ValReal rLit _kind -> do
            e <- realLit sym (realAstLitToRational rLit)
            pure [ValueAndStateProduced (SomeReal e) state]
        ValLogical b _kind ->
            if b then pure [ValueAndStateProduced (SomeBool (truePred sym)) state]
                else pure [ValueAndStateProduced (SomeBool (falsePred sym)) state]
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

                    
evalBinary :: ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> BinaryOp
    -> SomeExpr (ExprBuilder t st fs)
    -> SomeExpr (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]

evalBinary sym _flags span op v1 v2 state =
    case op of
        Addition -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    z <- intAdd sym x y
                    pure [ValueAndStateProduced (SomeInt z) state]
                (SomeReal x, SomeReal y) -> do
                    z <- realAdd sym x y
                    pure [ValueAndStateProduced (SomeReal z) state]

        Subtraction -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    z <- intSub sym x y
                    pure [ValueAndStateProduced (SomeInt z) state]
                (SomeReal x, SomeReal y) -> do
                    z <- realSub sym x y
                    pure [ValueAndStateProduced (SomeReal z) state]

        Multiplication -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    z <- intMul sym x y
                    pure [ValueAndStateProduced (SomeInt z) state]
                (SomeReal x, SomeReal y) -> do
                    z <- realMul sym x y
                    pure [ValueAndStateProduced (SomeReal z) state]

        Division -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            case (v1p, v2p) of
                (SomeInt x, SomeInt y) -> do
                    zero <- intLit sym 0
                    nonZero <- notPred sym =<< intEq sym y zero
                    newState <- addObligationAndAssume sym DivByZero span nonZero state
                    case executionStatus newState of
                        ExecutionHalted _ ->
                            pure [ValueComputationHaltedState newState]
                        ExecutionComplete -> do
                            z <- intDiv sym x y
                            pure [ValueAndStateProduced (SomeInt z) newState]

                (SomeReal x, SomeReal y) -> do
                    zero <- realLit sym 0
                    nonZero <- realNe sym y zero
                    newState <- addObligationAndAssume sym DivByZero span nonZero state
                    case executionStatus newState of
                        ExecutionHalted _ ->
                            pure [ValueComputationHaltedState newState]
                        ExecutionComplete -> do
                            z <- realDiv sym x y
                            pure [ValueAndStateProduced (SomeReal z) newState]

        EQ ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- eqPred sym p q
                    pure [ValueAndStateProduced (SomeBool r) state]
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
                    pure [ValueAndStateProduced (SomeBool p) state]

        NE ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- notPred sym =<< eqPred sym p q
                    pure [ValueAndStateProduced (SomeBool r) state]
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
                    pure [ValueAndStateProduced (SomeBool p) state]

        LT -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLt sym x y
                (SomeReal x, SomeReal y) -> realLt sym x y
            pure [ValueAndStateProduced (SomeBool p) state]

        LTE -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLe sym x y
                (SomeReal x, SomeReal y) -> realLe sym x y
            pure [ValueAndStateProduced (SomeBool p) state]

        GT -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLt sym y x
                (SomeReal x, SomeReal y) -> realLt sym y x
            pure [ValueAndStateProduced (SomeBool p) state]

        GTE -> do
            (v1p, v2p) <- promoteNumeric sym v1 v2
            p <- case (v1p, v2p) of
                (SomeInt  x, SomeInt  y) -> intLe sym y x
                (SomeReal x, SomeReal y) -> realLe sym y x
            pure [ValueAndStateProduced (SomeBool p) state]

        And ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- andPred sym p q
                    pure [ValueAndStateProduced (SomeBool r) state]
                _ -> error ".and. requires logical operands"

        Or ->
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- orPred sym p q
                    pure [ValueAndStateProduced (SomeBool r) state]
                _ -> error ".or. requires logical operands"

        XOr -> do
            case (v1, v2) of
                (SomeBool p, SomeBool q) -> do
                    r <- notPred sym =<< eqPred sym p q
                    pure [ValueAndStateProduced (SomeBool r) state]
                _ -> error ".xor. requires logical operands"


        -- skip exponentiated for now

        _ -> error ("Unsupported binary operation: " ++ show op)

            

evalUnary :: IsSymExprBuilder sym
    => sym
    -> ExecutorFlags
    -> UnaryOp
    -> SomeExpr sym
    -> SymState sym a
    -> IO [ValueOutcome sym a (SomeExpr sym)]

evalUnary sym flags op v state =
    case op of
        Plus ->
            case v of
                SomeInt _ -> pure [ValueAndStateProduced v state]
                SomeReal _ -> pure [ValueAndStateProduced v state]
                _ -> error "Unary + requires numeric operand"
        Minus ->
            case v of
                SomeInt x -> do
                    r <- intNeg sym x
                    pure [ValueAndStateProduced (SomeInt r) state]
                SomeReal x -> do
                    r <- realNeg sym x
                    pure [ValueAndStateProduced (SomeReal r) state]
                _ -> error "Unary - requires numeric operand"
        Not -> 
            case v of
                SomeBool p -> do
                    q <- notPred sym p
                    pure [ValueAndStateProduced (SomeBool q) state]
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

coerceArrayOnAssignment :: ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> SomeExpr (ExprBuilder t st fs)
    -> SomeExpr (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
coerceArrayOnAssignment sym _flags span targetArray sourceValue state =
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
            state1 <- addObligationAndAssume sym ArrayShape span shapePredicate state
            case executionStatus state1 of
                ExecutionHalted _ -> pure [ValueComputationHaltedState state1]
                ExecutionComplete ->
                    pure
                        [ ValueAndStateProduced
                            (preserveTargetDimensions targetDims sourceArray)
                            state1
                        ]

        --without this, copyArray returned the source ArrayRecord directly, which
        --also copied the source dimension onto the target, leading to indexing bugs
        --this was unintended and has been fixed now
        preserveTargetDimensions targetDims sourceArray =
            case sourceArray of
                SomeIntArray record ->
                    SomeIntArray record { arrayDimensions = targetDims }
                SomeRealArray record ->
                    SomeRealArray record { arrayDimensions = targetDims }
                SomeBoolArray record ->
                    SomeBoolArray record { arrayDimensions = targetDims }
                _ -> error "Whole-array assignment source is not an array"

            

evalArraySubscript ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> Expression a
    -> [Index a]
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]

evalArraySubscript sym flags span baseExpr indicesExprs state = do
    bindValueOutcomes
        (evalArrayDesignator sym flags span baseExpr indicesExprs state)
        (\(designator, state1) -> readDesignator sym flags designator state1)
        (\haltedState -> pure [ValueComputationHaltedState haltedState])
