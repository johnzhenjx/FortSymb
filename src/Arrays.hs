module Arrays
  ( arrayElementType
  , dimensionOffset
  , dimensionExtent
  , arrayIndexInBounds
  , arrayIndicesInBounds
  , flattenArrayIndices
  , unflattenArrayIndex
  , evalArrayIndices
  , evalArrayDimensions
  , evalArrayDimension
  , createUninitialisedArray
  , createConstantArray
  , createArrayFromConstructor
  , lookupSomeArray
  , updateSomeArray
  ) where

import Types
import {-# SOURCE #-} EvalExpr (evalExpr, coerceOnAssignment)

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Parameterized.Context as Ctx

import What4.BaseTypes
import What4.Interface
import What4.Symbol

import Language.Fortran.AST

import What4.Expr
  ( ExprBuilder
  , FloatModeRepr(..)
  , newExprBuilder
  , BoolExpr
  , GroundValue
  , groundEval
  , EmptyExprBuilderState(..)
  , GroundEvalFn
  , ExprRangeBindings
  )

import What4.Expr.Builder


arrayElementType :: SomeExpr sym -> VarType
arrayElementType arrayExpr =
    case arrayExpr of
        SomeIntArray _ -> VarInt
        SomeRealArray _ -> VarReal
        SomeBoolArray _ -> VarBool
        _ -> error "arrayElementType expected an array"

dimensionOffset :: IsExprBuilder sym 
    => sym 
    -> ArrayDimension sym 
    -> SymExpr sym BaseIntegerType 
    -> IO (SymExpr sym BaseIntegerType)
dimensionOffset sym dimension index = intSub sym index (dimensionLower dimension)

--upper - lower + 1, symbolically
dimensionExtent :: IsExprBuilder sym 
    => sym 
    -> ArrayDimension sym 
    -> IO (SymExpr sym BaseIntegerType)
dimensionExtent sym dimension = do
    difference <- intSub sym (dimensionUpper dimension) (dimensionLower dimension)
    one <- intLit sym 1
    intAdd sym difference one


--one dimension, one index
arrayIndexInBounds :: IsExprBuilder sym 
    => sym 
    -> ArrayDimension sym 
    -> SymExpr sym BaseIntegerType 
    -> IO (Pred sym)
arrayIndexInBounds sym dimension index = do
    aboveLower <- intLe sym (dimensionLower dimension) index
    belowUpper <- intLe sym index (dimensionUpper dimension)
    andPred sym aboveLower belowUpper


-- andPreds across all dimensions and indices
arrayIndicesInBounds :: IsExprBuilder sym 
    => sym 
    -> [ArrayDimension sym] 
    -> [SymExpr sym BaseIntegerType] 
    -> IO (Pred sym)
arrayIndicesInBounds sym dimensions indices =
    case (dimensions, indices) of
        ([], []) -> pure (truePred sym)
        (dimension : remainingDimensions, index : remainingIndices) -> do
            currentPred <- arrayIndexInBounds sym dimension index
            remainingPred <- arrayIndicesInBounds sym remainingDimensions remainingIndices
            andPred sym currentPred remainingPred
        _ -> error "Array rank mismatch"
                

--symbolic flat=(i1​−L1​)+N1​((i2​−L2​)+N2​((i3​−L3​)+⋯)).
flattenArrayIndices :: IsExprBuilder sym 
    => sym 
    -> [ArrayDimension sym] 
    -> [SymExpr sym BaseIntegerType] 
    -> IO (SymExpr sym BaseIntegerType)
flattenArrayIndices sym dimensions indices =
    case (dimensions, indices) of
        ([],[]) -> intLit sym 0
        (dimension : remainingDimensions, index : remainingIndices) -> do
            thisRank <- dimensionOffset sym dimension index
            otherRanks <- flattenArrayIndices sym remainingDimensions remainingIndices
            extent <- dimensionExtent sym dimension
            intAdd sym thisRank =<< intMul sym otherRanks extent
        _ -> error "Array rank mismatch"



unflattenArrayIndex :: IsExprBuilder sym
    => sym
    -> [ArrayDimension sym]
    -> SymExpr sym BaseIntegerType
    -> IO [SymExpr sym BaseIntegerType]
unflattenArrayIndex sym dimensions flatIndex =
    go dimensions flatIndex
    where
        go [] _ = pure []
        go (dimension : remainingDimensions) remainingFlatIndex = do
            extent <- dimensionExtent sym dimension
            offset <- intMod sym remainingFlatIndex extent
            nextFlatIndex <- intDiv sym remainingFlatIndex extent
            index <- intAdd sym (dimensionLower dimension) offset
            remainingIndices <- go remainingDimensions nextFlatIndex
            pure (index : remainingIndices)



evalArrayDimensions ::
    IsExprBuilder sym =>
    sym ->
    ObligationFlags ->
    [DimensionDeclarator a] ->
    SymState sym ->
    IO ([ArrayDimension sym], SymState sym)
evalArrayDimensions sym flags dimensionDecls state = 
    case dimensionDecls of
        [] -> pure ([], state)
        decl : decls -> do
            (dimension, state1) <- evalArrayDimension sym flags decl state
            (dimensions, state2) <- evalArrayDimensions sym flags decls state1
            pure (dimension : dimensions, state2)


--assume all array sizes known for now
evalArrayDimension :: IsExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> DimensionDeclarator a 
    -> SymState sym 
    -> IO (ArrayDimension sym, SymState sym)
evalArrayDimension sym flags dimensionDecl state = do
    (lowerBound, state1) <-
        case dimDeclLower dimensionDecl of
            Nothing -> do
                defaultLower <- intLit sym 1
                pure (defaultLower, state)
            Just lowerExpr -> do
                (boundValue, state1) <- evalExpr sym flags lowerExpr state
                case boundValue of
                    SomeInt integerExpr -> pure (integerExpr, state1)
                    _ -> error "Array lower bound must be an integer expression"

    (upperBound, state2) <-
        case dimDeclUpper dimensionDecl of
            Nothing -> error "Array dimension has no upper bound"
            Just upperExpr -> do
                (boundValue, state2) <- evalExpr sym flags upperExpr state1
                case boundValue of
                    SomeInt integerExpr -> pure (integerExpr, state2)
                    _ -> error "Array upper bound must be an integer expression"

    pure ( ArrayDimension { dimensionLower = lowerBound, dimensionUpper = upperBound }, state2 )


evalArrayIndices :: IsExprBuilder sym
    => sym
    -> ObligationFlags
    -> [Index a]
    -> SymState sym
    -> IO ([SymExpr sym BaseIntegerType], SymState sym)
evalArrayIndices sym flags indices state = case indices of
    [] -> pure ([], state)
    indexNode : remainingNodes ->
        case indexNode of
            -- third param Maybe String is for functions/subprocs (?), must be Nothing here
            IxSingle _ann _span Nothing indexExpr -> do
                (indexValue, state1) <- evalExpr sym flags indexExpr state

                integerIndex <-
                    case indexValue of
                        SomeInt value -> pure value
                        _ -> error "Array index is not an integer"

                (remainingIndices, finalState) <- evalArrayIndices sym flags remainingNodes state1
                pure ( integerIndex : remainingIndices, finalState )

            --IxRange goes here, to be implemented
            _ ->
                error "Unsupported array section or index"



createUninitialisedArray :: IsSymExprBuilder sym 
    => sym 
    -> VarName 
    -> VarType 
    -> [ArrayDimension sym] 
    -> IO (SomeExpr sym)
createUninitialisedArray sym name varTy dimensions = do
    uninitialisedMask <- constantArray sym (Ctx.singleton BaseIntegerRepr) (falsePred sym)

    case varTy of
        VarInt -> do
            contents <- freshConstant
                            sym
                            (safeSymbol (name ++ "_contents"))
                            (BaseArrayRepr (Ctx.singleton BaseIntegerRepr) BaseIntegerRepr)

            pure $
                SomeIntArray
                    ArrayRecord
                        { arrayContents = contents
                        , arrayInitMask = uninitialisedMask
                        , arrayDimensions = dimensions
                        }

        VarReal -> do
            contents <- freshConstant
                            sym
                            (safeSymbol (name ++ "_contents"))
                            (BaseArrayRepr (Ctx.singleton BaseIntegerRepr) BaseRealRepr)

            pure $
                SomeRealArray
                    ArrayRecord
                        { arrayContents = contents
                        , arrayInitMask = uninitialisedMask
                        , arrayDimensions = dimensions
                        }

        VarBool -> do
            contents <- freshConstant
                            sym
                            (safeSymbol (name ++ "_contents"))
                            (BaseArrayRepr (Ctx.singleton BaseIntegerRepr) BaseBoolRepr)

            pure $
                SomeBoolArray
                    ArrayRecord
                        { arrayContents = contents
                        , arrayInitMask = uninitialisedMask
                        , arrayDimensions = dimensions
                        }


createConstantArray :: IsExprBuilder sym 
    => sym 
    -> [ArrayDimension sym] 
    -> SomeExpr sym 
    -> IO (SomeExpr sym)
createConstantArray sym dimensions initialValue = do
    initialisedMask <- constantArray sym (Ctx.singleton BaseIntegerRepr) (truePred sym)
    
    case initialValue of
        SomeInt value -> do
            contents <- constantArray sym (Ctx.singleton BaseIntegerRepr) value

            pure $
                SomeIntArray ArrayRecord
                    { arrayContents = contents
                    , arrayInitMask = initialisedMask
                    , arrayDimensions = dimensions
                    }

        SomeReal value -> do
            contents <- constantArray sym (Ctx.singleton BaseIntegerRepr) value

            pure $
                SomeRealArray ArrayRecord
                    { arrayContents = contents
                    , arrayInitMask = initialisedMask
                    , arrayDimensions = dimensions
                    }

        SomeBool value -> do
            contents <- constantArray sym (Ctx.singleton BaseIntegerRepr) value

            pure $
                SomeBoolArray ArrayRecord
                    { arrayContents = contents
                    , arrayInitMask = initialisedMask
                    , arrayDimensions = dimensions
                    }

        SomeIntArray _ -> error "Expected scalar integer initialiser, but got an array"

        SomeRealArray _ -> error "Expected scalar real initialiser, but got an array"

        SomeBoolArray _ -> error "Expected scalar logical initialiser, but got an array"



createArrayFromConstructor :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> VarName
    -> VarType
    -> [ArrayDimension sym]
    -> [Expression a]
    -> SymState sym
    -> IO (SomeExpr sym, SymState sym)
createArrayFromConstructor sym flags name declaredType dimensions elementExprs state = do
    initialArray <- createUninitialisedArray sym name declaredType dimensions
    -- stateWithShapeCheck <- addConstructorShapeObligation dimensions (length elementExprs) state
    -- ^ should check if the length of initialisation array matches the number of elements in declared array
    writeConstructorElements initialArray 0 elementExprs state

    where
        writeConstructorElements arrayExpr flatPosition elementExprs state = 
            case elementExprs of
                [] -> pure (arrayExpr, state)
                (elementExpr : remainingExprs) -> do
                    (elementValue, state1) <- evalExpr sym flags elementExpr state
                    coercedValue <- coerceOnAssignment sym declaredType elementValue

                    flatIndex <- intLit sym flatPosition
                    indices <- unflattenArrayIndex sym dimensions flatIndex
                    (updatedArray, state2) <- updateSomeArray sym flags arrayExpr indices coercedValue state1
                    writeConstructorElements updatedArray (flatPosition + 1) remainingExprs state2

    
-- createArrayFromConstructor :: IsSymExprBuilder sym 
--     => sym 
--     -> ObligationFlags 
--     -> VarName
--     -> VarType 
--     -> [ArrayDimension sym] 
--     -> [Expression a] 
--     -> SymState sym 
--     -> IO (SomeExpr sym, SymState sym)
-- createArrayFromConstructor sym flags name declaredType dimensions elementExprs state = do
--     --assume init array dimensions is equal to actual array
--     (elementValues, finalState) <- evalConstructorElements elementExprs state
--     initialisedMask <- constantArray sym (Ctx.singleton BaseIntegerRepr) (truePred sym)


--     where
--         evalConstructorElements elementExprs state = case elementExprs of
--             [] -> pure ([], state)
--             expr : remainingExprs -> do
--                 (value, state1) <- evalExpr sym flags expr state
--                 coercedValue <- coerceOnAssignment sym declaredType value
--                 (remainingValues, finalState) <- evalConstructorElements remainingExprs state1
--                 pure ( coercedValue : remainingValues, finalState )



--using normal index lists
lookupSomeArray :: IsExprBuilder sym 
    => sym
    -> ObligationFlags
    -> SomeExpr sym 
    -> [SymExpr sym BaseIntegerType]
    -> SymState sym
    -> IO (SomeExpr sym, SymState sym)
lookupSomeArray sym flags arrayExpr indices state =
    case arrayExpr of
        SomeIntArray arrayRecord -> lookupArray sym flags indices SomeInt arrayRecord state
        SomeRealArray arrayRecord -> lookupArray sym flags indices SomeReal arrayRecord state
        SomeBoolArray arrayRecord -> lookupArray sym flags indices SomeBool arrayRecord state
        _ ->
            error "lookupSomeArray: expression is not an array (or unaccepted array)"
    --weirdly, i get type error on SomeInt if i dont including sym, flags, indices and state into params for lookupArray -- will have to ask Nikolaus
    where
        lookupArray sym flags indices wrap arrayRecord state = do
            newState <-
                if isObligationEnabled flags ArrayBounds
                    then do
                        inBoundsPred <- arrayIndicesInBounds sym (arrayDimensions arrayRecord) indices
                        let obligation = Obligation
                                { obligationKind = ArrayBounds
                                , obligationPredicate = inBoundsPred
                                , obligationPath = pathCond state
                                }
                        pure state { obligations = obligation : obligations state }

                    else pure state

            flatIndex <- flattenArrayIndices sym (arrayDimensions arrayRecord) indices
            value <- arrayLookup sym (arrayContents arrayRecord) (Ctx.singleton flatIndex)
            pure (wrap value, newState)



updateSomeArray :: IsExprBuilder sym 
    => sym
    -> ObligationFlags
    -> SomeExpr sym 
    -> [SymExpr sym BaseIntegerType] 
    -> SomeExpr sym 
    -> SymState sym
    -> IO (SomeExpr sym, SymState sym)
updateSomeArray sym flags arrayExpr indices newValue state =
    case (arrayExpr, newValue) of
        (SomeIntArray arrayRecord, SomeInt value) -> updateArray sym flags indices SomeIntArray arrayRecord value state
        (SomeRealArray arrayRecord, SomeReal value) -> updateArray sym flags indices SomeRealArray arrayRecord value state 
            --same type error problem as above
        (SomeBoolArray arrayRecord, SomeBool value) -> updateArray sym flags indices SomeBoolArray arrayRecord value state

        (SomeIntArray {}, _) -> error "updateSomeArray: expected an integer value"
        (SomeRealArray {}, _) -> error "updateSomeArray: expected a real value"
        (SomeBoolArray {}, _) -> error "updateSomeArray: expected a logical value"

        _ -> error "updateSomeArray: expression is not an array"
    where
        updateArray sym flags indices wrap arrayRecord value state = do
            newState <-
                if isObligationEnabled flags ArrayBounds
                    then do
                        inBoundsPred <- arrayIndicesInBounds sym (arrayDimensions arrayRecord) indices
                        let obligation = Obligation
                                { obligationKind = ArrayBounds
                                , obligationPredicate = inBoundsPred
                                , obligationPath = pathCond state
                                }
                        pure state { obligations = obligation : obligations state }

                    else pure state

            flatIndex <- flattenArrayIndices sym (arrayDimensions arrayRecord) indices
            updatedContents <- arrayUpdate sym (arrayContents arrayRecord) (Ctx.singleton flatIndex) value
            updatedInitMask <- arrayUpdate sym (arrayInitMask arrayRecord) (Ctx.singleton flatIndex) (truePred sym)
            let updatedArray = wrap arrayRecord { arrayContents = updatedContents, arrayInitMask = updatedInitMask }
            pure (updatedArray, newState)
