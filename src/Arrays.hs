module Arrays where

import Types
import {-# SOURCE #-} EvalExpr (evalExpr, coerceOnAssignment, bindBranches)

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Parameterized.Context as Ctx

import What4.BaseTypes
import What4.Interface
import What4.Symbol

import Language.Fortran.AST

import Control.Monad 


arrayElementType :: SomeExpr sym -> VarType
arrayElementType arrayExpr =
    case arrayExpr of
        SomeIntArray _ -> VarInt
        SomeRealArray _ -> VarReal
        SomeBoolArray _ -> VarBool
        _ -> error "arrayElementType expected an array"

dimensionOffset :: IsSymExprBuilder sym 
    => sym 
    -> ArrayDimension sym 
    -> SymExpr sym BaseIntegerType 
    -> IO (SymExpr sym BaseIntegerType)
dimensionOffset sym dimension index = intSub sym index (dimensionLower dimension)

--upper - lower + 1, symbolically
dimensionExtent :: IsSymExprBuilder sym 
    => sym 
    -> ArrayDimension sym 
    -> IO (SymExpr sym BaseIntegerType)
dimensionExtent sym dimension = do
    difference <- intSub sym (dimensionUpper dimension) (dimensionLower dimension)

    one <- intLit sym 1
    rawExtent <- intAdd sym difference one

    zero <- intLit sym 0
    isNegative <- intLt sym rawExtent zero

    baseTypeIte sym isNegative zero rawExtent
    --clamps at 0, ie in fortran, vec(1:-1) is a zero-sized array

--one dimension, one index
arrayIndexInBounds :: IsSymExprBuilder sym 
    => sym 
    -> ArrayDimension sym 
    -> SymExpr sym BaseIntegerType 
    -> IO (Pred sym)
arrayIndexInBounds sym dimension index = do
    aboveLower <- intLe sym (dimensionLower dimension) index
    belowUpper <- intLe sym index (dimensionUpper dimension)
    andPred sym aboveLower belowUpper


-- andPreds across all dimensions and indices
arrayIndicesInBounds :: IsSymExprBuilder sym 
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
flattenArrayIndices :: IsSymExprBuilder sym 
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



unflattenArrayIndex :: IsSymExprBuilder sym
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



-- evalArrayDimensions ::
--     IsSymExprBuilder sym =>
--     sym ->
--     ObligationFlags ->
--     [DimensionDeclarator a] ->
--     SymState sym a ->
--     IO [([ArrayDimension sym], SymState sym a)]
-- evalArrayDimensions sym flags dimensionDecls state = 
--     case dimensionDecls of
--         [] -> pure [([], state)]
--         decl : decls -> do
--             (dimension, state1) <- evalArrayDimension sym flags decl state
--             (dimensions, state2) <- evalArrayDimensions sym flags decls state1
--             pure (dimension : dimensions, state2)


-- --assume all array sizes known for now
-- evalArrayDimension :: IsSymExprBuilder sym 
--     => sym 
--     -> ObligationFlags 
--     -> DimensionDeclarator a 
--     -> SymState sym a 
--     -> IO (ArrayDimension sym, SymState sym a)
-- evalArrayDimension sym flags dimensionDecl state = do
--     (lowerBound, state1) <-
--         case dimDeclLower dimensionDecl of
--             Nothing -> do
--                 defaultLower <- intLit sym 1
--                 pure (defaultLower, state)
--             Just lowerExpr -> do
--                 (boundValue, state1) <- evalExpr sym flags lowerExpr state
--                 case boundValue of
--                     SomeInt integerExpr -> pure (integerExpr, state1)
--                     _ -> error "Array lower bound must be an integer expression"

--     (upperBound, state2) <-
--         case dimDeclUpper dimensionDecl of
--             Nothing -> error "Array dimension has no upper bound"
--             Just upperExpr -> do
--                 (boundValue, state2) <- evalExpr sym flags upperExpr state1
--                 case boundValue of
--                     SomeInt integerExpr -> pure (integerExpr, state2)
--                     _ -> error "Array upper bound must be an integer expression"

--     pure ( ArrayDimension { dimensionLower = lowerBound, dimensionUpper = upperBound }, state2 )



evalArrayDimensions :: IsSymExprBuilder sym 
    => sym 
    -> ObligationFlags
    -> [DimensionDeclarator a]
    -> SymState sym a 
    -> IO [([ArrayDimension sym], SymState sym a)]
evalArrayDimensions sym flags dimensionDecls state =
    case dimensionDecls of
        [] -> pure [([], state)]
        decl : decls ->
            bindBranches
                (evalArrayDimension sym flags decl state)
                (\dimension state1 ->
                    bindBranches
                        (evalArrayDimensions sym flags decls state1)
                        (\dimensions state2 ->
                            pure [ (dimension : dimensions, state2) ]
                        )
                )

evalArrayDimension :: IsSymExprBuilder sym 
    => sym 
    -> ObligationFlags 
    -> DimensionDeclarator a 
    -> SymState sym a 
    -> IO [(ArrayDimension sym, SymState sym a)]

evalArrayDimension sym flags dimensionDecl state =
    case dimDeclUpper dimensionDecl of
        Nothing -> error "Array dimension has no upper bound"

        Just upperExpr ->
            bindBranches
                (case dimDeclLower dimensionDecl of
                    Nothing -> do --default lower bound of 1
                        lowerBound <- intLit sym 1
                        pure [(lowerBound, state)]

                    Just lowerExpr ->
                        bindBranches
                            (evalExpr sym flags lowerExpr state)
                            (\value state1 ->
                                case value of
                                    SomeInt lowerBound -> pure [(lowerBound, state1)]
                                    _ -> error "Array lower bound must be an integer expression"
                        )
                )
                (\lowerBound state1 ->
                    bindBranches
                        (evalExpr sym flags upperExpr state1)
                        (\value state2 ->
                            case value of
                                SomeInt upperBound ->
                                    pure [ ( ArrayDimension { dimensionLower = lowerBound, dimensionUpper = upperBound}, state2 ) ]
                                _ -> error "Array upper bound must be an integer expression"
                        )
                )



evalArrayIndices :: IsSymExprBuilder sym
    => sym
    -> ObligationFlags
    -> [Index a]
    -> SymState sym a
    -> IO [([SymExpr sym BaseIntegerType], SymState sym a)]

evalArrayIndices sym flags indices state =
    case indices of
        [] -> pure [([], state)]

        (IxSingle _ann _span Nothing indexExpr) : remainingNodes ->
            bindBranches
                (evalExpr sym flags indexExpr state)
                (\indexValue state1 -> do
                    integerIndex <- case indexValue of
                        SomeInt value -> pure value
                        _ -> error "Array index is not an integer"

                    bindBranches
                        (evalArrayIndices sym flags remainingNodes state1)
                        (\remainingIndices finalState ->
                            pure [ ( integerIndex : remainingIndices, finalState) ])
                    )
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


createConstantArray :: IsSymExprBuilder sym 
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
    -> SymState sym a
    -> IO [(SomeExpr sym, SymState sym a)]

createArrayFromConstructor sym flags name declaredType dimensions elementExprs state = do
    initialArray <- createUninitialisedArray sym name declaredType dimensions
    stateWithShapeCheck <- addConstructorShapeObligation sym flags dimensions (length elementExprs) state
    -- ^ checks if the length of initialisation array matches the number of elements in declared array
    writeConstructorElements initialArray 0 elementExprs stateWithShapeCheck

    where
        writeConstructorElements arrayExpr flatPosition elementExprs state = 
            case elementExprs of
                [] -> pure [(arrayExpr, state)]
                (elementExpr : remainingExprs) -> 
                    bindBranches
                        (evalExpr sym flags elementExpr state)
                        (\elementValue state1 -> do
                            coercedValue <- coerceOnAssignment sym declaredType elementValue
                            flatIndex <- intLit sym flatPosition
                            indices <- unflattenArrayIndex sym dimensions flatIndex
                            (updatedArray, state2) <- updateSomeArray sym flags arrayExpr indices coercedValue state1
                            writeConstructorElements updatedArray (flatPosition + 1) remainingExprs state2
                        )


        addConstructorShapeObligation sym flags dimensions constructorLength state
            | not (isObligationEnabled flags ArrayShape) = pure state
            | otherwise = do
                extents <- mapM (dimensionExtent sym) dimensions
                one <- intLit sym 1
                arraySize <- foldM (intMul sym) one extents
                suppliedSize <- intLit sym (toInteger constructorLength)
                shapeMatches <- isEq sym arraySize suppliedSize
                
                let obligation = Obligation
                        { obligationKind = ArrayBounds
                        , obligationPredicate = shapeMatches
                        , obligationPath = pathCond state
                        }

                pure state { obligations = obligation : obligations state }


-- createArrayFromConstructor sym flags name declaredType dimensions elementExprs state = do
--     initialArray <- createUninitialisedArray sym name declaredType dimensions
--     stateWithShapeCheck <- addConstructorShapeObligation sym flags dimensions (length elementExprs) state
--     -- ^ checks if the length of initialisation array matches the number of elements in declared array
--     writeConstructorElements initialArray 0 elementExprs stateWithShapeCheck

--     where
--         writeConstructorElements arrayExpr flatPosition elementExprs state = 
--             case elementExprs of
--                 [] -> pure (arrayExpr, state)
--                 (elementExpr : remainingExprs) -> do
--                     (elementValue, state1) <- evalExpr sym flags elementExpr state
--                     coercedValue <- coerceOnAssignment sym declaredType elementValue

--                     flatIndex <- intLit sym flatPosition
--                     indices <- unflattenArrayIndex sym dimensions flatIndex
--                     (updatedArray, state2) <- updateSomeArray sym flags arrayExpr indices coercedValue state1
--                     writeConstructorElements updatedArray (flatPosition + 1) remainingExprs state2


--         addConstructorShapeObligation sym flags dimensions constructorLength state
--             | not (isObligationEnabled flags ArrayShape) = pure state
--             | otherwise = do
--                 extents <- mapM (dimensionExtent sym) dimensions
--                 one <- intLit sym 1
--                 arraySize <- foldM (intMul sym) one extents
--                 suppliedSize <- intLit sym (toInteger constructorLength)
--                 shapeMatches <- isEq sym arraySize suppliedSize
                
--                 let obligation = Obligation
--                         { obligationKind = ArrayBounds
--                         , obligationPredicate = shapeMatches
--                         , obligationPath = pathCond state
--                         }

--                 pure state { obligations = obligation : obligations state }



--using normal index lists
lookupSomeArray :: IsSymExprBuilder sym 
    => sym
    -> ObligationFlags
    -> SomeExpr sym 
    -> [SymExpr sym BaseIntegerType]
    -> SymState sym a
    -> IO (SomeExpr sym, SymState sym a)
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



updateSomeArray :: IsSymExprBuilder sym 
    => sym
    -> ObligationFlags
    -> SomeExpr sym 
    -> [SymExpr sym BaseIntegerType] 
    -> SomeExpr sym 
    -> SymState sym a
    -> IO (SomeExpr sym, SymState sym a)
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
