module Arrays where

import Types
import {-# SOURCE #-} EvalExpr (evalExpr, coerceOnAssignment, bindValueOutcomes)
import SymbolicPath

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Parameterized.Context as Ctx

import What4.BaseTypes
import What4.Interface
import What4.Symbol
import What4.Expr.Builder

import Language.Fortran.AST
import Language.Fortran.Util.Position (SrcSpan)

import Control.Monad 

-- offset
--     = zero-based, per-dimension positions

-- index
--     = absolute Fortran indices, start-offsetted

-- flatIndex
--     = one zero-based position for the entire flattened array


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
                

--symbolic flat=(i1​−L1​)+N1​((i2​−L2​)+N2​((i3​−L3​)+⋯)) IS ZERO INDEXED
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
            zero <- intLit sym 0
            one <- intLit sym 1
            extent <- dimensionExtent sym dimension
            extentIsZero <- intEq sym extent zero
            --empty arrays have no valid indices, but their backing functions must still avoid division by zero
            --it is assumed that accessing zero arrays will always fail bounds check so safeExtent is not problematic
            safeExtent <- baseTypeIte sym extentIsZero one extent
            offset <- intMod sym remainingFlatIndex safeExtent
            nextFlatIndex <- intDiv sym remainingFlatIndex safeExtent
            index <- intAdd sym (dimensionLower dimension) offset
            remainingIndices <- go remainingDimensions nextFlatIndex
            pure (index : remainingIndices)




evalArrayDimensions :: 
    ExprBuilder t st fs
    -> ExecutorFlags
    -> [DimensionDeclarator a]
    -> SymState (ExprBuilder t st fs) a 
    -> IO [ValueOutcome (ExprBuilder t st fs) a [ArrayDimension (ExprBuilder t st fs)]]
evalArrayDimensions sym flags dimensionDecls state =
    case dimensionDecls of
        [] -> pure [ValueAndStateProduced [] state]
        decl : decls ->
            bindValueOutcomes
                (evalArrayDimension sym flags decl state)
                (\(dimension, state1) ->
                    bindValueOutcomes
                        (evalArrayDimensions sym flags decls state1)
                        (\(dimensions, state2) ->
                            pure [ValueAndStateProduced (dimension : dimensions) state2]
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])
                )
                (\haltedState -> pure [ValueComputationHaltedState haltedState])

evalArrayDimension ::
    ExprBuilder t st fs
    -> ExecutorFlags 
    -> DimensionDeclarator a 
    -> SymState (ExprBuilder t st fs) a 
    -> IO [ValueOutcome (ExprBuilder t st fs) a (ArrayDimension (ExprBuilder t st fs))]

evalArrayDimension sym flags dimensionDecl state =
    case dimDeclUpper dimensionDecl of
        Nothing -> error "Array dimension has no upper bound"

        Just upperExpr ->
            bindValueOutcomes
                (case dimDeclLower dimensionDecl of
                    Nothing -> do --default lower bound of 1
                        lowerBound <- intLit sym 1
                        pure [ValueAndStateProduced lowerBound state]

                    Just lowerExpr ->
                        bindValueOutcomes
                            (evalExpr sym flags lowerExpr state)
                            (\(value, state1) ->
                                case value of
                                    SomeInt lowerBound -> pure [ValueAndStateProduced lowerBound state1]
                                    _ -> error "Array lower bound must be an integer expression"
                            )
                            (\haltedState -> pure [ValueComputationHaltedState haltedState])
                )
                (\(lowerBound, state1) ->
                    bindValueOutcomes
                        (evalExpr sym flags upperExpr state1)
                        (\(value, state2) ->
                            case value of
                                SomeInt upperBound ->
                                    pure
                                        [ ValueAndStateProduced
                                            (ArrayDimension
                                                { dimensionLower = lowerBound
                                                , dimensionUpper = upperBound
                                                })
                                            state2
                                        ]
                                _ -> error "Array upper bound must be an integer expression"
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])
                )
                (\haltedState -> pure [ValueComputationHaltedState haltedState])



data EvaluatedArraySubscript sym
    = ScalarSubscript (SymExpr sym BaseIntegerType)
    | SectionSubscript
        { sectionStart :: SymExpr sym BaseIntegerType
        , sectionStride :: SymExpr sym BaseIntegerType
        , sectionExtent :: SymExpr sym BaseIntegerType
        }


evalArraySubscripts ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> [ArrayDimension (ExprBuilder t st fs)]
    -> [Index a]
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a [EvaluatedArraySubscript (ExprBuilder t st fs)]]
evalArraySubscripts sym flags dimensions indices state =
    case (dimensions, indices) of
        ([], []) -> pure [ValueAndStateProduced [] state]

        (dimension : remainingDimensions, index : remainingIndices) ->
            bindValueOutcomes
                (evalArraySubscript sym flags dimension index state)
                (\(subscript, state1) ->
                    bindValueOutcomes
                        (evalArraySubscripts sym flags remainingDimensions remainingIndices state1)
                        (\(remainingSubscripts, state2) ->
                            pure [ValueAndStateProduced (subscript : remainingSubscripts) state2]
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])
                )
                (\haltedState -> pure [ValueComputationHaltedState haltedState])

        _ -> error "Array rank mismatch"

    where
        evalArraySubscript sym flags dimension index state =
            case index of
                IxSingle _ann _span Nothing indexExpr ->
                    bindValueOutcomes
                        (evalExpr sym flags indexExpr state)
                        (\(indexValue, state1) ->
                            case indexValue of
                                SomeInt integerIndex -> pure [ValueAndStateProduced (ScalarSubscript integerIndex) state1]
                                _ -> error "Array index is not an integer"
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])

                IxSingle _ann _span (Just _) _indexExpr ->
                    error "Named array indices are not supported"

                IxRange _ann span maybeLowerExpr maybeUpperExpr maybeStrideExpr ->
                    bindValueOutcomes
                        (evalMaybeIntegerExpr maybeLowerExpr state)
                        (\(maybeLower, state1) ->
                            bindValueOutcomes
                                (evalMaybeIntegerExpr maybeUpperExpr state1)
                                (\(maybeUpper, state2) ->
                                    bindValueOutcomes
                                        (evalMaybeIntegerExpr maybeStrideExpr state2)
                                        (\(maybeStride, state3) -> do
                                            one <- intLit sym 1
                                            zero <- intLit sym 0
                                            let stride = maybe one id maybeStride
                                            strideIsZero <- intEq sym stride zero
                                            strideIsNonZero <- notPred sym strideIsZero
                                            state4 <- addObligationAndAssume sym ArraySectionStrideNonZero span strideIsNonZero state3

                                            case executionStatus state4 of
                                                ExecutionHalted _ ->
                                                    pure [ValueComputationHaltedState state4]
                                                ExecutionComplete -> do
                                                    strideIsPositive <- intLt sym zero stride
                                                    defaultStart <-
                                                        baseTypeIte
                                                            sym
                                                            strideIsPositive
                                                            (dimensionLower dimension)
                                                            (dimensionUpper dimension)
                                                    defaultEnd <-
                                                        baseTypeIte
                                                            sym
                                                            strideIsPositive
                                                            (dimensionUpper dimension)
                                                            (dimensionLower dimension)
                                                    let start = maybe defaultStart id maybeLower
                                                        end = maybe defaultEnd id maybeUpper
                                                    extent <- arraySectionExtent sym start end stride
                                                    pure
                                                        [ ValueAndStateProduced
                                                            (SectionSubscript
                                                                { sectionStart = start
                                                                , sectionStride = stride
                                                                , sectionExtent = extent
                                                                })
                                                            state4
                                                        ]
                                        )
                                        (\haltedState -> pure [ValueComputationHaltedState haltedState])
                                )
                                (\haltedState -> pure [ValueComputationHaltedState haltedState])
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])

        evalMaybeIntegerExpr maybeExpr state =
            case maybeExpr of
                Nothing -> pure [ValueAndStateProduced Nothing state]
                Just expr ->
                    bindValueOutcomes
                        (evalExpr sym flags expr state)
                        (\(value, state1) ->
                            case value of
                                SomeInt integerValue -> pure [ValueAndStateProduced (Just integerValue) state1]
                                _ -> error "Array section bound or stride is not an integer"
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])


--computes how many elements a section contains
arraySectionExtent ::
    IsSymExprBuilder sym
    => sym
    -> SymExpr sym BaseIntegerType
    -> SymExpr sym BaseIntegerType
    -> SymExpr sym BaseIntegerType
    -> IO (SymExpr sym BaseIntegerType)
arraySectionExtent sym start end stride = do
    zero <- intLit sym 0
    one <- intLit sym 1
    let extentInDirection lower upper positiveStride = do
            hasElements <- intLe sym lower upper
            distance <- intSub sym upper lower
            steps <- intDiv sym distance positiveStride
            --add 1 as steps counts the gaps between elements but we need to count the elements themselves
            extent <- intAdd sym steps one
            baseTypeIte sym hasElements extent zero

    strideIsPositive <- intLt sym zero stride
    negativeStride <- intNeg sym stride
    positiveResult <- extentInDirection start end stride
    negativeResult <- extentInDirection end start negativeStride

    baseTypeIte sym strideIsPositive positiveResult negativeResult


arraySubscriptsInBounds ::
    IsSymExprBuilder sym
    => sym
    -> [ArrayDimension sym]
    -> [EvaluatedArraySubscript sym]
    -> IO (Pred sym)
arraySubscriptsInBounds sym dimensions subscripts =
    case (dimensions, subscripts) of
        ([], []) -> pure (truePred sym)

        (dimension : remainingDimensions, subscript : remainingSubscripts) -> do
            currentPredicate <-
                case subscript of
                    ScalarSubscript index -> arrayIndexInBounds sym dimension index

                    SectionSubscript start stride extent -> do
                        zero <- intLit sym 0
                        one <- intLit sym 1
                        isEmpty <- intEq sym extent zero
                        steps <- intSub sym extent one
                        lastIndex <- intAdd sym start =<< intMul sym steps stride
                        startInBounds <- arrayIndexInBounds sym dimension start
                        endInBounds <- arrayIndexInBounds sym dimension lastIndex
                        orPred sym isEmpty =<< andPred sym startInBounds endInBounds

            remainingPredicate <- arraySubscriptsInBounds sym remainingDimensions remainingSubscripts
            andPred sym currentPredicate remainingPredicate

        _ -> error "Array rank mismatch"


sectionDimensions ::
    IsSymExprBuilder sym
    => sym
    -> [EvaluatedArraySubscript sym]
    -> IO [ArrayDimension sym]
sectionDimensions sym subscripts = do
    lowerBound <- intLit sym 1
    pure (buildDimensions lowerBound subscripts)
    where
        buildDimensions lowerBound remainingSubscripts =
            case remainingSubscripts of
                [] -> []
                --a scalar subscript removes that dimension from the result
                --e.g. matrix(2, :) is a rank 1 result
                ScalarSubscript _ : remaining ->
                    buildDimensions lowerBound remaining
                SectionSubscript _ _ extent : remaining ->
                    ArrayDimension
                        { dimensionLower = lowerBound
                        , dimensionUpper = extent
                        }
                        : buildDimensions lowerBound remaining


hasArraySection :: [EvaluatedArraySubscript sym] -> Bool
hasArraySection = any (\subscript -> case subscript of {ScalarSubscript _ -> False; SectionSubscript {} -> True})


arrayShapesEqual ::
    IsSymExprBuilder sym
    => sym
    -> [ArrayDimension sym]
    -> [ArrayDimension sym]
    -> IO (Pred sym)
arrayShapesEqual sym targetDimensions sourceDimensions =
    case (targetDimensions, sourceDimensions) of
        ([], []) -> pure (truePred sym)

        (targetDimension : remainingTargets, sourceDimension : remainingSources) -> do
            targetExtent <- dimensionExtent sym targetDimension
            sourceExtent <- dimensionExtent sym sourceDimension
            currentDimensionsEqual <- intEq sym targetExtent sourceExtent
            remainingDimensionsEqual <- arrayShapesEqual sym remainingTargets remainingSources
            andPred sym currentDimensionsEqual remainingDimensionsEqual

        _ -> pure (falsePred sym)

createArraySection ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> SomeExpr (ExprBuilder t st fs)
    -> [EvaluatedArraySubscript (ExprBuilder t st fs)]
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
createArraySection sym _flags span arrayExpr subscripts state = do
    let sourceDimensions =
            case arrayExpr of
                SomeIntArray record -> arrayDimensions record
                SomeRealArray record -> arrayDimensions record
                SomeBoolArray record -> arrayDimensions record
                _ -> error "Array section base expression is not an array"

    boundsPredicate <- arraySubscriptsInBounds sym sourceDimensions subscripts
    state1 <- addObligationAndAssume sym ArrayBounds span boundsPredicate state

    case executionStatus state1 of
        ExecutionHalted _ -> pure [ValueComputationHaltedState state1]
        ExecutionComplete -> do
            let sectionId = freshCount state1
                state2 = state1 { freshCount = sectionId + 1 }
            sectionValue <-
                case arrayExpr of
                    SomeIntArray record -> SomeIntArray <$> createSectionRecord sym sectionId record subscripts
                    SomeRealArray record -> SomeRealArray <$> createSectionRecord sym sectionId record subscripts
                    SomeBoolArray record -> SomeBoolArray <$> createSectionRecord sym sectionId record subscripts
                    _ -> error "Array section base expression is not an array"
            pure [ValueAndStateProduced sectionValue state2]

    where
        createSectionRecord ::
            IsSymExprBuilder sym
            => sym
            -> Int
            -> ArrayRecord sym elementType
            -> [EvaluatedArraySubscript sym]
            -> IO (ArrayRecord sym elementType)
        createSectionRecord sym sectionId sourceRecord subscripts = do
            flatIndexVar <-
                freshBoundVar
                    sym
                    (safeSymbol ("array_section_index_" ++ show sectionId))
                    BaseIntegerRepr
            resultDimensions <- sectionDimensions sym subscripts
            let flatIndex = varExpr sym flatIndexVar --return an expression that references the bound variable

            resultIndices <- unflattenArrayIndex sym resultDimensions flatIndex
            sourceIndices <- mapSectionIndices sym subscripts resultIndices
            sourceFlatIndex <- flattenArrayIndices sym (arrayDimensions sourceRecord) sourceIndices

            contentsBody <- arrayLookup sym (arrayContents sourceRecord) (Ctx.singleton sourceFlatIndex)
            contentsFunction <-
                definedFn
                    sym
                    (safeSymbol ("array_section_contents_" ++ show sectionId))
                    (Ctx.singleton flatIndexVar)
                    contentsBody
                    AlwaysUnfold
            contents <- arrayFromFn sym contentsFunction

            initMaskBody <-
                arrayLookup sym (arrayInitMask sourceRecord) (Ctx.singleton sourceFlatIndex)
            initMaskFunction <-
                definedFn
                    sym
                    (safeSymbol ("array_section_init_mask_" ++ show sectionId))
                    (Ctx.singleton flatIndexVar)
                    initMaskBody
                    AlwaysUnfold
            initMask <- arrayFromFn sym initMaskFunction

            pure
                ArrayRecord
                    { arrayContents = contents
                    , arrayInitMask = initMask
                    , arrayDimensions = resultDimensions
                    }


        --converts indices in newly created (one-indexed) section array back into indices of source array
        mapSectionIndices ::
            IsSymExprBuilder sym
            => sym
            -> [EvaluatedArraySubscript sym]
            -> [SymExpr sym BaseIntegerType]
            -> IO [SymExpr sym BaseIntegerType]
        mapSectionIndices sym subscripts sectionIndices =
            case (subscripts, sectionIndices) of
                ([], []) -> pure []

                (ScalarSubscript index : remainingSubscripts, _) -> do
                    --scalar section indices map to themselves and do not consume a result index
                    remainingIndices <- mapSectionIndices sym remainingSubscripts sectionIndices
                    pure (index : remainingIndices)

                (SectionSubscript start stride _extent : remainingSubscripts, sectionIndex : remainingSectionIndices) -> do
                    one <- intLit sym 1
                    logicalSteps <- intSub sym sectionIndex one --no. of steps in logical (1,2,3,...)
                    sourceIndex <- intAdd sym start =<< intMul sym logicalSteps stride --start + space covered in original
                    remainingIndices <- mapSectionIndices sym remainingSubscripts remainingSectionIndices
                    pure (sourceIndex : remainingIndices)

                _ -> error "Array section rank mismatch"


updateArraySection ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> SomeExpr (ExprBuilder t st fs)
    -> [EvaluatedArraySubscript (ExprBuilder t st fs)]
    -> SomeExpr (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
updateArraySection sym _flags span targetArray subscripts sourceValue state = do
    let targetDimensions =
            case targetArray of
                SomeIntArray record -> arrayDimensions record
                SomeRealArray record -> arrayDimensions record
                SomeBoolArray record -> arrayDimensions record
                _ -> error "Array section assignment target is not an array"

    boundsPredicate <- arraySubscriptsInBounds sym targetDimensions subscripts
    state1 <- addObligationAndAssume sym ArrayBounds span boundsPredicate state

    case executionStatus state1 of
        ExecutionHalted _ -> pure [ValueComputationHaltedState state1]
        ExecutionComplete ->
            case (targetArray, sourceValue) of
                (SomeIntArray targetRecord, SomeInt value) ->
                    updateArraySectionFromScalar sym subscripts SomeIntArray targetRecord value state1
                (SomeRealArray targetRecord, SomeReal value) ->
                    updateArraySectionFromScalar sym subscripts SomeRealArray targetRecord value state1
                (SomeBoolArray targetRecord, SomeBool value) ->
                    updateArraySectionFromScalar sym subscripts SomeBoolArray targetRecord value state1

                (SomeIntArray targetRecord, SomeIntArray sourceRecord) ->
                    updateArraySectionFromArray sym span subscripts SomeIntArray targetRecord sourceRecord state1
                (SomeRealArray targetRecord, SomeRealArray sourceRecord) ->
                    updateArraySectionFromArray sym span subscripts SomeRealArray targetRecord sourceRecord state1
                (SomeBoolArray targetRecord, SomeBoolArray sourceRecord) ->
                    updateArraySectionFromArray sym span subscripts SomeBoolArray targetRecord sourceRecord state1

                (SomeIntArray {}, _) -> error "Integer array section requires an integer scalar or array"
                (SomeRealArray {}, _) -> error "Real array section requires a real scalar or array"
                (SomeBoolArray {}, _) -> error "Logical array section requires a logical scalar or array"
                _ -> error "Array section assignment target is not an array"


updateArraySectionFromScalar ::
    ExprBuilder t st fs
    -> [EvaluatedArraySubscript (ExprBuilder t st fs)]
    -> (ArrayRecord (ExprBuilder t st fs) elementType -> SomeExpr (ExprBuilder t st fs))
    -> ArrayRecord (ExprBuilder t st fs) elementType
    -> SymExpr (ExprBuilder t st fs) elementType
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
updateArraySectionFromScalar sym subscripts wrap targetRecord value state = do
    let sectionId = freshCount state
    updatedRecord <-
        createSectionOverlay
            sym
            sectionId
            targetRecord
            subscripts
            (\_offsets -> pure value)
            (\_offsets -> pure (truePred sym))
    let updatedState = state { freshCount = sectionId + 1 }
    pure [ValueAndStateProduced (wrap updatedRecord) updatedState]


updateArraySectionFromArray ::
    ExprBuilder t st fs
    -> SrcSpan
    -> [EvaluatedArraySubscript (ExprBuilder t st fs)]
    -> (ArrayRecord (ExprBuilder t st fs) elementType -> SomeExpr (ExprBuilder t st fs))
    -> ArrayRecord (ExprBuilder t st fs) elementType
    -> ArrayRecord (ExprBuilder t st fs) elementType
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
updateArraySectionFromArray sym span subscripts wrap targetRecord sourceRecord state = do
    targetDimensions <- sectionDimensions sym subscripts
    shapePredicate <- arrayShapesEqual sym targetDimensions (arrayDimensions sourceRecord)
    stateAfterShape <- addObligationAndAssume sym ArrayShape span shapePredicate state

    case executionStatus stateAfterShape of
        ExecutionHalted _ -> pure [ValueComputationHaltedState stateAfterShape]
        ExecutionComplete -> do
            let sectionId = freshCount stateAfterShape
            updatedRecord <-
                createSectionOverlay
                    sym
                    sectionId
                    targetRecord
                    subscripts
                    (lookupSourceContents sourceRecord)
                    (lookupSourceInitMask sourceRecord)
            let updatedState = stateAfterShape { freshCount = sectionId + 1 }
            pure [ValueAndStateProduced (wrap updatedRecord) updatedState]

    where
        lookupSourceContents sourceRecord offsets = do
            sourceIndices <- indicesFromOffsets sym (arrayDimensions sourceRecord) offsets
            sourceFlatIndex <- flattenArrayIndices sym (arrayDimensions sourceRecord) sourceIndices
            arrayLookup sym (arrayContents sourceRecord) (Ctx.singleton sourceFlatIndex)

        lookupSourceInitMask sourceRecord offsets = do
            sourceIndices <- indicesFromOffsets sym (arrayDimensions sourceRecord) offsets
            sourceFlatIndex <-
                flattenArrayIndices sym (arrayDimensions sourceRecord) sourceIndices
            arrayLookup sym (arrayInitMask sourceRecord) (Ctx.singleton sourceFlatIndex)


createSectionOverlay ::
    IsSymExprBuilder sym
    => sym
    -> Int
    -> ArrayRecord sym elementType
    -> [EvaluatedArraySubscript sym]
    -> ([SymExpr sym BaseIntegerType] -> IO (SymExpr sym elementType))
    -> ([SymExpr sym BaseIntegerType] -> IO (Pred sym))
    -> IO (ArrayRecord sym elementType)
--returns updatedTarget such that
--updatedTarget(i) = source(sectionOffset(i)) if i is in the section, else targetRecord(i)
--newContentsAt and newInitMaskAt are lambdas \offsets -> ... that tell createSectionOverlay what to replace
--the content and init mask element with respectively
createSectionOverlay sym sectionId targetRecord subscripts newContentsAt newInitMaskAt = do
    flatIndexVar <-
        freshBoundVar
            sym
            (safeSymbol ("array_section_update_index_" ++ show sectionId))
            BaseIntegerRepr
    let flatIndex = varExpr sym flatIndexVar

    targetIndices <- unflattenArrayIndex sym (arrayDimensions targetRecord) flatIndex
    (isSelected, sectionOffsets) <- sectionMembershipAndOffsets sym subscripts targetIndices

    oldContents <- arrayLookup sym (arrayContents targetRecord) (Ctx.singleton flatIndex)
    selectedContents <- newContentsAt sectionOffsets
    contentsBody <- baseTypeIte sym isSelected selectedContents oldContents
    contentsFunction <-
        definedFn
            sym
            (safeSymbol ("array_section_update_contents_" ++ show sectionId))
            (Ctx.singleton flatIndexVar)
            contentsBody
            AlwaysUnfold
    contents <- arrayFromFn sym contentsFunction

    oldInitMask <- arrayLookup sym (arrayInitMask targetRecord) (Ctx.singleton flatIndex)
    selectedInitMask <- newInitMaskAt sectionOffsets
    initMaskBody <- baseTypeIte sym isSelected selectedInitMask oldInitMask
    initMaskFunction <-
        definedFn
            sym
            (safeSymbol ("array_section_update_init_mask_" ++ show sectionId))
            (Ctx.singleton flatIndexVar)
            initMaskBody
            AlwaysUnfold
    initMask <- arrayFromFn sym initMaskFunction

    pure
        targetRecord
            { arrayContents = contents
            , arrayInitMask = initMask
            }


sectionMembershipAndOffsets ::
    IsSymExprBuilder sym
    => sym
    -> [EvaluatedArraySubscript sym]
    -> [SymExpr sym BaseIntegerType]
    -> IO (Pred sym, [SymExpr sym BaseIntegerType])
--targetIndices is generic fresh bound variable representing current flat index
--returns Pred for whether targetIndices is included in section described by subscripts
--and their zero-based positions within their section dimensions (for future arrayLookup)
sectionMembershipAndOffsets sym subscripts targetIndices =
    case (subscripts, targetIndices) of
        ([], []) -> pure (truePred sym, [])

        (ScalarSubscript selectedIndex : remainingSubscripts, targetIndex : remainingTargetIndices) -> do
            currentMatches <- intEq sym targetIndex selectedIndex
            (remainingMatches, remainingOffsets) <-
                sectionMembershipAndOffsets sym remainingSubscripts remainingTargetIndices
            matches <- andPred sym currentMatches remainingMatches
            pure (matches, remainingOffsets)

        (SectionSubscript start stride extent : remainingSubscripts, targetIndex : remainingTargetIndices) -> do
            zero <- intLit sym 0
            one <- intLit sym 1
            
            steps <- intSub sym extent one
            finalIndex <- intAdd sym start =<< intMul sym steps stride

            --1. CHECK IF ELEMENT IS WITHIN LOWER AND UPPER
            let targetWithin lower upper = do
                    aboveLower <- intLe sym lower targetIndex
                    belowUpper <- intLe sym targetIndex upper
                    andPred sym aboveLower belowUpper

            strideIsPositive <- intLt sym zero stride

            withinPositiveRange <- targetWithin start finalIndex
            withinNegativeRange <- targetWithin finalIndex start
            withinRange <- baseTypeIte sym strideIsPositive withinPositiveRange withinNegativeRange

            --2. CHECK IF ELEMENT IS ACTUALLY "IN LINE" WITH STRIDE
            difference <- intSub sym targetIndex start
            -- negativeStride <- intNeg sym stride
            -- absoluteStride <- baseTypeIte sym strideIsPositive stride negativeStride
            absoluteStride <- intAbs sym stride
            remainder <- intMod sym difference absoluteStride
            isStrideElement <- intEq sym remainder zero
            
            --ANDS THE TWO + SECTION MUST HAVE NON-ZERO EXTENT
            hasElements <- intLt sym zero extent
            currentMatches <- andPred sym isStrideElement =<< andPred sym hasElements withinRange

            offset <- intDiv sym difference stride --zero-based position within this section dimension
            (remainingMatches, remainingOffsets) <-
                sectionMembershipAndOffsets sym remainingSubscripts remainingTargetIndices
            matches <- andPred sym currentMatches remainingMatches
            pure (matches, offset : remainingOffsets)

        _ -> error "Array section rank mismatch"


indicesFromOffsets ::
    IsSymExprBuilder sym
    => sym
    -> [ArrayDimension sym]
    -> [SymExpr sym BaseIntegerType]
    -> IO [SymExpr sym BaseIntegerType]
--maps zero-based offsets into indices, per dimension
indicesFromOffsets sym dimensions offsets =
    case (dimensions, offsets) of
        ([], []) -> pure []
        (dimension : remainingDimensions, offset : remainingOffsets) -> do
            index <- intAdd sym (dimensionLower dimension) offset
            remainingIndices <- indicesFromOffsets sym remainingDimensions remainingOffsets
            pure (index : remainingIndices)
        _ -> error "Array section shape rank mismatch"




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



createArrayFromConstructor ::
    ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> VarName
    -> VarType
    -> [ArrayDimension (ExprBuilder t st fs)]
    -> [Expression a]
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]

createArrayFromConstructor sym flags span name declaredType dimensions elementExprs state = do
    initialArray <- createUninitialisedArray sym name declaredType dimensions
    stateWithShapeCheck <- addConstructorShapeObligation sym dimensions (length elementExprs) state
    -- ^ checks if the length of initialisation array matches the number of elements in declared array
    case executionStatus stateWithShapeCheck of
        ExecutionHalted _ -> pure [ValueComputationHaltedState stateWithShapeCheck]
        ExecutionComplete -> writeConstructorElements initialArray 0 elementExprs stateWithShapeCheck

    where
        writeConstructorElements arrayExpr flatPosition elementExprs state = 
            case elementExprs of
                [] -> pure [ValueAndStateProduced arrayExpr state]
                (elementExpr : remainingExprs) -> 
                    bindValueOutcomes
                        (evalExpr sym flags elementExpr state)
                        (\(elementValue, state1) -> do
                            coercedValue <- coerceOnAssignment sym declaredType elementValue
                            flatIndex <- intLit sym flatPosition
                            indices <- unflattenArrayIndex sym dimensions flatIndex
                            bindValueOutcomes
                                (updateSomeArray sym flags span arrayExpr indices coercedValue state1)
                                (\(updatedArray, state2) ->
                                    writeConstructorElements updatedArray (flatPosition + 1) remainingExprs state2
                                )
                                (\haltedState -> pure [ValueComputationHaltedState haltedState])
                        )
                        (\haltedState -> pure [ValueComputationHaltedState haltedState])


        addConstructorShapeObligation sym dimensions constructorLength state = do
            extents <- mapM (dimensionExtent sym) dimensions
            one <- intLit sym 1
            arraySize <- foldM (intMul sym) one extents
            suppliedSize <- intLit sym (toInteger constructorLength)
            shapeMatches <- isEq sym arraySize suppliedSize
            addObligationAndAssume sym ArrayShape span shapeMatches state


--using normal index lists
lookupSomeArray :: ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> SomeExpr (ExprBuilder t st fs)
    -> [SymExpr (ExprBuilder t st fs) BaseIntegerType]
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
lookupSomeArray sym _flags span arrayExpr indices state =
    case arrayExpr of
        SomeIntArray arrayRecord -> lookupArray sym span indices SomeInt arrayRecord state
        SomeRealArray arrayRecord -> lookupArray sym span indices SomeReal arrayRecord state
        SomeBoolArray arrayRecord -> lookupArray sym span indices SomeBool arrayRecord state
        _ -> error "lookupSomeArray: expression is not an array (or unaccepted array)"
    --weirdly, i get type error on SomeInt if i dont including sym, flags, indices and state into params for lookupArray -- will have to ask Nikolaus
    where
        lookupArray sym span indices wrap arrayRecord state = do
            inBoundsPred <- arrayIndicesInBounds sym (arrayDimensions arrayRecord) indices
            newState <- addObligationAndAssume sym ArrayBounds span inBoundsPred state

            case executionStatus newState of
                ExecutionHalted _ -> pure [ValueComputationHaltedState newState]
                ExecutionComplete -> do
                    flatIndex <- flattenArrayIndices sym (arrayDimensions arrayRecord) indices
                    initialisedPred <-
                        arrayLookup sym (arrayInitMask arrayRecord) (Ctx.singleton flatIndex)
                    -- Unlike other guarded operations, initialisation can differ
                    -- within one symbolic state, so preserve both feasible subsets.
                    let obligation = Obligation
                            { obligationKind = UninitialisedRead
                            , obligationSpan = span
                            , obligationPredicate = initialisedPred
                            , obligationPath = pathCond newState
                            }
                        stateWithObligation = newState
                            { obligations = obligation : obligations newState }

                    maybeInitialisedState <-
                        addPathConditionAndKeepIfFeasible
                            sym initialisedPred stateWithObligation
                    uninitialisedPred <- notPred sym initialisedPred
                    maybeUninitialisedState <-
                        addPathConditionAndKeepIfFeasible
                            sym uninitialisedPred stateWithObligation

                    successfulOutcomes <-
                        case maybeInitialisedState of
                            Nothing -> pure []
                            Just initialisedState -> do
                                value <- arrayLookup sym (arrayContents arrayRecord) (Ctx.singleton flatIndex)
                                pure [ValueAndStateProduced (wrap value) initialisedState]

                    let haltedOutcomes =
                            case maybeUninitialisedState of
                                Nothing -> []
                                Just uninitialisedState ->
                                    [ ValueComputationHaltedState
                                        uninitialisedState
                                            { executionStatus =
                                                ExecutionHalted
                                                    (ObligationCannotHold UninitialisedRead span)
                                            }
                                    ]
                    pure (successfulOutcomes ++ haltedOutcomes)



updateSomeArray :: ExprBuilder t st fs
    -> ExecutorFlags
    -> SrcSpan
    -> SomeExpr (ExprBuilder t st fs)
    -> [SymExpr (ExprBuilder t st fs) BaseIntegerType]
    -> SomeExpr (ExprBuilder t st fs)
    -> SymState (ExprBuilder t st fs) a
    -> IO [ValueOutcome (ExprBuilder t st fs) a (SomeExpr (ExprBuilder t st fs))]
updateSomeArray sym _flags span arrayExpr indices newValue state =
    case (arrayExpr, newValue) of
        (SomeIntArray arrayRecord, SomeInt value) -> updateArray sym span indices SomeIntArray arrayRecord value state
        (SomeRealArray arrayRecord, SomeReal value) -> updateArray sym span indices SomeRealArray arrayRecord value state
            --same type error problem as above
        (SomeBoolArray arrayRecord, SomeBool value) -> updateArray sym span indices SomeBoolArray arrayRecord value state

        (SomeIntArray {}, _) -> error "updateSomeArray: expected an integer value"
        (SomeRealArray {}, _) -> error "updateSomeArray: expected a real value"
        (SomeBoolArray {}, _) -> error "updateSomeArray: expected a logical value"

        _ -> error "updateSomeArray: expression is not an array"
    where
        updateArray sym span indices wrap arrayRecord value state = do
            inBoundsPred <- arrayIndicesInBounds sym (arrayDimensions arrayRecord) indices
            newState <- addObligationAndAssume sym ArrayBounds span inBoundsPred state

            case executionStatus newState of
                ExecutionHalted _ -> pure [ValueComputationHaltedState newState]
                ExecutionComplete -> do
                    flatIndex <- flattenArrayIndices sym (arrayDimensions arrayRecord) indices
                    updatedContents <- arrayUpdate sym (arrayContents arrayRecord) (Ctx.singleton flatIndex) value
                    updatedInitMask <- arrayUpdate sym (arrayInitMask arrayRecord) (Ctx.singleton flatIndex) (truePred sym)
                    let updatedArray = wrap arrayRecord { arrayContents = updatedContents, arrayInitMask = updatedInitMask }
                    pure [ValueAndStateProduced updatedArray newState]
