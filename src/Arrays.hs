module Arrays
  ( dimensionOffset
  , dimensionExtent
  , arrayIndexInBounds
  , arrayIndicesInBounds
  , flattenArrayIndices
  , evalArrayDimensions
  , evalArrayDimension
  , createUninitialisedArray
  , createConstantArray
  ) where

import Types
import EvalExpr

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


-- --using normal index lists
-- lookupSomeArray :: IsExprBuilder sym 
--     => sym 
--     -> SomeExpr sym 
--     -> [SymExpr sym BaseIntegerType] 
--     -> IO (SomeExpr sym)
-- lookupSomeArray sym arrayExpr indices = case arrayExpr of
--         SomeRealArray array dimensions -> lookupArray SomeReal array dimensions
--         SomeIntArray array dimensions -> lookupArray SomeInt array dimensions
--         SomeBoolArray array dimensions -> lookupArray SomeBool array dimensions
--     where
--         lookupArray wrap array dimensions = do
--             flatIndex <- flattenArrayIndices sym dimensions indices
--             value <- arrayLookup sym array (Ctx.singleton flatIndex)
--             pure (wrap value)