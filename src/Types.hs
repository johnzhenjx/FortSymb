{-# LANGUAGE TypeOperators #-}

module Types where

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Parameterized.Context as Ctx

import What4.Interface
import What4.BaseTypes


type VarName = String


type IntegerIndex = Ctx.EmptyCtx Ctx.::> BaseIntegerType --flatten all arrays to a 1D

data ArrayDimension sym = ArrayDimension
    { dimensionLower :: SymExpr sym BaseIntegerType
    , dimensionUpper :: SymExpr sym BaseIntegerType
    }

data ArrayRecord sym elementType = ArrayRecord
    { arrayContents :: SymArray sym IntegerIndex elementType
    , arrayInitMask :: SymArray sym IntegerIndex BaseBoolType
    , arrayDimensions :: [ArrayDimension sym]
    }


data SomeExpr sym where
    SomeInt  :: SymExpr sym BaseIntegerType -> SomeExpr sym
    SomeReal :: SymExpr sym BaseRealType -> SomeExpr sym
    SomeBool :: Pred sym -> SomeExpr sym

    --stores SymArray and its 
    SomeIntArray :: ArrayRecord sym BaseIntegerType -> SomeExpr sym
    SomeRealArray :: ArrayRecord sym BaseRealType -> SomeExpr sym
    SomeBoolArray :: ArrayRecord sym BaseBoolType -> SomeExpr sym

data VarType
    = VarReal
    | VarInt
    | VarBool
    | VarArray VarType Int --array of type and rank
    deriving Show

data VarBinding sym = VarBinding
    { varType  :: VarType
    , varValue :: Maybe (SomeExpr sym)
    }


data ObligationKind = UserAssertions | DivByZero | ArrayBounds | ArrayShape
    deriving (Eq, Ord, Show)

type ObligationFlags = Map ObligationKind Bool

data Obligation sym = Obligation
    { obligationKind :: ObligationKind,
      obligationPredicate :: Pred sym,
      obligationPath :: [Pred sym]
    }

data SymState sym = SymState
    { env :: Map VarName (VarBinding sym),
      pathCond :: [Pred sym],
      obligations :: [Obligation sym],
      freshCount :: Int
    }

isObligationEnabled :: ObligationFlags -> ObligationKind -> Bool
isObligationEnabled flags kind = Map.findWithDefault False kind flags


emptyState :: SymState sym
emptyState = SymState
    { env = Map.empty,
      pathCond = [],
      obligations = [],
      freshCount = 0
    }


type Counterexample = Map VarName (Maybe String)

data ObligationResult
    = ObligationValid
    | ObligationInvalid Counterexample
    deriving (Show)