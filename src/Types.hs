module Types
    ( VarName
    , SomeExpr(..)
    , VarType(..)
    , VarBinding(..)
    , ObligationKind(..)
    , ObligationFlags(..)
    , Obligation(..)
    , SymState(..)
    , isObligationEnabled
    , emptyState
    , Counterexample(..)
    , ObligationResult(..)
    ) where

import Data.Map (Map)
import qualified Data.Map as Map

import What4.Interface
import What4.BaseTypes

type VarName = String

data SomeExpr sym where
    SomeReal :: SymExpr sym BaseRealType -> SomeExpr sym
    SomeInt  :: SymExpr sym BaseIntegerType -> SomeExpr sym
    SomeBool :: Pred sym -> SomeExpr sym

data VarType
    = VarReal
    | VarInt
    | VarBool
    deriving Show

data VarBinding sym = VBinding
    { varType  :: VarType
    , varValue :: Maybe (SomeExpr sym)
    }


data ObligationKind = UserAssertions | DivByZero
    deriving (Eq, Ord, Show)

type ObligationFlags = Map ObligationKind Bool

data Obligation sym = Obligation
    { obligationKind :: ObligationKind,
      obligationPredicate :: Pred sym,
      obligationPath :: [Pred sym]
    }

data SymState sym = SState
    { env :: Map VarName (VarBinding sym),
      pathCond :: [Pred sym],
      obligations :: [Obligation sym],
      freshCount :: Int
    }

isObligationEnabled :: ObligationFlags -> ObligationKind -> Bool
isObligationEnabled flags kind = Map.findWithDefault False kind flags


emptyState :: SymState sym
emptyState = SState
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