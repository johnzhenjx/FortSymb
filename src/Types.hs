module Types
  ( VarName
  , SomeExpr(..)
  , VarType(..)
  , VarBinding(..)
  , SymState(..)
  , emptyState
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

data SymState sym = SState
    { env        :: Map VarName (VarBinding sym)
    , pathCond   :: [Pred sym]
    , freshCount :: Int
    }

emptyState :: SymState sym
emptyState = SState
    { env = Map.empty
    , pathCond = []
    , freshCount = 0
    }