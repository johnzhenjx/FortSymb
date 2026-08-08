{-# LANGUAGE TypeOperators #-}

module Types where

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Parameterized.Context as Ctx

import What4.Interface
import What4.BaseTypes

import Language.Fortran.AST
import Language.Fortran.Parser
import Language.Fortran.Util.Position

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


data ProcedureDef a
    = FunctionDef
        { functionParameters :: [VarName],
          functionResult     :: VarName,
          functionBody       :: [Block a], 
          functionMaybeReturnTypeSpec :: Maybe (TypeSpec a)
        }
    | SubroutineDef
        { subroutineParameters :: [VarName],
          subroutineBody       :: [Block a]
        }

type ProcedureEnv a = Map String (ProcedureDef a)


data ObligationKind = UserAssertion | DivByZero | ArrayBounds | ArrayShape | IncrementStepNonZero | UninitialisedRead
    deriving (Eq, Ord, Show)

data ExecutorFlags = ExecutorFlags 
    {
        userAssertionEnabled :: Bool,
        maxDoLoopUnroll :: Int
    }
        

data Obligation sym = Obligation
    { obligationKind :: ObligationKind,
      obligationSpan :: SrcSpan,
      obligationPredicate :: Pred sym,
      obligationPath :: [Pred sym]
    }


data ExecutionStatus
    = ExecutionComplete
    | ExecutionHalted HaltReason
    deriving (Show)

data HaltReason
    = LoopUnrollLimitReached
        { incompleteLoopSpan :: SrcSpan
        , incompleteUnrollCount    :: Int
        }
    | ObligationCannotHold
        { unsatObligationKind :: ObligationKind
        , unsatObligationSpan :: SrcSpan
        }
    deriving (Show)

data ValueOutcome sym a
    = ValueAndStateProduced (SomeExpr sym) (SymState sym a)
    | ValueComputationHaltedState (SymState sym a)

data SymState sym a = SymState
    { env :: Map VarName (VarBinding sym),
      pathCond :: [Pred sym],
      obligations :: [Obligation sym],
      freshCount :: Int,
      procedureEnv :: ProcedureEnv a,
      executionStatus :: ExecutionStatus 
    }


emptyState :: ProcedureEnv a -> SymState sym a
emptyState procEnv = SymState
    { env = Map.empty,
      pathCond = [],
      obligations = [],
      freshCount = 0,
      procedureEnv = procEnv,
      executionStatus = ExecutionComplete
    }


type Counterexample = Map VarName (Maybe String)

data ObligationResult
    = ObligationValid
    | ObligationInvalid Counterexample
    deriving (Show)
