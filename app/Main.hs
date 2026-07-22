module Main (main) where

import qualified Data.ByteString.Char8 as B

import Data.Map (Map)  
import qualified Data.Map as Map

import Language.Fortran.Parser
import Language.Fortran.Version
import Language.Fortran.AST
import qualified Language.Fortran.AST.Literal.Real as ASTReal

import What4.Interface
import What4.BaseTypes
import What4.Expr.Builder
import What4.Symbol
import What4.Expr
         ( ExprBuilder,  FloatModeRepr(..), newExprBuilder
         , BoolExpr, GroundValue, groundEval
		 , EmptyExprBuilderState(..), GroundEvalFn, ExprRangeBindings )

import What4.Config (extendConfig)
import What4.Solver
         (defaultLogData, z3Options, withZ3, SatResult(..))
import What4.Protocol.SMTLib2
         (assume, sessionWriter, runCheckSat)

         
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some

import Data.Ratio ((%))

import Prettyprinter

import Prelude hiding (EQ, LT, GT)

import Types
import EvalExpr
import Printer
import Solver
import Arrays
import Attributes
import Functions
import Executor

import qualified Data.List.NonEmpty as NonEmpty

import Control.Monad (forM_, filterM, foldM)

import Data.Char (isSpace)
import Data.List (dropWhileEnd, stripPrefix)






-- !@assert [predicate]
preprocessAssertions :: String -> String
preprocessAssertions source =
    unlines (map rewriteLine (lines source))
    where
        rewriteLine line =
            case breakAssertionComment line of
                Just (indentation, predicate) ->
                    indentation --keep indentation to preserve scope
                        ++ "call fortsymb_assert("
                        ++ predicate
                        ++ ")"
                Nothing -> line

        breakAssertionComment :: String -> Maybe (String, String)
        breakAssertionComment line =
            let indentation = takeWhile isSpace line
                content = dropWhile isSpace line
            in
                case stripPrefix "!@assert " content of
                    Just predicate ->  Just (indentation, (dropWhileEnd isSpace . dropWhile isSpace) predicate)
                    Nothing -> Nothing



main :: IO ()
main = do
    let filename = "test1.f90"
    contents <- B.readFile filename

    let transformedSource = B.pack (preprocessAssertions (B.unpack contents))

    case byVer Fortran90 filename transformedSource of
        Left err -> do
            putStrLn "Parse error:"
            print err

        Right ast -> do
            putStrLn "Parsed successfully!"
            print ast

            Some nonceGen <- newIONonceGenerator
            sym <- newExprBuilder FloatRealRepr EmptyExprBuilderState nonceGen
            extendConfig z3Options (getConfiguration sym)

            let flags = Map.fromList
                    [ (UserAssertions, True)
                    , (DivByZero, True)
                    , (ArrayBounds, True)
                    , (ArrayShape, True)
                    ]

            allStates <- execProgramFile sym flags ast
            printStates allStates

            feasibleStates <- keepFeasibleStates sym allStates
            printStates feasibleStates

            obligationResults <- evaluateAllStateObligations sym feasibleStates
            printAllObligationResults obligationResults