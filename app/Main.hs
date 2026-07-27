module Main (main) where

import qualified Data.ByteString.Char8 as B

import qualified Data.Map as Map

import Language.Fortran.Parser
import Language.Fortran.Version

import What4.Interface
import What4.Expr.Builder
import What4.Expr

import What4.Config (extendConfig)
import What4.Solver
         
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some

import Prelude hiding (EQ, LT, GT)

import Types
import Printer
import Solver
import Executor

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

            let flags = ExecutorFlags {
                obligationFlags = Map.fromList
                    [ (UserAssertions, True)
                    , (DivByZero, True)
                    , (ArrayBounds, True)
                    , (ArrayShape, True)
                    , (IncrementStepNonZero, True)
                    ]
              , maxDoLoopUnroll = 5
            }

            allStates <- execProgramFile sym flags ast
            printStates allStates

            feasibleStates <- keepFeasibleStates sym allStates
            printStates feasibleStates

            obligationResults <- evaluateAllStateObligations sym feasibleStates
            printAllObligationResults obligationResults