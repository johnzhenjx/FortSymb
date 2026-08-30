{-# LANGUAGE ApplicativeDo #-}

module Main (main) where

import qualified Data.ByteString.Char8 as B


import Language.Fortran.Parser hiding (Parser)
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

import Control.Exception
    ( ErrorCall
    , Handler(..)
    , IOException
    , catches
    , displayException
    )
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Options.Applicative



parseCliOptions :: Parser (FilePath, ExecutorFlags, ReportOptions)
parseCliOptions = do
    filePath <- argument str (metavar "FILE" <> help "Path of Fortran source file")
    flags <- parseExecutorFlags
    reportOptions <- parseReportOptions
    pure (filePath, flags, reportOptions)

parseExecutorFlags :: Parser ExecutorFlags
parseExecutorFlags = do
    assertionsEnabled <- flag True False
        ( long "no-user-asserts" <> help "Disable proof obligations generated from user assertions" )
    maxUnroll <- option nonNegativeIntReader
        ( long "max-unroll" <> metavar "N" <> value 10 <> showDefault <> help "Maximum number of DO-loop unrollings" )
    maxCallDepth <- option nonNegativeIntReader
        ( long "max-call-depth" <> metavar "N" <> value 10 <> showDefault <> help "Maximum nested procedure-call depth" )
    pure ExecutorFlags
        { userAssertionEnabled = assertionsEnabled
        , maxDoLoopUnroll = maxUnroll
        , maxProcedureCallDepth = maxCallDepth
        }


nonNegativeIntReader :: ReadM Int
nonNegativeIntReader =
    eitherReader
        (\text ->
            case reads text of
                [(parsedValue, "")]
                    | parsedValue >= 0 -> Right parsedValue
                _ -> Left "expected a non-negative integer"
        )


parseReportOptions :: Parser ReportOptions
parseReportOptions = do
    showValidInternal <- switch
        ( long "show-valid-internal-obligations"
            <> help "Show valid internal proof obligations (DivByZero, ArrayBounds, etc)"
        )
    pure ReportOptions
        { showValidInternalObligations = showValidInternal
        }


cliOptionsInfo :: ParserInfo (FilePath, ExecutorFlags, ReportOptions)
cliOptionsInfo = info (parseCliOptions <**> helper)
        ( fullDesc
        <> header "FortSymb"
        )


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



exitWithError :: String -> IO a
exitWithError message = do
    hPutStrLn stderr message
    exitFailure


handleErrorCall :: ErrorCall -> IO a
handleErrorCall exception = exitWithError (takeWhile (/= '\n') (displayException exception))


handleIOError :: IOException -> IO a
handleIOError exception = exitWithError (displayException exception)


main :: IO ()
main = runFortSymb `catches` [ Handler handleErrorCall, Handler handleIOError ]


runFortSymb :: IO ()
runFortSymb = do
    (filePath, flags, reportOptions) <- execParser cliOptionsInfo
    
    contents <- B.readFile filePath
    let transformedSource = B.pack (preprocessAssertions (B.unpack contents))

    case byVer Fortran90 filePath transformedSource of
        Left parseError ->
            error $ show parseError

        Right ast -> do
            -- styledAst <- styledText secondaryStyle (show ast)
            -- putStrLn styledAst
            -- putStrLn ""

            --changed from Some nonceGen <- newIONonceGenerator due to new {-# LANGUAGE ApplicativeDo #-}
            someNonceGen <- newIONonceGenerator
            case someNonceGen of
                Some nonceGen -> do
                    sym <- newExprBuilder FloatRealRepr EmptyExprBuilderState nonceGen
                    extendConfig z3Options (getConfiguration sym)
                    resultStates <- execProgramFile sym flags ast
                    obligationResults <- evaluateAllStateObligations sym resultStates
                    printStatesWithObligationResults sym reportOptions "feasible" resultStates obligationResults
