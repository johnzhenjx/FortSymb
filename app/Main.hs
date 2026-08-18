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
    maxUnroll <- option auto 
        ( long "max-unroll" <> metavar "N" <> value 10 <> showDefault <> help "Maximum number of DO-loop unrollings" )
    pure ExecutorFlags
        { userAssertionEnabled = assertionsEnabled
        , maxDoLoopUnroll = maxUnroll
        }


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
        <> progDesc "Symbolic executor for Fortran programs"
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



main :: IO ()
main = do
    (filePath, flags, reportOptions) <- execParser cliOptionsInfo
    
    contents <- B.readFile filePath
    let transformedSource = B.pack (preprocessAssertions (B.unpack contents))

    case byVer Fortran90 filePath transformedSource of
        Left err -> do
            putStrLn "Parse error:"
            print err

        Right ast -> do
            styledAst <- styledText secondaryStyle (show ast)
            putStrLn styledAst
            putStrLn ""

            --changed from Some nonceGen <- newIONonceGenerator due to new {-# LANGUAGE ApplicativeDo #-}
            someNonceGen <- newIONonceGenerator
            case someNonceGen of
                Some nonceGen -> do
                    sym <- newExprBuilder FloatRealRepr EmptyExprBuilderState nonceGen
                    extendConfig z3Options (getConfiguration sym)

                    -- allStates <- execProgramFile sym flags ast
                    -- feasibleStates <- keepFeasibleStates sym allStates
                    -- obligationResults <- evaluateAllStateObligations sym feasibleStates
                    -- printStatesWithObligationResults "feasible" feasibleStates obligationResults

                    resultStates <- execProgramFile sym flags ast
                    obligationResults <- evaluateAllStateObligations sym resultStates
                    printStatesWithObligationResults sym reportOptions "feasible" resultStates obligationResults
