{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Printer where

import Data.Char (toUpper)
import Data.List (dropWhileEnd)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import qualified Data.Parameterized.Context as Ctx
import System.Console.ANSI
    ( Color (Cyan, Green, Red)
    , ColorIntensity (Vivid)
    , ConsoleIntensity (BoldIntensity, FaintIntensity)
    , ConsoleLayer (Foreground)
    , SGR (Reset, SetColor, SetConsoleIntensity)
    , hNowSupportsANSI
    , setSGRCode
    )
import System.Environment (lookupEnv)
import System.IO (hIsTerminalDevice, stdout)

import Types
import Arrays (flattenArrayIndices)

import What4.Expr (ExprBuilder)
import What4.Interface
    ( BaseBoolType
    , IsExpr
    , IsSymExprBuilder
    , SymExpr
    , arrayLookup
    , asConstantPred
    , asInteger
    , intLit
    , printSymExpr
    )


data ReportOptions = ReportOptions
    { showValidInternalObligations :: Bool
    }


styledText :: [SGR] -> String -> IO String
styledText style text = do
    enabled <- colourEnabled
    pure $
        if enabled
            then setSGRCode style ++ text ++ setSGRCode [Reset]
            else text


colourEnabled :: IO Bool
colourEnabled = do
    outputIsTerminal <- hIsTerminalDevice stdout
    outputSupportsAnsi <-
        if outputIsTerminal
            then hNowSupportsANSI stdout
            else pure False
    noColourRequested <- isJust <$> lookupEnv "NO_COLOR"
    pure (outputIsTerminal && outputSupportsAnsi && not noColourRequested)


normalStyle, boldStyle, greenStyle, redStyle, cyanStyle, secondaryStyle :: [SGR]
normalStyle = [Reset]
boldStyle = [SetConsoleIntensity BoldIntensity]
greenStyle = [SetColor Foreground Vivid Green]
redStyle = [SetColor Foreground Vivid Red]
cyanStyle = [SetColor Foreground Vivid Cyan]
secondaryStyle = [SetConsoleIntensity FaintIntensity]


showSymExpr :: IsExpr expr => expr tp -> String
showSymExpr = show . printSymExpr


showBinding :: IsExpr (SymExpr sym) => VarBinding sym -> String
showBinding binding =
    show (varType binding)
        ++ case varValue binding of
            Nothing -> ", uninitialised"
            Just value -> ", initialised = " ++ showSomeExpr value


showSomeExpr :: IsExpr (SymExpr sym) => SomeExpr sym -> String
showSomeExpr value =
    case value of
        SomeInt expression -> "int " ++ showSymExpr expression
        SomeReal expression -> "real " ++ showSymExpr expression
        SomeBool predicate -> "bool " ++ showSymExpr predicate
        SomeIntArray array -> showArrayRecord "integer" array
        SomeRealArray array -> showArrayRecord "real" array
        SomeBoolArray array -> showArrayRecord "logical" array


showArrayRecord ::
    IsExpr (SymExpr sym) =>
    String ->
    ArrayRecord sym tp ->
    String
showArrayRecord elementType array =
    unlines
        [ elementType ++ " array"
        , "dimensions:" ++ showArrayDimensions (arrayDimensions array)
        , "contents: " ++ showSymExpr (arrayContents array)
        , "initialisation mask: " ++ showSymExpr (arrayInitMask array)
        ]


showArrayDimensions ::
    IsExpr (SymExpr sym) =>
    [ArrayDimension sym] ->
    String
showArrayDimensions dimensions =
    case dimensions of
        [] -> " none"
        _ -> concatMap showDimension (numbered dimensions)
  where
    showDimension (index, dimension) =
        "\n  "
            ++ show index
            ++ ". lower = "
            ++ showSymExpr (dimensionLower dimension)
            ++ ", upper = "
            ++ showSymExpr (dimensionUpper dimension)


showExecutionStatus :: ExecutionStatus -> String
showExecutionStatus status =
    case status of
        ExecutionComplete -> "Complete"
        ExecutionHalted reason -> "Halted: " ++ showHaltReason reason


showHaltReason :: HaltReason -> String
showHaltReason reason =
    case reason of
        LoopUnrollLimitReached
            { incompleteLoopSpan = loopSpan
            , incompleteUnrollCount = unrollCount
            } ->
                "loop unroll limit reached at "
                    ++ show loopSpan
                    ++ " after "
                    ++ show unrollCount
                    ++ " iterations"

        ObligationCannotHold kind sourceSpan ->
            "obligation cannot hold: "
                ++ show kind
                ++ " at "
                ++ show sourceSpan

        ProcedureCallDepthLimitReached procedureName callDepth callDepthLimit ->
            "procedure call-depth limit reached while calling "
                ++ procedureName
                ++ " at depth "
                ++ show callDepth
                ++ " (limit "
                ++ show callDepthLimit
                ++ ")"


printStates ::
    IsSymExprBuilder sym =>
    sym ->
    String ->
    [SymState sym a] ->
    IO ()
printStates sym label states = do
    printReportHeading label (length states)
    mapM_ printNumberedState (numbered states)
  where
    printNumberedState (index, state) = do
        printStateHeading index
        printState sym state


printState ::
    IsSymExprBuilder sym =>
    sym ->
    SymState sym a ->
    IO ()
printState sym state = do
    printStateDetails sym state
    printObligations (reverse (obligations state))


printStateDetails ::
    IsSymExprBuilder sym =>
    sym ->
    SymState sym a ->
    IO ()
printStateDetails sym state = do
    statusText <-
        styledText
            (case executionStatus state of
                ExecutionComplete -> normalStyle
                ExecutionHalted _ -> redStyle)
            (showExecutionStatus (executionStatus state))
    putStrLn $ "  Status: " ++ statusText

    printEnvironment sym state

    printPredicatesAt
        2
        "Path conditions"
        "<true>"
        (reverse (pathCond state))


printEnvironment ::
    forall sym a.
    IsSymExprBuilder sym =>
    sym ->
    SymState sym a ->
    IO ()
printEnvironment sym state = do
    printSectionHeading 2 "Environment"

    case Map.toList (env state) of
        [] -> printSecondaryLine 4 "<empty>"
        bindings -> mapM_ printBindingEntry bindings

    putStrLn ""
  where
    printBindingEntry (name, binding) = do
        nameText <- styledText boldStyle name
        typeText <- styledText normalStyle (" : " ++ show (varType binding))

        case varValue binding of
            Nothing ->
                putStrLn $ "    " ++ nameText ++ typeText ++ " = <uninitialised>"

            Just value ->
                printBoundValue name nameText typeText value

    printBoundValue plainName styledName typeText value =
        case value of
            SomeInt expression ->
                printInlineOrBlock 4 (styledName ++ typeText ++ " = ") (showSymExpr expression)

            SomeReal expression ->
                printInlineOrBlock 4 (styledName ++ typeText ++ " = ") (showSymExpr expression)

            SomeBool predicate ->
                printInlineOrBlock 4 (styledName ++ typeText ++ " = ") (showSymExpr predicate)

            SomeIntArray array ->
                printArrayValue plainName styledName typeText "integer" array

            SomeRealArray array ->
                printArrayValue plainName styledName typeText "real" array

            SomeBoolArray array ->
                printArrayValue plainName styledName typeText "logical" array

    printArrayValue ::
        forall tp.
        String ->
        String ->
        String ->
        String ->
        ArrayRecord sym tp ->
        IO ()
    printArrayValue plainName styledName typeText elementType array = do
        arrayDescription <-
            styledText normalStyle (" (initialised " ++ elementType ++ " array)")
        putStrLn $ "    " ++ styledName ++ typeText ++ arrayDescription

        case numbered (arrayDimensions array) of
            [] -> printSecondaryLine 6 "Dimensions: <none>"
            dimensions -> mapM_ printDimension dimensions

        maybeElements <- expandConcreteArray sym array
        case maybeElements of
            Just [] -> printSecondaryLine 6 "Elements: <empty>"
            Just elements -> mapM_ (printArrayElement plainName) elements
            Nothing -> do
                printInlineOrBlock 6 "Contents: " (showSymExpr (arrayContents array))
                printInlineOrBlock 6 "Initialisation mask: " (showSymExpr (arrayInitMask array))

    printDimension (index, dimension) = do
        let lower = showSymExpr (dimensionLower dimension)
            upper = showSymExpr (dimensionUpper dimension)
            label = "Dimension " ++ show index ++ ": "
        case (lines lower, lines upper) of
            ([lowerLine], [upperLine]) ->
                printSecondaryLine 6 (label ++ lowerLine ++ " .. " ++ upperLine)
            _ -> do
                printSecondaryLine 6 ("Dimension " ++ show index ++ ":")
                printInlineOrBlock 8 "Lower: " lower
                printInlineOrBlock 8 "Upper: " upper

    printArrayElement ::
        forall tp.
        String ->
        ([Integer], Maybe (SymExpr sym tp)) ->
        IO ()
    printArrayElement name (indices, maybeValue) =
        printInlineOrBlock
            6
            (name ++ "(" ++ commaSeparated (map show indices) ++ ") = ")
            (maybe "<uninitialised>" showSymExpr maybeValue)


printPredicates ::
    IsExpr expr =>
    String ->
    String ->
    [expr BaseBoolType] ->
    IO ()
printPredicates = printPredicatesAt 0


printPredicatesAt ::
    IsExpr expr =>
    Int ->
    String ->
    String ->
    [expr BaseBoolType] ->
    IO ()
printPredicatesAt indentation heading emptyMessage predicates = do
    printSectionHeading indentation (dropTrailingColon heading)

    case numbered predicates of
        [] -> printSecondaryLine (indentation + 2) emptyMessage
        numberedPredicates ->
            printNumberedTextBlocks
                normalStyle
                (indentation + 2)
                (map (\(index, predicate) -> (index, showSymExpr predicate)) numberedPredicates)

    putStrLn ""


printObligations ::
    IsExpr (SymExpr sym) =>
    [Obligation sym] ->
    IO ()
printObligations obligationsToPrint = do
    printNumberedObligations (numbered obligationsToPrint) 0


printNumberedObligations ::
    IsExpr (SymExpr sym) =>
    [(Int, Obligation sym)] ->
    Int ->
    IO ()
printNumberedObligations numberedObligations hiddenCount = do
    printSectionHeading 2 "Proof obligations"

    case numberedObligations of
        [] -> printSecondaryLine 4 (if hiddenCount == 0 then "<none>" else "<none shown>")
        _ -> mapM_ printObligation numberedObligations

    printHiddenObligationCount hiddenCount

    putStrLn ""
  where
    printObligation (index, obligation) = do
        kindText <- styledText cyanStyle (show (obligationKind obligation))
        spanText <-
            styledText normalStyle (" at " ++ show (obligationSpan obligation))
        putStrLn $
            "    "
                ++ show index
                ++ ". "
                ++ kindText
                ++ spanText

        printInlineOrBlock
            6 "Predicate: "
            (showSymExpr (obligationPredicate obligation))

        case numbered (reverse (obligationPath obligation)) of
            [] -> printSecondaryLine 6 "Path: <true>"
            predicates -> do
                printSecondaryLine 6 "Path:"
                printNumberedTextBlocks
                    normalStyle
                    8
                    (map (\(pathIndex, predicate) -> (pathIndex, showSymExpr predicate)) predicates)


printAllObligationResults ::
    [[
        ( Obligation (ExprBuilder t st fs)
        , ObligationResult
        )
    ]] ->
    IO ()
printAllObligationResults stateResults =
    mapM_ printStateResult (numbered stateResults)
  where
    printStateResult (stateNumber, results) = do
        printStateHeading stateNumber
        printObligationResults results


printStatesWithObligationResults ::
    IsSymExprBuilder sym =>
    sym ->
    ReportOptions ->
    String ->
    [SymState sym a] ->
    [[(Obligation sym, ObligationResult)]] ->
    IO ()
printStatesWithObligationResults sym reportOptions label states stateResults = do
    printReportHeading label (length states)
    printPairedStates (1 :: Int) states stateResults
  where
    printPairedStates _ [] [] = pure ()

    printPairedStates index (state : remainingStates) (results : remainingResults) = do
        let numberedResults = numbered results
            visibleResults = filter (shouldPrintObligationResult reportOptions . snd) numberedResults
            hiddenCount = length numberedResults - length visibleResults
        printStateHeading index
        printStateDetails sym state
        printNumberedObligations
            (map (\(number, (obligation, _result)) -> (number, obligation)) visibleResults)
            hiddenCount
        printNumberedObligationResults visibleResults hiddenCount
        printPairedStates (index + 1) remainingStates remainingResults

    printPairedStates _ _ _ =
        error "State and obligation-result counts do not match."


printObligationResults ::
    [(Obligation sym, ObligationResult)] ->
    IO ()
printObligationResults results = do
    printNumberedObligationResults (numbered results) 0


printNumberedObligationResults ::
    [(Int, (Obligation sym, ObligationResult))] ->
    Int ->
    IO ()
printNumberedObligationResults numberedResults hiddenCount = do
    printSectionHeading 2 "Obligation results"

    case numberedResults of
        [] -> printSecondaryLine 4 (if hiddenCount == 0 then "<none>" else "<none shown>")
        _ -> mapM_ printObligationResult numberedResults

    printHiddenObligationCount hiddenCount

    putStrLn ""


shouldPrintObligationResult ::
    ReportOptions ->
    (Obligation sym, ObligationResult) ->
    Bool
shouldPrintObligationResult reportOptions (obligation, result) =
    case result of
        ObligationInvalid _ -> True
        ObligationValid ->
            obligationKind obligation == UserAssertion
                || showValidInternalObligations reportOptions


printHiddenObligationCount :: Int -> IO ()
printHiddenObligationCount hiddenCount =
    if hiddenCount == 0
        then pure ()
        else
            printStyledLine
                secondaryStyle
                4
                (show hiddenCount ++ " valid internal " ++ noun ++ " hidden")
  where
    noun =
        if hiddenCount == 1
            then "obligation"
            else "obligations"


printObligationResult ::
    (Int, (Obligation sym, ObligationResult)) ->
    IO ()
printObligationResult
    ( obligationNumber
    , (obligation, result)
    ) = do
        kindText <- styledText cyanStyle (show (obligationKind obligation))
        spanText <-
            styledText normalStyle (" at " ++ show (obligationSpan obligation))
        resultText <-
            styledText
                (case result of
                    ObligationValid -> greenStyle
                    ObligationInvalid _ -> redStyle)
                (showObligationResult result)
        putStrLn $
            "    "
                ++ show obligationNumber
                ++ ". "
                ++ kindText
                ++ spanText
                ++ ": "
                ++ resultText

        case result of
            ObligationValid -> pure ()
            ObligationInvalid counterexample -> printCounterexample counterexample


showObligationResult :: ObligationResult -> String
showObligationResult result =
    case result of
        ObligationValid -> "Valid"
        ObligationInvalid _ -> "Invalid"


printCounterexample :: Counterexample -> IO ()
printCounterexample counterexample = do
    putStrLn "      Counterexample:"

    case Map.toList counterexample of
        [] -> printSecondaryLine 8 "<empty>"
        variables -> mapM_ printVariable variables
  where
    printVariable (name, maybeValue) = do
        nameText <- styledText boldStyle name
        printInlineOrBlock
            8 (nameText ++ " = ") (maybe "<uninitialised>" id maybeValue)


printReportHeading :: String -> Int -> IO ()
printReportHeading label stateCount = do
    heading <- styledText boldStyle "FortSymb verification report"
    stateCountText <- styledText normalStyle (stateCountHeading label stateCount)
    putStrLn heading
    putStrLn stateCountText
    putStrLn ""


printStateHeading :: Int -> IO ()
printStateHeading index = do
    heading <- styledText boldStyle ("State " ++ show index)
    putStrLn heading


printSectionHeading :: Int -> String -> IO ()
printSectionHeading indentation heading = do
    styledHeading <- styledText boldStyle heading
    putStrLn $ indent indentation styledHeading


printExpressionField :: Int -> String -> String -> IO ()
printExpressionField indentation label expression = do
    putStrLn $ indent indentation (label ++ ":")
    printTextBlock (indentation + 2) expression


printInlineOrBlock :: Int -> String -> String -> IO ()
printInlineOrBlock indentation prefix text =
    case nonEmptyLines text of
        [singleLine] ->
            putStrLn $ indent indentation (prefix ++ singleLine)
        textLines -> do
            putStrLn $ indent indentation (dropWhileEnd (== ' ') prefix)
            mapM_ (putStrLn . indent (indentation + 2)) textLines


printStyledInlineOrBlock :: [SGR] -> Int -> String -> String -> IO ()
printStyledInlineOrBlock style indentation prefix text =
    case nonEmptyLines text of
        [singleLine] ->
            styledText style (prefix ++ singleLine)
                >>= putStrLn . indent indentation
        textLines -> do
            styledText style (dropWhileEnd (== ' ') prefix)
                >>= putStrLn . indent indentation
            mapM_ (printStyledLine style (indentation + 2)) textLines


printSecondaryLine :: Int -> String -> IO ()
printSecondaryLine = printStyledLine normalStyle


printStyledLine :: [SGR] -> Int -> String -> IO ()
printStyledLine style indentation text =
    styledText style text >>= putStrLn . indent indentation


printNumberedTextBlocks :: [SGR] -> Int -> [(Int, String)] -> IO ()
printNumberedTextBlocks style indentation entries =
    case entries of
        [] -> pure ()
        (index, "true") : remainingEntries -> do
            let (remainingTrueEntries, rest) =
                    span ((== "true") . snd) remainingEntries
                finalIndex =
                    case reverse remainingTrueEntries of
                        [] -> index
                        (lastIndex, _) : _ -> lastIndex
                indexLabel =
                    if finalIndex == index
                        then show index
                        else show index ++ "-" ++ show finalIndex
            printStyledLine style indentation (indexLabel ++ ". true")
            printNumberedTextBlocks style indentation rest

        (index, text) : remainingEntries -> do
            printStyledInlineOrBlock style indentation (show index ++ ". ") text
            printNumberedTextBlocks style indentation remainingEntries


printTextBlock :: Int -> String -> IO ()
printTextBlock indentation text =
    mapM_ (putStrLn . indent indentation) (nonEmptyLines text)


nonEmptyLines :: String -> [String]
nonEmptyLines text =
    case lines text of
        [] -> [""]
        textLines -> textLines


expandConcreteArray ::
    IsSymExprBuilder sym =>
    sym ->
    ArrayRecord sym tp ->
    IO (Maybe [([Integer], Maybe (SymExpr sym tp))])
expandConcreteArray sym array =
    case traverse concreteBounds (arrayDimensions array) of
        Nothing -> pure Nothing
        Just bounds ->
            if arrayElementCount bounds > toInteger maximumExpandedArrayElements
                then pure Nothing
                else expandElements (enumerateIndices bounds)
  where
    expandElements indices =
        case indices of
            [] -> pure (Just [])
            currentIndices : remainingIndices -> do
                symbolicIndices <- mapM (intLit sym) currentIndices
                flatIndex <-
                    flattenArrayIndices
                        sym
                        (arrayDimensions array)
                        symbolicIndices
                initialised <-
                    arrayLookup
                        sym
                        (arrayInitMask array)
                        (Ctx.singleton flatIndex)
                case asConstantPred initialised of
                    Nothing -> pure Nothing
                    Just isInitialised -> do
                        maybeValue <-
                            if isInitialised
                                then
                                    Just
                                        <$> arrayLookup
                                            sym
                                            (arrayContents array)
                                            (Ctx.singleton flatIndex)
                                else pure Nothing
                        remainingElements <- expandElements remainingIndices
                        pure
                            ( fmap
                                ((currentIndices, maybeValue) :)
                                remainingElements
                            )


concreteBounds ::
    IsExpr (SymExpr sym) =>
    ArrayDimension sym ->
    Maybe (Integer, Integer)
concreteBounds dimension = do
    lower <- asInteger (dimensionLower dimension)
    upper <- asInteger (dimensionUpper dimension)
    pure (lower, upper)


enumerateIndices :: [(Integer, Integer)] -> [[Integer]]
enumerateIndices bounds =
    case bounds of
        [] -> [[]]
        (lower, upper) : remainingBounds ->
            [ index : remainingIndices
            | remainingIndices <- enumerateIndices remainingBounds
            , index <- [lower .. upper]
            ]


arrayElementCount :: [(Integer, Integer)] -> Integer
arrayElementCount =
    product
        . map
            (\(lower, upper) -> max 0 (upper - lower + 1))


maximumExpandedArrayElements :: Int
maximumExpandedArrayElements = 256


commaSeparated :: [String] -> String
commaSeparated values =
    case values of
        [] -> ""
        value : remainingValues ->
            value ++ concatMap (", " ++) remainingValues


stateCountHeading :: String -> Int -> String
stateCountHeading label stateCount =
    headingLabel ++ ": " ++ show stateCount
  where
    headingLabel =
        case words label of
            [] -> "States"
            firstWord : remainingWords ->
                unwords (capitalise firstWord : remainingWords) ++ " states"

    capitalise word =
        case word of
            [] -> []
            firstCharacter : remainingCharacters ->
                toUpper firstCharacter : remainingCharacters


numbered :: [value] -> [(Int, value)]
numbered = zip [1 ..]


indent :: Int -> String -> String
indent indentation text = replicate indentation ' ' ++ text


indentFollowingLines :: Int -> String -> String
indentFollowingLines indentation text =
    case lines text of
        [] -> ""
        firstLine : remainingLines ->
            firstLine
                ++ concatMap
                    (\line -> "\n" ++ indent indentation line)
                    remainingLines


dropTrailingColon :: String -> String
dropTrailingColon text =
    case reverse text of
        ':' : remainingCharacters -> reverse remainingCharacters
        _ -> text
