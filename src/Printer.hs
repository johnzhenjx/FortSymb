{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Printer where

import qualified Data.Map as Map

import Arrays
import Types

import What4.Expr
    ( ExprBuilder
    )
import What4.Interface
    ( BaseBoolType
    , IsExpr
    , SymExpr
    , printSymExpr
    )


showSymExpr :: IsExpr expr => expr tp -> String
showSymExpr =
    show . printSymExpr


showBinding ::
    IsExpr (SymExpr sym) =>
    VarBinding sym ->
    String
showBinding binding =
    show (varType binding)
        ++ case varValue binding of
            Nothing ->
                ", uninitialised"

            Just value ->
                ", initialised = " ++ showSomeExpr value


showSomeExpr ::
    IsExpr (SymExpr sym) =>
    SomeExpr sym ->
    String
showSomeExpr value =
    case value of
        SomeInt expression ->
            "int " ++ showSymExpr expression

        SomeReal expression ->
            "real " ++ showSymExpr expression

        SomeBool predicate ->
            "bool " ++ showSymExpr predicate

        SomeIntArray array ->
            showArrayRecord "integer" array

        SomeRealArray array ->
            showArrayRecord "real" array

        SomeBoolArray array ->
            showArrayRecord "logical" array


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
        [] ->
            " none"

        _ ->
            concatMap showDimension (numbered dimensions)
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
        ExecutionComplete ->
            "Complete"

        ExecutionHalted reason ->
            "Halted: " ++ showHaltReason reason


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

        ObligationCannotHold kind ->
            "obligation cannot hold: " ++ show kind

printStates ::
    IsExpr (SymExpr sym) =>
    [SymState sym a] ->
    IO ()
printStates states = do
    putStrLn $ "Number of states: " ++ show (length states)
    putStrLn ""

    mapM_ printNumberedState (numbered states)
  where
    printNumberedState (index, state) = do
        putStrLn $ "=== State " ++ show index ++ " ==="
        printState state


printState ::
    IsExpr (SymExpr sym) =>
    SymState sym a ->
    IO ()
printState state = do
    putStrLn $ "Execution status: " ++ showExecutionStatus (executionStatus state)

    printEnvironment state

    printPredicates
        "Path conditions:"
        "<true>"
        (reverse (pathCond state))

    printObligations
        (reverse (obligations state))

    putStrLn ""


printEnvironment ::
    IsExpr (SymExpr sym) =>
    SymState sym a ->
    IO ()
printEnvironment state = do
    putStrLn "Environment:"

    printCollection
        "  <empty>"
        printBinding
        (Map.toList (env state))
  where
    printBinding (name, binding) =
        putStrLn $
            "  "
                ++ name
                ++ " : "
                ++ indentFollowingLines 4 (showBinding binding)


printPredicates ::
    IsExpr expr =>
    String ->
    String ->
    [expr BaseBoolType] ->
    IO ()
printPredicates heading emptyMessage predicates = do
    printPredicatesAt 0 heading emptyMessage predicates


printPredicatesAt ::
    IsExpr expr =>
    Int ->
    String ->
    String ->
    [expr BaseBoolType] ->
    IO ()
printPredicatesAt indentation heading emptyMessage predicates = do
    putStrLn $ indent indentation heading

    printCollection
        (indent (indentation + 2) emptyMessage)
        printPredicate
        (numbered predicates)
  where
    printPredicate (index, predicate) =
        putStrLn $
            indent (indentation + 2) ""
                ++ show index
                ++ ". "
                ++ showSymExpr predicate


printObligations ::
    IsExpr (SymExpr sym) =>
    [Obligation sym] ->
    IO ()
printObligations obligationsToPrint = do
    putStrLn "Proof obligations:"

    printCollection
        "  <none>"
        printObligation
        (numbered obligationsToPrint)
  where
    printObligation (index, obligation) = do
        putStrLn $
            "  "
                ++ show index
                ++ ". "
                ++ show (obligationKind obligation)

        putStrLn $
            "    Predicate: "
                ++ showSymExpr (obligationPredicate obligation)

        printPredicatesAt
            4
            "Path at generation:"
            "<true>"
            (reverse (obligationPath obligation))


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
        putStrLn $
            "=== Obligation results for state "
                ++ show stateNumber
                ++ " ==="

        printCollection
            "  <none>"
            printObligationResult
            (numbered results)

        putStrLn ""

    printObligationResult
        ( obligationNumber
        , (obligation, result)
        ) = do
            putStrLn $
                "  "
                    ++ show obligationNumber
                    ++ ". "
                    ++ show (obligationKind obligation)
                    ++ ": "
                    ++ showObligationResult result

            case result of
                ObligationValid ->
                    pure ()

                ObligationInvalid counterexample ->
                    printCounterexample counterexample


showObligationResult :: ObligationResult -> String
showObligationResult result =
    case result of
        ObligationValid ->
            "Valid"

        ObligationInvalid _ ->
            "Invalid"


printCounterexample :: Counterexample -> IO ()
printCounterexample counterexample =
    case Map.toList counterexample of
        [] ->
            putStrLn "    Counterexample: <empty>"

        variables -> do
            putStrLn "    Counterexample:"

            mapM_
                printVariable
                variables
  where
    printVariable (name, maybeValue) =
        putStrLn $
            "      "
                ++ name
                ++ " = "
                ++ maybe "<uninitialised>" id maybeValue


printCollection ::
    String ->
    (value -> IO ()) ->
    [value] ->
    IO ()
printCollection emptyMessage printValue values =
    case values of
        [] ->
            putStrLn emptyMessage

        _ ->
            mapM_ printValue values


numbered :: [value] -> [(Int, value)]
numbered =
    zip [1 ..]


indent :: Int -> String -> String
indent indentation text =
    replicate indentation ' ' ++ text


indentFollowingLines :: Int -> String -> String
indentFollowingLines indentation text =
    case lines text of
        [] -> ""
        firstLine : remainingLines ->
            firstLine
                ++ concatMap
                    (\line -> "\n" ++ indent indentation line)
                    remainingLines
