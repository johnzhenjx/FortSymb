{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Printer where

import qualified Data.Map as Map

import Types
import Arrays
import What4.Interface

import What4.Expr
         ( ExprBuilder )


showSymExpr :: IsExpr expr => expr tp -> String
showSymExpr = show . printSymExpr


showBinding :: IsExpr (SymExpr sym) =>
    VarBinding sym ->
    String
showBinding binding =
    show (varType binding)
        ++ case varValue binding of
            Nothing ->
                ", uninitialised"

            Just value ->
                ", initialised = " ++ showSomeExpr value


showSomeExpr :: IsExpr (SymExpr sym) => SomeExpr sym -> String
showSomeExpr value =
    case value of
        SomeInt expression ->
            "int " ++ showSymExpr expression

        SomeReal expression ->
            "real " ++ showSymExpr expression

        SomeBool predicate ->
            "bool " ++ showSymExpr predicate

        SomeIntArray arrayRecord ->
            showArrayRecord "integer" arrayRecord

        SomeRealArray arrayRecord ->
            showArrayRecord "real" arrayRecord

        SomeBoolArray arrayRecord ->
            showArrayRecord "logical" arrayRecord
    

showArrayRecord ::
    IsExpr (SymExpr sym) =>
    String ->
    ArrayRecord sym tp ->
    String
showArrayRecord elementType arrayRecord =
    elementType
        ++ " array"
        -- ++ "\n    rank: "
        -- ++ show (length dimensions)
        ++ "\n    dimensions:"
        ++ showArrayDimensions dimensions
        ++ "\n    contents: "
        ++ showSymExpr (arrayContents arrayRecord)
        ++ "\n    initialisation mask: "
        ++ showSymExpr (arrayInitMask arrayRecord)
  where
    dimensions = arrayDimensions arrayRecord

showArrayDimensions ::
    IsExpr (SymExpr sym) =>
    [ArrayDimension sym] ->
    String
showArrayDimensions [] =
    " none"

showArrayDimensions dimensions =
    concatMap showNumberedDimension (zip [1 :: Int ..] dimensions)
  where
    showNumberedDimension (dimensionNumber, dimension) =
        "\n        "
            ++ show dimensionNumber
            ++ ". lower = "
            ++ showSymExpr (dimensionLower dimension)
            ++ ", upper = "
            ++ showSymExpr (dimensionUpper dimension)


printStates ::
    IsExpr (SymExpr sym) =>
    [SymState sym a] ->
    IO ()
printStates states = do
    putStrLn ("Number of states: " ++ show (length states))
    putStrLn ""

    mapM_
        printNumberedState
        (zip [(1 :: Int) ..] states)
  where
    printNumberedState (index, state) = do
        putStrLn ("=== State " ++ show index ++ " ===")
        printState state


printState ::
    IsExpr (SymExpr sym) =>
    SymState sym a ->
    IO ()
printState state = do
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

    case Map.toList (env state) of
        [] ->
            putStrLn "  <empty>"

        bindings ->
            mapM_ printBinding bindings
  where
    printBinding (name, binding) =
        putStrLn
            ( "  "
                ++ name
                ++ " : "
                ++ showBinding binding
            )


printPredicates ::
    IsExpr expr =>
    String ->
    String ->
    [expr BaseBoolType] ->
    IO ()
printPredicates heading emptyMessage predicates = do
    putStrLn heading

    case predicates of
        [] ->
            putStrLn ("  " ++ emptyMessage)

        _ ->
            mapM_
                printNumberedPredicate
                (zip [(1 :: Int) ..] predicates)
  where
    printNumberedPredicate (index, predicate) =
        putStrLn
            ( "  "
                ++ show index
                ++ ". "
                ++ showSymExpr predicate
            )


printObligations ::
    IsExpr (SymExpr sym) =>
    [Obligation sym] ->
    IO ()
printObligations obligationsToPrint = do
    putStrLn "Proof obligations:"

    case obligationsToPrint of
        [] ->
            putStrLn "  <none>"

        _ ->
            mapM_
                printNumberedObligation
                (zip [(1 :: Int) ..] obligationsToPrint)
  where
    printNumberedObligation (index, obligation) = do
        putStrLn
            ( "  "
                ++ show index
                ++ ". "
                ++ show (obligationKind obligation)
            )

        putStrLn
            ( "     Predicate: "
                ++ showSymExpr (obligationPredicate obligation)
            )

        putStrLn "     Path at generation:"

        case reverse (obligationPath obligation) of
            [] ->
                putStrLn "       <true>"

            predicates ->
                mapM_
                    printPathPredicate
                    (zip [(1 :: Int) ..] predicates)

    printPathPredicate (index, predicate) =
        putStrLn
            ( "       "
                ++ show index
                ++ ". "
                ++ showSymExpr predicate
            )



printAllObligationResults ::
    [ [ ( Obligation (ExprBuilder t st fs)
        , ObligationResult
        )
      ]
    ] ->
    IO ()
printAllObligationResults stateResults =
    printStateResults 1 stateResults
  where
    printStateResults stateNumber remainingStateResults =
        case remainingStateResults of
            [] ->
                pure ()

            results : laterResults -> do
                putStrLn
                    ("=== Obligation results for state "
                        ++ show stateNumber
                        ++ " ==="
                    )

                printObligationResults 1 results

                putStrLn ""

                printStateResults
                    (stateNumber + 1)
                    laterResults

    printObligationResults obligationNumber remainingResults =
        case remainingResults of
            [] ->
                putStrLn "  <none>"

            (obligation, result) : laterResults -> do
                putStrLn
                    ( "  "
                        ++ show obligationNumber
                        ++ ". "
                        ++ show (obligationKind obligation)
                        ++ ": "
                        ++ resultSummary result
                    )

                case result of
                    ObligationValid ->
                        pure ()

                    ObligationInvalid counterexample ->
                        printStoredCounterexample
                            counterexample

                printObligationResults
                    (obligationNumber + 1)
                    laterResults

    resultSummary result =
        case result of
            ObligationValid ->
                "Valid"

            ObligationInvalid _ ->
                "Invalid"

    printStoredCounterexample counterexample =
        case Map.toList counterexample of
            [] ->
                putStrLn "     Counterexample: <empty>"

            variables -> do
                putStrLn "     Counterexample:"
                printVariables variables

    printVariables variables =
        case variables of
            [] ->
                pure ()

            (name, maybeValue) : remainingVariables -> do
                putStrLn
                    ( "       "
                        ++ name
                        ++ " = "
                        ++ case maybeValue of
                            Nothing ->
                                "<uninitialised>"

                            Just value ->
                                value
                    )

                printVariables remainingVariables