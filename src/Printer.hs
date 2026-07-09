module Printer (showBinding, showSomeExpr, printState, printStates) where
    
import qualified Data.Map as Map

import Types

import What4.Interface

showBinding :: IsExpr (SymExpr sym) => VarBinding sym -> String
showBinding binding =
    case varValue binding of
        Nothing -> show (varType binding) ++ ", uninitialised"
        Just e -> show (varType binding) ++ ", initialised = " ++ showSomeExpr e

showSomeExpr :: IsExpr (SymExpr sym) => SomeExpr sym -> String
showSomeExpr expr =
    case expr of
        SomeInt e -> "int " ++ show (printSymExpr e)
        SomeReal e -> "real " ++ show (printSymExpr e)
        SomeBool p -> "bool " ++ show (printSymExpr p)


printStates :: IsExpr (SymExpr sym) => [SymState sym] -> IO ()
printStates states = do
    putStrLn ("Number of final states: " ++ show (length states))
    mapM_ printNumberedState (zip [(1 :: Int)..] states)
    where
        printNumberedState (i, state) = do
            putStrLn ("=== Final state " ++ show i ++ " ===")
            printState state

printState :: IsExpr (SymExpr sym) => SymState sym -> IO ()
printState state = do
    putStrLn "Environment:"

    if Map.null (env state)
        then putStrLn "  <empty>"
        else mapM_ printOne (Map.toList (env state))

    putStrLn "Path condition:"

    case pathCond state of
        [] -> putStrLn "  <true (empty pathCond list)>"
        ps -> mapM_ printPathPred ps
    
    putStrLn ""
    where
        printOne (name, binding) = putStrLn ("  " ++ name ++ " : " ++ showBinding binding)
        printPathPred p = putStrLn ("  " ++ show (printSymExpr p))