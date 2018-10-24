module Main where

import System.Environment
import System.Exit

import Language.Alg.C

compile :: FilePath -> IO ()
compile f = parseFile f >>= \(_st, p) ->
  printProg p

compileAll :: [FilePath] -> IO ()
compileAll [] = putStrLn "Error: unrecognised input" >>
  getProgName >>=
  putStrLn . usage >> exitWith (ExitFailure 1)
compileAll fs = mapM_ compile fs

main :: IO ()
main = getArgs >>= compileAll

usage :: String -> String
usage s = "Usage: " ++ s ++ " <file>..."
