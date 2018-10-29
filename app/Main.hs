module Main where

import System.Environment
import System.Exit

import Language.Alg.C
import Language.Par.Prog


compile :: FilePath -> IO ()
compile f = do
  putStrLn $ "Compiling: " ++ f
  putStrLn "...parsing"
  t <- parseFile f
  putStrLn "...typechecking"
  (numRoles, _tyDefns, fnDefns) <- annotateProg <$> uncurry typecheck t
  putStrLn $ "...generated " ++ show numRoles ++ " potential distinct roles"
  printAnnProg fnDefns

compileAll :: [FilePath] -> IO ()
compileAll [] = putStrLn "Error: unrecognised input" >>
  getProgName >>=
  putStrLn . usage >> exitWith (ExitFailure 1)
compileAll fs = mapM_ compile fs

main :: IO ()
main = getArgs >>= compileAll

usage :: String -> String
usage s = "Usage: " ++ s ++ " <file>..."
