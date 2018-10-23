module Main where

import System.Exit

import Test.HUnit

import qualified Test.Alg.Ppr
import qualified Test.Alg.Parser

main :: IO ()
main = do
  c <- runTestTT $
      TestList [ Test.Alg.Ppr.tests
               , Test.Alg.Parser.tests
               ]

  print c
  if (errors c + failures c == 0)
    then exitWith ExitSuccess
    else exitWith (ExitFailure 1)
