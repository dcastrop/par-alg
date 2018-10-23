module Main where

import System.Exit

import Test.HUnit

import qualified Test.Alg.Ppr

main :: IO ()
main = do
  c <- runTestTT $
      TestList [ Test.Alg.Ppr.tests
               ]

  print c
  if (errors c + failures c == 0)
    then exitWith ExitSuccess
    else exitWith (ExitFailure 1)
