{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}
module Main where

import Data.Typeable
import Data.Data
import System.Environment
import System.Console.CmdArgs

import Language.Alg.C
import Language.Alg.Typecheck
import Language.Alg.Internal.TcM
import Language.Par.Prog
import Language.Ept.EMonad

logInfo :: String -> IO ()
logInfo = whenLoud . putStrLn

logError :: String -> IO ()
logError = putStrLn

output :: String -> IO ()
output = whenNormal . putStrLn

compile :: Flags -> FilePath -> IO ()
compile Flags { recursion_depth = d } f = do
  logInfo $ "Compiling: " ++ f
  logInfo "...parsing"
  t <- parseFile f
  logInfo "...typechecking"
  (tcSt@TcSt { nextRole = numRoles }, _tyDefns, fnDefns) <- uncurry (typecheck d) t
  logInfo $ "...generated " ++ show numRoles ++ " potential distinct roles"
  output $ renderProg fnDefns
  logInfo "...compiling to monadic code"
  (_, parProg) <- generate tcSt fnDefns
  output $ renderPCode parProg

compileAll :: Flags -> IO ()
compileAll f@Flags { files = fl } = mapM_ (compile f) fl

data Flags
  = Flags
  { recursion_depth :: Int
  , num_procs :: Int
  , files :: [FilePath]
  } deriving (Show, Data, Typeable)

flags :: String -> Flags
flags p
  = Flags
  { recursion_depth = 0 &= help "Unroll recursive functions up to a maximum depth"
  , num_procs = 1 &= help "Maximum number of roles"
  , files = def &= args &= typFile
  }
  &= verbosity
  &= summary (p ++ " compiler")
  &= program p

main :: IO ()
main = do
  p <- getProgName
  f <- cmdArgs $ flags p
  compileAll f

usage :: String -> String
usage s = "Usage: " ++ s ++ " <file>..."
