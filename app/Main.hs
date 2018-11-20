{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}
module Main where

import Data.Typeable
import Data.Data
import Data.Char
import System.Environment
import System.Console.CmdArgs
import System.FilePath.Posix

import Language.Alg.C
import Language.Alg.Typecheck
import Language.Alg.Internal.TcM
-- import Language.Alg.Internal.Ppr
import Language.Par.Prog
import Language.Ept.EMonad

stdPrelude :: String
stdPrelude = "AlgPrelude.hs"

logInfo :: String -> IO ()
logInfo = whenLoud . putStrLn

logError :: String -> IO ()
logError = putStrLn

output :: String -> IO ()
output = whenNormal . putStrLn

compile :: Flags -> FilePath -> IO ()
compile flg f = do
  logInfo $ "Compiling: " ++ f
  logInfo "...parsing"
  t <- parseFile f
  logInfo "...typechecking"
  (tcSt@TcSt { nextRole = numRoles }, pr1) <- uncurry typecheck t
  logInfo $ "...generated " ++ show numRoles ++ " potential distinct roles"
  let (fnm, _ext) = splitExtension f
  writeFile (fnm ++ ".proto") $ renderProg $ wtPDefs pr1
  logInfo "...compiling to monadic code"
  (_, parProg) <- generate tcSt pr1
  writeFile (capitalise fnm ++ ".hs") $
    renderPCode
      (takeBaseName $ maybe stdPrelude id $ prelude flg)
      (takeBaseName $ atoms flg)
      (capitalise $ takeBaseName f) parProg
  where
    capitalise [] = []
    capitalise (h : t) = toUpper h : t

compileAll :: Flags -> IO ()
compileAll f@Flags { files = fl } = compile f fl

data Flags
  = Flags
  { num_procs :: Int
  , prelude   :: Maybe FilePath
  , atoms     :: FilePath
  , gen_atoms :: Bool
  , files     :: FilePath
  } deriving (Show, Data, Typeable)

flags :: String -> Flags
flags p
  = Flags
  { num_procs = 1 &= help "Maximum number of roles"
  , prelude = Nothing &= opt stdPrelude &= typFile &= help "Generate `Alg` Prelude"
  , atoms = "Atoms.hs" &= typFile &= help "The 'atoms' module"
  , gen_atoms = False &= help "Generate 'atoms' module"
  , files = def &= args &= typFile
  }
  &= verbosity
  &= summary (p ++ " compiler")
  &= program p

main :: IO ()
main = do
  p <- getProgName
  f <- cmdArgs $ flags p
  maybe (pure ())  (\fn -> writeFile fn $ renderPrelude $ takeBaseName fn) $ prelude f
  compileAll f

usage :: String -> String
usage s = "Usage: " ++ s ++ " <file>..."
