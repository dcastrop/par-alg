{-# OPTIONS_GHC -threaded #-}
module Main where

import Data.Complex
import Control.Monad
import Control.DeepSeq
import Data.List ( sort )
import Data.Vector  ( Vector )
import qualified Data.Vector as V
import System.Random ( randomRIO )
import Statistics.Types
import System.Clock

import Criterion.Main
import Criterion.Types

import AlgPrelude
import DotProd

ensure :: NFData a => a -> IO a
ensure xs = xs `deepseq` return xs


range       = [ 2 ^ sizeLow
              , 2 ^ (sizeLow + 1)
              , 2 ^ (sizeLow + 2)
              , 2 ^ (sizeLow + 3)
              , 2 ^ (sizeLow + 4)
              , 2 ^ (sizeLow + 5)
              , 2 ^ (sizeLow + 6)
              , 2 ^ (sizeLow + 7)
              , 2 ^ (sizeLow + 8)
              , 2 ^ (sizeLow + 9)
              , 2 ^ (sizeLow + 10)
              ]
step        = sizeLow `div` 10
numSteps    = 10
randList n  = replicateM n $ randomRIO (minBound, maxBound :: Int)
sizeLow     = 10

main = cmain -- msMain 100000

msMain sz = do
  l <- randList sz
  t'init <- getTime Realtime
  dotp l >>= ensure
  t'last <- getTime Realtime
  print $ t'last - t'init


config = defaultConfig
  { resamples = 30
  , confInterval = cl99
  , timeLimit = 60
  }

mkEnv = mapM randList range

cmain =
  defaultMainWith config
      [ env mkEnv mkMsBench
      , env mkEnv mkSqBench
      ]
  where
    mkMsBench l = bgroup "par" $ take (length range) $ go l
      where
        go ~(l:t) = bench (show $ length l) (nfIO $ dotp l) : go t
    mkSqBench l = bgroup "seq" $ take (length range) $ go l
      where
        go ~(l:t) = bench (show $ length l) (nf dotHs l) : go t
