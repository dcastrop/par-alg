{-# OPTIONS_GHC -threaded #-}
{-# LANGUAGE TupleSections #-}
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
import Atoms
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
randPairL n = Pair2 <$!> (toL1 <$!> randList n) <*> (toL1 <$!> randList n)
sizeLow     = 10

main = cmain -- msMain 100000

msMain sz = do
  l <- randPairL sz
  t'init <- getTime Realtime
  dotpar (rzip l) >>= ensure
  t'last <- getTime Realtime
  print $ t'last - t'init


config = defaultConfig
  { resamples = 30
  , confInterval = cl99
  , timeLimit = 60
  }

mkEnv = mapM (\i -> (i,) <$!> randPairL i) range

cmain =
  defaultMainWith config
      [ env mkEnv mkMsBench
      , env mkEnv mkSqBench
      ]
  where
    mkMsBench l = bgroup "par" $ take (length range) $ go l
      where
        go ~(l:t) = bench (show $ fst l) (nfIO $ dotpar $ rzip $ snd l) : go t
    mkSqBench l = bgroup "seq" $ take (length range) $ go l
      where
        go ~(l:t) = bench (show $ fst l) (nf dot $ snd l) : go t
