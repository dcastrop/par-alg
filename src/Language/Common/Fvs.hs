module Language.Common.Fvs
  ( Fvs (..)
  ) where

import Language.Common.Id
import Data.Set ( Set )
import qualified Data.Set as Set

class Fvs t where
  fvs :: t -> Set Id

instance Fvs Id where
  fvs = Set.singleton . id
