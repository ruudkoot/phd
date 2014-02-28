module FTV where

import qualified Data.Set        as S
import qualified Data.Set.Util   as S

import Names

-- * Free variables

class FTV a where
    ftv :: a -> S.Set Name
    
instance (FTV a, Ord a) => FTV (S.Set a) where
    ftv s = S.unionMap ftv s

