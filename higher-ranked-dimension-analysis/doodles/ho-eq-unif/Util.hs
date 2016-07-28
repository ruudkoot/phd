module Util where

import Data.Set (Set, toList, unions)

-- * Sets * ---------------------------------------------------------------[X]--

-- UNUSED
unionMap :: Ord b => (a -> Set b) -> Set a -> Set b
unionMap f ss = unions (map f (toList ss))

unionMap' :: Ord b => (a -> Set b) -> [a] -> Set b
unionMap' f ss = unions (map f ss)
