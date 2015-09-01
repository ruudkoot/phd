module Data.Set.Util (overlap, overlaps, unionMap) where

import qualified Data.List.Util as L
import qualified Data.Set       as S

overlap :: Ord a => S.Set a -> S.Set a -> Bool
overlap s t = not (S.null (S.intersection s t))

overlaps :: Ord a => [S.Set a] -> Bool
overlaps = or . L.pairwiseT overlap

unionMap :: (Ord a, Ord b) => (a -> S.Set b) -> S.Set a -> S.Set b
unionMap f = S.unions . map f . S.toList
