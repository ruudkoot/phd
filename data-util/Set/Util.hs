module Data.Set.Util (all, overlap, overlaps, unionMap, showSet) where

import Prelude hiding (all)

import qualified Data.List.Util as L
import qualified Data.Set       as S

all :: Ord a => (a -> Bool) -> S.Set a -> Bool
all p = S.foldr (\x r -> p x && r) True

overlap :: Ord a => S.Set a -> S.Set a -> Bool
overlap s t = not (S.null (S.intersection s t))

overlaps :: Ord a => [S.Set a] -> Bool
overlaps = or . L.pairwiseT overlap

unionMap :: (Ord a, Ord b) => (a -> S.Set b) -> S.Set a -> S.Set b
unionMap f = S.unions . map f . S.toList

showSet :: Show a => S.Set a -> String
showSet s = "{" ++ drop 10 (init (show s)) ++ "}"
