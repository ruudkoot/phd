module Data.List.Util (pairwiseT) where

pairwiseT :: (a -> a -> b) -> [a] -> [b]
pairwiseT _ []        = []
pairwiseT f [x]       = [f x x]
pairwiseT f xxs@(x:_) = pairwiseT' xxs
    where pairwiseT' [x']           = [f x' x]
          pairwiseT' (x1:xs@(x2:_)) = f x1 x2 : pairwiseT' xs
