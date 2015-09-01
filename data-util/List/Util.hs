module Data.List.Util (pairwiseT, worklist) where

pairwiseT :: (a -> a -> b) -> [a] -> [b]
pairwiseT _ []        = []
pairwiseT f [x]       = [f x x]
pairwiseT f xxs@(x:_) = pairwiseT' xxs
    where pairwiseT' [x']           = [f x' x]
          pairwiseT' (x1:xs@(x2:_)) = f x1 x2 : pairwiseT' xs

-- worklist :: Foldable m => (a -> b -> (b, m a)) -> b -> m a -> b
worklist :: (a -> b -> (b, [a])) -> b -> [a] -> b
worklist (#) i []     = i
worklist (#) i (m:ms) = let (j, ns) = m # i in worklist (#) j (ms ++ ns)
