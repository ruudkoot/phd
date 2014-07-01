module Util.List where

{-# INLINE splice3 #-}
splice3 :: [a] -> ([a],[a],[a])
splice3 []           = ([],[],[])
splice3 [x]          = ([x],[],[])
splice3 [x,y]        = ([x],[y],[])
splice3 [x,y,z]      = ([x],[y],[x])
splice3 (x:y:z:xyzs) = let (xs,ys,zs) = splice3 xyzs in (x:xs,y:ys,z:zs)

{-# INLINE splice #-}
splice :: Int -> [a] -> [[a]]
splice n xs = let (xs', xss) = splitAt n xs
               in zipWith' (:) xs' (splice n xss ++ repeat [])

{-# INLINE zipWith' #-}
zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' f []     _       = []
zipWith' f (x:xs) ~(y:ys) = x `f` y : zipWith' f xs ys

{-# INLINE unzip4 #-}
unzip4 :: [(a, b, c, d)] -> ([a], [b], [c], [d])
unzip4 = foldr (\(a,b,c,d) ~(as,bs,cs,ds) -> (a:as,b:bs,c:cs,d:ds))
               ([],[],[],[])
