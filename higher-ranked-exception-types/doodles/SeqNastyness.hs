{-# LANGUAGE RankNTypes #-}

module Main where

-- | mapSeq

mapSeq :: (a -> b) -> [a] -> [b]
mapSeq _ []     = []
mapSeq f (x:xs) = f `seq` f x : mapSeq f xs

test1 = mapSeq id [1..9]
test2 = mapSeq id (map (error . show) [1..9])
test3 = mapSeq id ([1..4] ++ error "[5]" ++ [6..9])
test4 = mapSeq (const 0) [1..9]
test5 = mapSeq (const 0) (map (error . show) [1..9])
test6 = mapSeq (const 0) ([1..4] ++ error "[5]" ++ [6..9])
test7 = mapSeq (error "f") [1..9]
test8 = mapSeq (error "f") (map (error . show) [1..9])
test9 = mapSeq (error "f") ([1..4] ++ error "[5]" ++ [6..9])

test7_ = map (error "f") [1..9]
test8_ = map (error "f") (map (error . show) [1..9])
test9_ = map (error "f") ([1..4] ++ error "[5]" ++ [6..9])


test1' = length test1
test2' = length test2
test3' = length test3
test4' = length test4
test5' = length test5
test6' = length test6
test7' = length test7
test8' = length test8
test9' = length test9

test7_' = length test7_
test8_' = length test8_
test9_' = length test9_

-- | Polymorphic types

constSeq :: a -> b -> b
constSeq x y = x `seq` y

-- | Higher-ranked polymorphic types

rank2Seq :: (forall a. a) -> b
rank2Seq x = x `seq` error "b"

-- | Lambdas

flipConstSeq :: a -> b -> a
flipConstSeq = \x -> x `seq` (\y -> x)
