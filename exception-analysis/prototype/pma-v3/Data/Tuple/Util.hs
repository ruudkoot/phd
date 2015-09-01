module Data.Tuple.Util where

fst3 :: (a, b, c) -> a
fst3 (x, y, z) = x

snd3 :: (a, b, c) -> b
snd3 (x, y, z) = y

trd3 :: (a, b, c) -> c
trd3 (x, y, z) = z
