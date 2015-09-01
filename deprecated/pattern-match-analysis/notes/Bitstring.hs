module Main where

type Bitstring = [Int]

add :: Bitstring -> Bitstring -> Bitstring
add [] y = y
add x [] = x
add (0:x) (0:y) = 0 : add x y
add (0:x) (1:y) = 1 : add x y
add (1:x) (0:y) = 1 : add x y
add (1:x) (1:y) = 0 : add (add [1] x) y
