module Main where

-- Dussart, Mossin & Henglein
f1 x y   = if x then True else f1 y x
f2 x y z = if x then True else f2 z x y

-- Glenn, Stuckey & Sulzmann
h1 x y b = if b then x else h1 x (h1 y x b) b
h2 x y b = if b then x else h2 (h2 y x (not b)) x (not b)
