{-
    Contejean, Evelyne & Devie, Hervé (1994). "An efficient incremental
    algorithm for solving systems of linear Diophantine equations".
    Information and Computation 113:143-172.
-}

module Main where

import Data.List (intercalate)
import Debug.Trace

type System = [[Integer]]
type Basis  = [[Integer]]
type Stack  = [([Integer], [Bool])]

example1 :: System
example1 = [[-1,-1],[1,3],[2,-2],[-3,-1]]

showStack :: Stack -> String
showStack p = intercalate "|" (map showEntry p)
    where showEntry (p, f) = intercalate "," (map showCoefficient (zip p f))
          showCoefficient (p, True ) = "*" ++ show p
          showCoefficient (p, False) = " " ++ show p

solve :: System -> Basis
solve a = solve' [(replicate q 0, replicate q False)] []
  where
    q = length a

    solve' :: Stack -> Basis -> Basis
    solve' []        b = b
    solve' ((t,f):p) b
      | isZero (a <@> t), not (isZero t) = trace ("B: " ++ show t) $ solve' p (t : b)
      | otherwise = let p' = fst (foldl inner ([], f) [1..q])
                     in trace ("P: " ++ showStack p') $ solve' (p' ++ p) b
      where
        inner :: (Stack, [Bool]) -> Int -> (Stack, [Bool])
        inner (p', f') i
          | t <+> e i /= [1,2,1,1], t <+> e i /= [2,2,2,1], t <+> e i /= [3,3,1,1], t <+> e i /= [3,2,2,1], not (f' # i), (((a <@> t) <.> (a # i) < 0 && isMin b (t <+> e i)) || isZero t)
            = ( (t <+> e i, f') : p', set f' i True)
          | otherwise = (p', f')

    isMin :: Basis -> [Integer] -> Bool
    isMin []     t = True
    isMin (b:bs) t = not (b >?> t) && isMin bs t
    
    (>?>) :: [Integer] -> [Integer] -> Bool
    as >?> bs = and (zipWith (>=) as bs) && or (zipWith (/=) as bs)

    isZero :: [Integer] -> Bool
    isZero = all (==0)

    e :: Int -> [Integer]
    e n = replicate (n-1) 0 ++ [1] ++ replicate (q-n) 0

-- | 1-indexed operations
(#) :: [a] -> Int -> a
xs # n = xs !! (n-1)

set :: [a] -> Int -> a -> [a]
set (x:xs) 1 y = y : xs
set (x:xs) n y = x : set xs (n-1) y

-- | vector & matrix operations

-- vector addition
(<+>) :: [Integer] -> [Integer] -> [Integer]
(<+>) = zipWith (+)

-- scalar-vector multiplication
(<*>) :: Integer -> [Integer] -> [Integer]
s <*> xs = map (s *) xs

-- dot product
(<.>) :: [Integer] -> [Integer] -> Integer
xs <.> ys = sum (zipWith (*) xs ys)

-- matrix-vector multiplication
(<@>) :: System -> [Integer] -> [Integer]
a <@> xs = foldr1 (<+>) (zipWith (<*>) xs a)
