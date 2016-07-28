{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif.FirstOrder.AbelianGroups where

import Control.Applicative ((<$>))
import Control.Arrow ((***),(&&&))
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List

import           Data.Function
import           Data.Graph
import           Data.List      ( intersect, minimumBy, nub, partition, sort, sortBy
                                , zip4
                                )
import           Data.Maybe
import           Data.Map       (Map)
import qualified Data.Map       as Map
import           Data.Set       hiding (filter, foldr, map, partition, null)
import qualified Data.Set       as Set

import Unif.FirstOrder.Types

maximum' :: Ord a => a -> [a] -> a
maximum' x xs = maximum (x : xs)

-- * AG-unification with free nullary constants (unitary) * ---------------[X]--

-- Kennedy (1996) / Lankford, Butler & Brady (1984) + Knuth (1969)

data AG
    = Mul
    | Inv
    | Unit
  deriving (Eq, Bounded, Enum, Ord, Show)
  -- FIXME: arbitrary Ord for Set

count p = length . filter p

set :: [a] -> Int -> a -> [a]
set xs n x = let (xs1,_:xs2) = splitAt n xs in xs1 ++ [x] ++ xs2

divides :: Integral a => a -> a -> Bool
x `divides` y = y `mod` x == 0

type AGExp1   = ([Int],[Int])
type AGSubst1 = [AGExp1]

agIdSubst :: Int -> Int -> AGSubst1
agIdSubst m' n' = map idRow [0 .. m' - 1]
  where idRow x = (replicate x 0 ++ [1] ++ replicate (m' - x - 1) 0, replicate n' 0)

-- matrix-vector multiplication
agApplySubst :: AGSubst1 -> AGExp1 -> AGExp1
agApplySubst ss (ds@(length -> m'),bs) | length ss == m'
    = foldr f (replicate m' 0, bs) (zip ss ds)
        where f ((ds',bs'),d) (ds'',bs'')
                = (zipWith (\d' d'' -> d * d' + d'') ds' ds''
                  ,zipWith (\b' b'' -> d * b' + b'') bs' bs'')

-- matrix-matrix multiplication
agCompSubst :: AGSubst1 -> AGSubst1 -> AGSubst1
agCompSubst ss us = map (agApplySubst ss) us

-- FIXME: verify solution is valid
agUnif1 :: AGExp1 -> Maybe AGSubst1
agUnif1 delta@(xs@(length -> m'), ys@(length -> n')) =
    let m     = count (/= 0) xs
        n     = count (/= 0) ys
        (d,x) = minimumBy (compare `on` (abs . snd)) (filter ((/= 0) . snd) (zip [0..] xs))
     in case (m,n) of
            (0,0) -> Just (agIdSubst m' n')
            (0,_) -> Nothing
            (1,_) | all (x `divides`) ys -> Just $
                      set (agIdSubst m' n') d (replicate m' 0, map (\y -> -y `div` x) ys)
                  | otherwise            -> Nothing
            (_,_) -> do
                -- 'div' always rounds down (also for a negative lhs)
                let us = set (agIdSubst m' n') d
                             (set (map (\x' -> -(x' `div` x)) xs) d 1
                             ,     map (\y  -> -(y  `div` x)) ys     )
                ss <- agUnif1 (agApplySubst us delta)
                return $ agCompSubst ss us

-- solve a system of equations
-- FIXME: verify solution is valid
agUnif1' :: [AGExp1] -> Maybe AGSubst1
agUnif1' [x]    = agUnif1 x
agUnif1' (x:xs) = do s <- agUnif1 x
                     t <- agUnif1' (map (agApplySubst s) xs)
                     return $ agCompSubst t s

-- solve the constant matching problem
-- FIXME: verify solution is valid
agConstMatch :: AGExp1 -> AGExp1 -> Maybe AGSubst1
agConstMatch (vs1@(length -> m ), cs1@(length -> n ))
             (vs2@(length -> m'), cs2@(length -> n'))
  | m == m' && n == n'
    = let vs = vs1
          cs = zipWith (\c1 c2 -> c1 - c2) (cs1 ++ replicate m 0) (cs2 ++ vs2)
       in case agUnif1 (vs, cs) of
            Nothing    -> Nothing
            Just subst -> Just (map f subst)
                where f (vs, splitAt n -> (cs, cs')) = (zipWith (+) vs cs', cs)
  | otherwise = error "agConstMatch: m /= m' || n /= n'"

-- Solve a system of equations in AG, while treating a set of given variables as
-- constants.
agUnif1TreatingAsConstant
    :: TermAlg AG f' () Int
    => [T AG f' () Int]               -- set of marked variables SMV
    -> AGUnifProb AG f' () Int
    -> Maybe (AGUnifProb AG f' () Int)
agUnif1TreatingAsConstant smv p
    = let numV1  = maximum (map (\(s,t) -> max (numX  s) (numX  t)) p)
          numV2  = maximum (map (\(s,t) -> max (numX' s) (numX' t)) p)
          numC'  = 0 -- max (numC  s) (numC  t)
          p'     = map (constantify numC'  smv *** constantify numC' smv) p
          numC'' = maximum (map (\(s,t) -> max (numC  s) (numC  t)) p')
       in case agUnif1' (map (toExp' numV1 numV2 numC'') p') of
            Nothing -> Nothing
            Just agSubst -> Just $ map (deconstantify numC' *** deconstantify numC')
                                       (fromExp numV1 agSubst)
       
constantify
    :: TermAlg AG f' Int Int
    => Int
    -> [T AG f' () Int]
    -> T AG f' () Int
    -> T AG f' Int Int
constantify numC' smv = constantify'
  where
    constantify' (X  x    ) | X  x  `elem` smv = C (numC' + 2 * x)
                            | otherwise        = X x
    constantify' (X' x'   ) | X' x' `elem` smv = C (numC' + 2 * x' + 1)
                            | otherwise        = X' x'
    constantify' (C  c    ) = error "constantify'" -- C  c
    constantify' (F  f  ts) = F  f  (map constantify' ts)
    constantify' (F' f' ts) = F' f' (map constantify' ts)
    
deconstantify
    :: TermAlg AG f' Int Int
    => Int
    -> T AG f' Int Int
    -> T AG f' () Int
deconstantify numC' = deconstantify'
  where
    deconstantify' (X  x ) = X  x
    deconstantify' (X' x') = X' x'
    deconstantify' (C  c ) | c < numC'                        = error "deconstantify'"
                                                           -- = C  c
                           | (x ,0) <- (c - numC') `divMod` 2 = X  x
                           | (x',1) <- (c - numC') `divMod` 2 = X' x'
    deconstantify' (F  f  ts) = F  f  (map deconstantify' ts)
    deconstantify' (F' f' ts) = F' f' (map deconstantify' ts)
    
    
-------------------------------------------------------------------------------


numX :: T f f' c Int -> Int
numX (X  x   ) = x + 1
numX (X' _   ) = 0
numX (C  _   ) = error "numX: C" -- 0
numX (F  _ ts) = maximum' 0 (map numX ts)
numX (F' _ ts) = maximum' 0 (map numX ts)

numX' :: T f f' c x -> Int
numX' (X  _   ) = 0
numX' (X' x'  ) = x' + 1
numX' (C  _   ) = error "numX': C" -- 0
numX' (F  _ ts) = maximum' 0 (map numX' ts)
numX' (F' _ ts) = maximum' 0 (map numX' ts)

numC :: T f f' Int x -> Int
numC (X  _   ) = 0
numC (X' _   ) = 0
numC (C  c   ) = c + 1
numC (F  _ ts) = maximum' 0 (map numC ts)
numC (F' _ ts) = maximum' 0 (map numC ts)

castC :: T f f' () x -> T f f' c x
castC (X  x    ) = X  x
castC (X' x'   ) = X' x'
castC (C  c    ) = error "castC: C"
castC (F  f  ts) = F  f  (map castC ts)
castC (F' f' ts) = F' f' (map castC ts)

castC' :: T f f' c x -> T f f' () x
castC' (X  x    ) = X  x
castC' (X' x'   ) = X' x'
castC' (C  c    ) = error "castC': C"
castC' (F  f  ts) = F  f  (map castC' ts)
castC' (F' f' ts) = F' f' (map castC' ts)

toExp :: Int -> Int -> Int -> T AG f' () Int -> AGExp1
toExp v1 v2 c s = toExp' v1 v2 c (castC s, F Unit [])

toExp' :: Int -> Int -> Int -> (T AG f' Int Int, T AG f' Int Int) -> AGExp1
toExp' v1 v2 c (s,t) = mul (toExp'' s) (inv (toExp'' t))
  where
    toExp'' (X  x           ) = let (vs,cs) = unit in (set vs       x   1, cs)
    toExp'' (X' x'          ) = let (vs,cs) = unit in (set vs (v1 + x') 1, cs)
    toExp'' (C  c           ) = let (vs,cs) = unit in (vs, set cs c 1)
    toExp'' (F  Unit [     ]) = unit
    toExp'' (F  Inv  [t    ]) = inv (toExp'' t)
    toExp'' (F  Mul  [t1,t2]) = mul (toExp'' t1) (toExp'' t2)

    unit = (replicate (v1 + v2) 0, replicate c 0)
    inv  = map negate *** map negate
    mul (xs,xs') (ys,ys') = (zipWith (+) xs ys, zipWith (+) xs' ys')
    

fromExp :: Int -> AGSubst1 -> AGUnifProb AG f' Int Int
fromExp v1 ss@(length -> v)
    = zipWith (\x t -> (x, fromExp' t)) (map X [0 .. v1 - 1] ++ map X' [0 .. v - v1]) ss
  where
    fromExp' :: AGExp1 -> T AG f' Int Int
    fromExp' (splitAt v1 -> (vs,vs'),cs)
        = let xs =    map (fromExp'' X ) (filter ((/=0) . snd) (zip [0 .. v1]     vs ))
                   ++ map (fromExp'' X') (filter ((/=0) . snd) (zip [0 .. v - v1] vs'))
                   ++ map (fromExp'' C ) (filter ((/=0) . snd) (zip [0 .. ]       cs ))
           in case xs of
                [] -> F Unit []
                _  -> foldr1 (\x y -> F Mul [x,y]) xs

    fromExp'' :: (Int -> T AG f' Int Int) -> (Int, Int) -> T AG f' Int Int
    fromExp'' con (x,n)
        | n < 0     = F Inv [fromExp'' con (x,-n)]
        | otherwise = foldr1 (\_ y -> F Mul [con x,y]) (replicate n (con x))

