{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif.FirstOrder.Free (
    freeUnif
) where

import Control.Arrow ((***))
import Data.Function (on)
import Data.List     (sortBy)

import Unif.FirstOrder.Types

freeUnif
    :: TermAlg f f' c Int
    => FOUnifProb f f' c Int
    -> Maybe (FOUnifProb f f' c Int)
freeUnif = freeUnif' []
  where

    freeUnif' sol [] = Just (sortBy (compare `on` fst) sol)
    
    freeUnif' sol ((F' f1 ts1, F' f2 ts2):prob)
        -- Decompose
        | f1 == f2  = freeUnif' sol (zip ts1 ts2 ++ prob)
        -- Clash
        | otherwise = Nothing

    -- Orient
    freeUnif' sol ((X x1, X' x2) : prob)
        = freeUnif' sol ((X' x2, X x1) : prob)
    freeUnif' sol ((t@(F' _ _),x@(X _)) : prob)
        = freeUnif' sol ((x,t) : prob)
    freeUnif' sol ((t@(F' _ _),x@(X' _ )) : prob)
        = freeUnif' sol ((x,t) : prob)

    freeUnif' sol (p@(X' x1, X x2) : prob)
        -- Elimintate
        = freeUnif' (p : elim sol) (elim prob)
            where elim = map (subst' x1 (X' x2) *** subst' x1 (X' x2))

    freeUnif' sol (p@(X x1, X x2) : prob)
        -- Delete
        | x1 == x2  = freeUnif' sol prob
        -- Eliminate
        | otherwise = freeUnif' (p : elim sol) (elim prob)
            where elim = map (subst x1 (X x2) *** subst x1 (X x2))
    
    freeUnif' sol (p@(X' x1, X' x2) : prob)
        -- Delete
        | x1 == x2  = freeUnif' sol prob
        -- Eliminate
        | otherwise = freeUnif' (p : elim sol) (elim prob)
            where elim = map (subst' x1 (X' x2) *** subst' x1 (X' x2))

    freeUnif' sol (p@(X x, t@(F' f ts)) : prob)
        -- Occurs-Check
        | x `elem` vars t = Nothing
        -- Eliminate
        | otherwise       = freeUnif' (p : elim sol) (elim prob)
            where elim = map (subst x t *** subst x t)

    freeUnif' sol (p@(X' x, t@(F' f ts)) : prob)
        -- Occurs-Check
        | x `elem` vars' t = Nothing
        -- Eliminate
        | otherwise        = freeUnif' (p : elim sol) (elim prob)
            where elim = map (subst' x t *** subst' x t)

{-------------------------------------------------------------------------------

    -- Note that we are only interested in unification in T(F',X) and not in
    -- T(F,X). The following cases can therefore be omitted.


    -- Clash / Decompose
    freeUnif' sol ((F f1 ts1, F f2 ts2):prob)
        | f1 == f2  = freeUnif' sol (zip ts1 ts2 ++ prob)
        | otherwise = Nothing
    freeUnif' _ ((F  _ _, F' _ _):_) = Nothing
    freeUnif' _ ((F' _ _, F  _ _):_) = Nothing
    -- Orient
    freeUnif' sol ((t@(F  _ _),x@(X  _)):prob) = freeUnif' sol ((x,t):prob)
    freeUnif' sol ((t@(F  _ _),x@(X' _)):prob) = freeUnif' sol ((x,t):prob)
    -- Eliminate / Occurs-Check
    freeUnif' sol (p@(X x, t@(F f ts)):prob)
        | x `elem` vars t = Nothing
        | otherwise       = freeUnif' (p:elim sol) (elim prob)
            where elim = map (subst x t *** subst x t)
    freeUnif' sol (p@(X' x, t@(F f ts)):prob)
        | x `elem` vars' t = Nothing
        | otherwise        = freeUnif' (p:elim sol) (elim prob)
            where elim = map (subst' x t *** subst' x t)

-------------------------------------------------------------------------------}
