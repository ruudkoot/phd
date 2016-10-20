{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif.FirstOrder.Types (
    T(..),
    vars,
    vars',
    numX,
    numX',
    numC,
    castC,
    castC',
    FOUnifProb,
    TermAlg,
    subst,
    subst'
) where

import Util (maximum')

-- FIXME: instead of X and X': x --> Either x Int?
-- FIXME: combine C and F? is C still used anywhere?
data T f f' c x
    = X  x                  -- variables            (E and E')
    | X' Int                -- fresh variables      (E and E')
    | C  c                  -- nullary constants    (FIXME: E???)
    | F  f  [T f f' c x]    -- function symbols     (E)
    | F' f' [T f f' c x]    -- function symbols     (E')
  deriving (Eq, Ord, Show)

vars :: T f f' c x -> [x]
vars (X  x   ) = [x]
vars (X' _   ) = []
vars (C  _   ) = error "vars: C" -- []
vars (F  _ ts) = concatMap vars ts
vars (F' _ ts) = concatMap vars ts

vars' :: T f f' c x -> [Int]
vars' (X  _   ) = []
vars' (X' x   ) = [x]
vars' (C  _   ) = error "vars': C" -- []
vars' (F  _ ts) = concatMap vars' ts
vars' (F' _ ts) = concatMap vars' ts

numX :: T f f' c Int -> Int
numX (X  x   ) = x + 1
numX (X' _   ) = 0
numX (C  _   ) = 0 -- error "numX: C"
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

type FOUnifProb f f' c x = [(T f f' c x, T f f' c x)]

class    (Ord  f, Ord  f', Ord  c, Ord  x
         ,Show f, Show f', Show c, Show x) => TermAlg f f' c x
instance (Ord f, Ord f', Ord c, Ord x
         ,Show f, Show f', Show c, Show x) => TermAlg f f' c x
         
subst :: TermAlg f f' c x => x -> T f f' c x -> T f f' c x -> T f f' c x
subst x t t'@(X  x') | x == x'   = t
                     | otherwise = t'
subst x _ t'@(X' _ ) = t'
subst x _ t'@(C  _ ) = error "subst: C" -- t'
subst x t (F  f  ts) = F  f  (map (subst x t) ts)
subst x t (F' f' ts) = F' f' (map (subst x t) ts)

subst' :: Int -> T f f' c x -> T f f' c x -> T f f' c x
subst' _ _ t'@(X  _ ) = t'
subst' x t t'@(X' x') | x == x'   = t
                      | otherwise = t'
subst' _ _ t'@(C  _ ) = error "subst': C" -- t'
subst' x t (F  f  ts) = F  f  (map (subst' x t) ts)
subst' x t (F' f' ts) = F' f' (map (subst' x t) ts)
