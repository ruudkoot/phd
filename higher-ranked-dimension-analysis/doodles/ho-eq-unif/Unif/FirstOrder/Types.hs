{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif.FirstOrder.Types where

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


-- FIXME: instead of X and X': x --> Either x Int?
-- FIXME: combine C and F?
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

type AGUnifProb f f' c x = [(T f f' c x, T f f' c x)]

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
