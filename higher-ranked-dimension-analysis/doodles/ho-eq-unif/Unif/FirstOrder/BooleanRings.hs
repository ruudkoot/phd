{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif.FirstOrder.BooleanRings (
    BR(..)
) where

import Data.Map

data BR
    = Add
    | Mul
    | Inv
    | Zero
    | Unit
  deriving (Eq, Bounded, Enum, Ord, Show)
  -- FIXME: arbitrary Ord for Set









-- | Non-clausal satisfiability testing (Van Gelder 1984) | --------------------

data BoolExp x
    = Val Bool
    | Lit x
    | BoolExp x :&: BoolExp x
    | BoolExp x :|: BoolExp x
    | Not (BoolExp x)
  deriving Show

data Polarity = Pos | Neg
  deriving Show

data SuccinctAndOrTree x
    = VAL Bool
    | LIT x
    | AND (Map x Polarity) [SuccinctAndOrTree x]
    | OR  (Map x Polarity) [SuccinctAndOrTree x]
  deriving Show

{-
succinct :: BoolExp x -> SuccinctAndOrTree x
succinct (Val t)     = VAL t
succinct (Lit x)     = LIT x
succinct (v1 :&: v2) = 
    let 
-}
