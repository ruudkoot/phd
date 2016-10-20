{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif.FirstOrder.BooleanRings (
    BA(..),
    BAExp,
    BASubst,
    baUnif1,
    -- TODO: baUnifN,
    BR(..),
    BRExp,
    BRSubst,
    brUnif1
    -- TODO: brUnifN
) where

import Unif.FirstOrder.Types
import qualified Sat.DPLL as DPLL

-- | Data.List | ---------------------------------------------------------------

lookupWithDefault :: Eq k => v -> k -> [(k, v)] -> v
lookupWithDefault def k xs = maybe def id (lookup k xs)

-- | Unification in Boolean algebras & rings using Löwenheim's method | --------

-- The heavy lifting is done by the SAT solver; DPLL is included. Non-clausal
-- satisfiability testing (e.g. Van Gelder 1984) may be more efficient than DPLL
-- if we don't keep intermediate expressions in CNF. (At least asymptotically,
-- but practically?)

-- TODO: Unification in arbitrary (as opposed to free) Boolean rings. See
--       Martin & Nipkow, Section 6. (Needs Knuth-Bendix to compute an
--       orthogonal basis efficiently.)

data BA
    = And
    | Or
    | Not
    | TRUE
    | FALSE
  deriving (Eq, Bounded, Enum, Ord, Show)

data BR
    = Add   -- xor
    | Mul   -- and
    | Inv   -- x = -x
    | Zero  -- false
    | One   -- true
  deriving (Eq, Bounded, Enum, Ord, Show)

type BAExp = T BA () Int Int
type BRExp = T BR () Int Int

showBRExp :: BRExp -> String
showBRExp (X x          ) = "x" ++ show x
showBRExp (C c          ) = "C" ++ show c
showBRExp (F Add  [p, q]) = "(" ++ showBRExp p ++ "+" ++ showBRExp q ++ ")"
showBRExp (F Mul  [p, q]) = "(" ++ showBRExp p ++ "+" ++ showBRExp q ++ ")"
showBRExp (F Inv  [p]   ) = "~(" ++ showBRExp p ++ ")"
showBRExp (F Zero []    ) = "0"
showBRExp (F One  []    ) = "1"

br2ba :: BRExp -> BAExp
br2ba (X x) = (X x)
br2ba (C c) = (C c)
br2ba (F Add [br2ba -> p', br2ba -> q'])
    = F And [F Or [p', q'], F Or [F Not [p'], F Not [q']]]
br2ba (F Mul  [p, q]      ) = F And [br2ba p, br2ba q]
br2ba (F Inv  [p]         ) = br2ba p
br2ba (F Zero []          ) = F FALSE []
br2ba (F One  []          ) = F TRUE  []

ba2exp :: BAExp -> DPLL.Exp Int
ba2exp (X x           ) = DPLL.Atom x
ba2exp (F And   [p, q]) = DPLL.And (ba2exp p) (ba2exp q)
ba2exp (F Or    [p, q]) = DPLL.Or  (ba2exp p) (ba2exp q)
ba2exp (F Not   [p]   ) = DPLL.Not (ba2exp p)
ba2exp (F TRUE  []    ) = DPLL.Val True
ba2exp (F FALSE []    ) = DPLL.Val False

type BASubst = [BAExp]
type BRSubst = [BRExp]

valuationToVector :: Int -> [(Int,Bool)] -> [Bool]
valuationToVector n xs = map (\i -> lookupWithDefault True i xs) [0 .. n - 1]

bool2ba :: Bool -> BAExp
bool2ba True  = F TRUE  []
bool2ba False = F FALSE []

bool2br :: Bool -> BRExp
bool2br True  = F One  []
bool2br False = F Zero []

-- * Solve the equation f(X) = 0 in BA.
baUnif1 :: BAExp -> Maybe BASubst
baUnif1 t =
    let numVars = numX t
     in case DPLL.dpll (DPLL.toCNF (ba2exp t)) of
            []        -> Nothing
            (val : _) ->
                let b = valuationToVector numVars val

                    f :: Int -> BAExp
                    f i = F Or [ F And [X i, F Not [t]     ]
                               , F And [bool2ba (b !! i), t] ]

                 in Just $ map f [0 .. numVars - 1]

cToBase :: Int -> BRExp -> BRExp
cToBase _ (X x) = X x
cToBase c (C c')
    | c == c'   = F One  []
    | otherwise = F Zero []
cToBase c (F f ts) = F f (map (cToBase c) ts)

-- * Solve the equation f(X) = 0 in BR.
brUnif1 :: Int -> BRExp -> Maybe BRSubst
brUnif1 c t =
    let t'      = cToBase c t
        numVars = numX t
        numBase = numC t
     in case DPLL.dpll (DPLL.toCNF (ba2exp (br2ba t'))) of
            []        -> Nothing
            (val : _) ->
                let b = valuationToVector numVars val

                    f :: Int -> BRExp
                    f i = F Add [X i, F Mul [t', F Add [X i, bool2br (b !! i)]]]

                 in Just $ map f [0 .. numVars - 1]
