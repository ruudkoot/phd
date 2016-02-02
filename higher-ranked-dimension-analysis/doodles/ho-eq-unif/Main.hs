{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Main where

import Control.Monad
import Control.Monad.State

import Data.Set hiding (map)

-- | Utility | ----------------------------------------------------------------

-- * Debugging * ---------------------------------------------------------------

(x:xs) !!! 0 = x
[]     !!! _ = error "!!!"
(x:xs) !!! n = xs !!! (n-1)

-- * Sets * --------------------------------------------------------------------

unionMap :: Ord b => (a -> Set b) -> Set a -> Set b
unionMap f ss = unions (map f (toList ss))

unionMap' :: Ord b => (a -> Set b) -> [a] -> Set b
unionMap' f ss = unions (map f ss)

-- | General framework | -------------------------------------------------------

-- * Types * -------------------------------------------------------------------

data Signature sort
    = [sort] :=> sort
  deriving (Eq, Show)

data SimpleType sort
    = [SimpleType sort] :-> sort
  deriving (Eq, Ord, Show)  -- FIXME: arbitrary Ord for Set

base :: sort -> SimpleType sort
base = ([] :->)

infix 4 :->

sig2ty :: Signature sort -> SimpleType sort
sig2ty (bs :=> b) = map base bs :-> b

class (Ord sort, Ord sig) => Theory sort sig | sig -> sort where
    -- FIXME: arbitrary Ord for Set (was Eq)
    signature :: sig -> Signature sort

data Atom sig
    = Bound Int     -- bound variables
    | Free  Int     -- free variables
    | Const sig     -- function constants
  deriving (Eq, Ord, Show)  -- FIXME: arbitrary Ord for Set
  
-- NOTE: does not enforce function constants to be first-order
--       does not enforce the whole term to be first-order
data AlgebraicTerm sort sig
    = A [SimpleType sort] (Atom sig) [AlgebraicTerm sort sig]
  deriving (Eq, Ord, Show)  -- FIXME: arbitrary Ord for Set
  
fv :: AlgebraicTerm sort sig -> [Int]
fv (A _ (Free f) es) = f : concatMap fv es
fv (A _ _        es) =     concatMap fv es

isRigid :: AlgebraicTerm sort sig -> Bool
isRigid (A _ (Bound _) _) = True
isRigid (A _ (Free  _) _) = False
isRigid (A _ (Const _) _) = True

-- Convert an atom into an eta-long term.
atom2term :: Theory sort sig => Env sort -> Env sort -> Atom sig -> AlgebraicTerm sort sig
atom2term envF envB (Bound n) =
    let (xs :-> _) = envB !! n
     in A xs (Bound $ length xs + n) (map (bound xs) [0 .. length xs - 1])
atom2term envF envB (Free  n) =
    let (xs :-> _) = envF !! n
     in A xs (Free  $ length xs + n) (map (bound xs) [0 .. length xs - 1])
atom2term envF envB (Const c) =
    let (xs :-> _) = sig2ty (signature c)
     in A xs (Const               c) (map (bound xs) [0 .. length xs - 1])

-- eta-long variables

type Env sort = [SimpleType sort]

free :: Env sort -> Int -> AlgebraicTerm sort sig
free env n
    = let (xs :-> _) = env !! n
       in A xs (Free $ length xs + n) (map (bound xs) [0 .. length xs - 1])

bound :: Env sort -> Int -> AlgebraicTerm sort sig
bound env n
    = let (xs :-> _) = env !! n
       in A xs (Bound $ length xs + n) (map (bound xs) [0 .. length xs - 1])

type Subst sort sig = [AlgebraicTerm sort sig]

substForFree :: Env sort -> AlgebraicTerm sort sig -> Int -> Subst sort sig
substForFree env v f = map (free env) [0 .. f - 1] ++ [v] ++ map (free env) [f + 1 ..]

type TermPair   sort sig = (AlgebraicTerm sort sig, AlgebraicTerm sort sig)
type TermSystem sort sig = [TermPair sort sig]


-- * Substitution and reduction * ----------------------------------------------

applySubstAndReduce :: Subst sort sig -> AlgebraicTerm sort sig -> AlgebraicTerm sort sig
applySubstAndReduce subst (A xs (Free f) ys)
    = let A xs' a ys' = subst !! f
       in reduce xs xs' a ys' ys
applySubstAndReduce subst u
    = u

bindAndReduce :: Subst sort sig -> AlgebraicTerm sort sig -> AlgebraicTerm sort sig
bindAndReduce zs (A xs (Bound b) ys)
    = let A xs' a ys' = zs !! b
       in reduce xs xs' a ys' ys
bindAndReduce zs u
    = u
    
reduce :: Env sort -> Env sort -> Atom sig -> Subst sort sig -> Subst sort sig -> AlgebraicTerm sort sig
reduce xs xs' a ys' ys
    | length xs' == length ys
        = let ys'' = map (bindAndReduce ys) ys'
           in case a of
                Bound b -> let A xsB aB ysB = ys !! b
                            in reduce xs xsB aB ysB ys''
                Free  f -> A xs (Free  f) ys''
                Const c -> A xs (Const c) ys''
    | otherwise = error "reduce: length xs' /= length ys"


-- * Partial bindings * --------------------------------------------------------

typeOfAtom :: Theory sort sig => Env sort -> Atom sig -> State (Env sort) (SimpleType sort)
typeOfAtom env (Bound b) = return $ env !! b
typeOfAtom _   (Free  f) = do
    env <- get
    return $ env !! f
typeOfAtom _   (Const c) = return $ sig2ty (signature c)

-- NOTE: assuming eta-long as always
typeOfTerm :: Theory sort sig => Env sort -> AlgebraicTerm sort sig -> State (Env sort) (SimpleType sort)
typeOfTerm envB (A xs a ys) = do
    envF    <- get
    _ :-> r <- typeOfAtom (xs ++ envB) a
    return $ xs :-> r

freshAtom :: SimpleType sort -> State (Env sort) (Atom sig)
freshAtom t = do
    env <- get
    put (env ++ [t])
    return $ Free (length env)

partialBinding :: Theory b s => SimpleType b -> Atom s -> State (Env b) (AlgebraicTerm b s)
partialBinding (as :-> b) a = do
    cs :-> b' <- typeOfAtom as a
    if b /= b' then
        error "partialBinding: b /= b'"
    else do

        let generalFlexibleTerm (fs :-> c') = do
                h <- freshAtom (as ++ fs :-> c')
                return $ A fs h $ map (bound $ fs ++ as) $
                    [length fs .. length fs + length as - 1] ++ [0 .. length fs - 1]

        gfts <- mapM generalFlexibleTerm cs
        return (A as a gfts)

-- * Maximal flexible subterms (Qian & Wang) * ---------------------------------

pmfs :: Theory sort sig => AlgebraicTerm sort sig
                            -> Set ([SimpleType sort], AlgebraicTerm sort sig)
pmfs = pmfs' []

pmfs' :: Theory sort sig => [SimpleType sort] -> AlgebraicTerm sort sig
                            -> Set ([SimpleType sort], AlgebraicTerm sort sig)
pmfs' ys (A xs (Free f) ss) = singleton (xs ++ ys, A [] (Free f) ss)
pmfs' ys (A xs a        ss) = unionMap' (pmfs' (xs ++ ys)) ss

-- * Transformation rules (Qian & Wang) * --------------------------------------

type TransformationRule b s = TermPair b s -> TermSystem b s -> State (Env b) (Maybe (TermSystem b s))

type     Conf b s = (Subst b s,                 TermSystem b s)
type HeadConf b s = (Subst b s, TermPair   b s, TermSystem b s)
type PartConf b s = (Subst b s, TermSystem b s, TermSystem b s)

transformAbs :: Theory b s => HeadConf b s -> State (Env b) (Maybe (Conf b s))
transformAbs (theta, (u,v), ss) | isRigid u || isRigid v = do
    -- maximal flexible subterms
    let ps = toList $ pmfs u `union` pmfs v
    -- conditional mapping
    -- NOTE: Unlike the paper we don't bother applying xs to H yet, as this
    --       will not necessarily form an eta-long term. Take care of this in
    --       the application function instead (xs are remembered in the
    --       conditional mapping anyway).
    hs <- forM ps $ \(xs,w) -> do
            xs' :-> r <- typeOfTerm [] w
            freshAtom (xs ++ xs' :-> r)
    let phi = zipWith (\(xs,w) h -> (xs,w,h)) ps hs
    envF <- get
    return $ Just $
        ( error "TODO"
        , [(applyConditionalMapping phi u,applyConditionalMapping phi v)]
          ++ map (\(xs,A xs' a' ys',h) -> (atom2term envF [] h, A (xs'++xs) a' ys')) phi
          ++ ss
        )
transformAbs _ | otherwise = return Nothing

type ConditionalMapping b s = [([SimpleType b], AlgebraicTerm b s, Atom s)]

applyConditionalMapping :: Theory b s => ConditionalMapping b s 
                                    -> AlgebraicTerm b s -> AlgebraicTerm b s
applyConditionalMapping = undefined

transformEUni :: PartConf b s -> State (Env b) (Maybe (Conf b s))
transformEUni = undefined

transformBin :: HeadConf b s -> State (Env b) (Maybe (Conf b s))
transformBin = undefined

-- * Control strategy (Qian & Wang) * ------------------------------------------

controlStrategy = undefined

-- | Examples | ----------------------------------------------------------------

-- * Maximal flexible subterms * -----------------------------------------------

data Sig' = F | G | H
  deriving (Eq, Ord, Show)
  
instance Theory Sort Sig' where
    signature H = [Real, Real] :=> Real

u0 = let f = 0
         g = 1
         x = 0
         y = 1
         x' = 1
         y' = 2
         z  = 0
      in A [base Real, base Real] (Const H)
            [A [] (Free f) [A [] (Bound x) []]
            ,A [base Real] (Free f) [A [] (Bound x') []]
            ,A [] (Free f) [A [] (Free g) [A [] (Bound x) []]]
            ]

-- | Higher-order dimension types | --------------------------------------------

data Sort
    = Real
  deriving (Eq, Ord, Show)  -- FIXME: arbitrary Ord for Set
  
data Sig
    = Mul
    | Inv
    | Unit
  deriving (Eq, Ord, Show)  -- FIXME: arbitrary Ord for Set

instance Theory Sort Sig where
    signature Mul  = [Real, Real] :=> Real
    signature Inv  = [Real]       :=> Real
    signature Unit = []           :=> Real
