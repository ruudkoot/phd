{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Main where

import Control.Monad
import Control.Monad.State

-- | Utility | ----------------------------------------------------------------

both :: (a -> b) -> (a, a) -> (b, b)
both f (x, y) = (f x, f y)

(|||) :: State s (Maybe a) -> State s (Maybe a) -> State s (Maybe a)
x ||| y = do x' <- x
             case x' of
                Nothing -> do y' <- y
                              case y' of
                                Nothing -> return Nothing
                                justY   -> return justY
                justX   -> do y' <- y
                              case y' of
                                Nothing -> return justX
                                justY   -> error "|||"


-- * Debugging * ---------------------------------------------------------------

(x:xs) !!! 0 = x
[]     !!! _ = error "!!!"
(x:xs) !!! n = xs !!! (n-1)


-- | General framework | -------------------------------------------------------

-- * Types * -------------------------------------------------------------------

data FirstOrderType base
    = [base] :=> base
  deriving (Eq, Show)

data SimpleType base
    = [SimpleType base] :-> base
  deriving (Eq, Show)

base :: base -> SimpleType base
base = ([] :->)

infix 4 :->

fo2simple :: FirstOrderType base -> SimpleType base
fo2simple (bs :=> b) = map base bs :-> b

class (Eq base, Eq sig) => Sig base sig | sig -> base where
    signature :: sig -> FirstOrderType base

data Atom sig
    = Bound Int     -- bound variables
    | Free  Int     -- free variables
    | Const sig     -- function constants
  deriving (Eq, Show)
  
-- NOTE: does not enforce function constants to be first-order
--       does not enforce the whole term to be first-order
data AlgebraicTerm base sig
    = A [SimpleType base] (Atom sig) [AlgebraicTerm base sig]
  deriving (Eq, Show)
  
fv :: AlgebraicTerm base sig -> [Int]
fv (A _ (Free f) es) = f : concatMap fv es
fv (A _ _        es) =     concatMap fv es

-- eta-long variables

type Env base = [SimpleType base]

free :: Env base -> Int -> AlgebraicTerm base sig
free env n
    = let (xs :-> _) = env !! n
       in A xs (Free $ length xs + n) (map (bound xs) [0 .. length xs - 1])

bound :: Env base -> Int -> AlgebraicTerm base sig
bound env n
    = let (xs :-> _) = env !! n
       in A xs (Bound $ length xs + n) (map (bound xs) [0 .. length xs - 1])

type Subst base sig = [AlgebraicTerm base sig]

substForFree :: Env base -> AlgebraicTerm base sig -> Int -> Subst base sig
substForFree env v f = map (free env) [0 .. f - 1] ++ [v] ++ map (free env) [f + 1 ..]

type TermPair   base sig = (AlgebraicTerm base sig, AlgebraicTerm base sig)
type TermSystem base sig = [TermPair base sig]


-- * Substitution and reduction * ----------------------------------------------

applySubstAndReduce :: Subst base sig -> AlgebraicTerm base sig -> AlgebraicTerm base sig
applySubstAndReduce subst (A xs (Free f) ys)
    = let A xs' a ys' = subst !! f
       in reduce xs xs' a ys' ys
applySubstAndReduce subst u
    = u

bindAndReduce :: Subst base sig -> AlgebraicTerm base sig -> AlgebraicTerm base sig
bindAndReduce zs (A xs (Bound b) ys)
    = let A xs' a ys' = zs !! b
       in reduce xs xs' a ys' ys
bindAndReduce zs u
    = u
    
reduce :: Env base -> Env base -> Atom sig -> Subst base sig -> Subst base sig -> AlgebraicTerm base sig
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

typeOf :: Sig base sig => Env base -> Atom sig -> State (Env base) (SimpleType base)
typeOf env (Bound b) = return $ env !! b
typeOf _   (Free  f) = do
    env <- get
    return $ env !! f
typeOf _   (Const c) = return $ fo2simple (signature c)

freshAtom :: SimpleType base -> State (Env base) (Atom sig)
freshAtom t = do
    env <- get
    put (env ++ [t])
    return $ Free (length env)

partialBinding :: Sig b s => SimpleType b -> Atom s -> State (Env b) (AlgebraicTerm b s)
partialBinding (as :-> b) a = do
    cs :-> b' <- typeOf as a
    if b /= b' then
        error "partialBinding: b /= b'"
    else do

        let generalFlexibleTerm (fs :-> c') = do
                h <- freshAtom (as ++ fs :-> c')
                return $ A fs h $ map (bound $ fs ++ as) $
                    [length fs .. length fs + length as - 1] ++ [0 .. length fs - 1]

        gfts <- mapM generalFlexibleTerm cs
        return (A as a gfts)


-- * Unification rules * -------------------------------------------------------

type UnificationRule b s = TermPair b s -> TermSystem b s -> State (Env b) (Maybe (TermSystem b s))

trivial :: Sig b s => UnificationRule b s
trivial (u, u') s
    | u == u'   = return $ Just s
    | otherwise = return $ Nothing

decomposition :: Sig b s => UnificationRule b s
decomposition (A xs a us, A xs' a' vs) s
    | xs == xs' && a == a' = return $ Just $ zip us vs ++ s
    | otherwise            = return $ Nothing

variableElimination :: Sig b s => UnificationRule b s
variableElimination (u,v) s
    = variableElimination' (u,v) ||| variableElimination' (v,u)
  where
    variableElimination' (A xs (Free f) us, v)
        | us == map (bound xs) [0 .. length xs - 1] && f `notElem` fv v
            = do env <- get
                 let subst = substForFree env v f
                 return $ Just $ (u,v) : map (both (applySubstAndReduce subst)) s
        | otherwise = return $ Nothing

imitation :: Sig b s => UnificationRule b s
imitation (u,v) s
    = imitation' (u,v) ||| imitation' (v,u)         -- FIXME: can both succeed
  where
    imitation' r@(A xs (Free f) us, A xs' (Free  g) vs) | f /= g
        = do env <- get
             t <- partialBinding (env !! f) (Free g)
             return $ Just $ (free env f, t) : r : s
    imitation' r@(A xs (Free f) us, A xs' (Const c) vs)
        = do env <- get
             t <- partialBinding (fo2simple $ signature c) (Const c)
             return $ Just $ (free env f, t) : r : s
    imitation _ = return Nothing


-- | Higher-order dimension types | --------------------------------------------

data Base
    = Real
  deriving (Eq, Show)
  
data Signature
    = Mul
    | Inv
  deriving (Eq, Show)

instance Sig Base Signature where
    signature Mul = [Real, Real] :=> Real
    signature Inv = [Real]       :=> Real
