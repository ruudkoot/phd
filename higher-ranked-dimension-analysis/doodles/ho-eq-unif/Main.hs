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

data Signature sort
    = [sort] :=> sort
  deriving (Eq, Show)

data SimpleType sort
    = [SimpleType sort] :-> sort
  deriving (Eq, Show)

sort :: sort -> SimpleType sort
sort = ([] :->)

infix 4 :->

sig2ty :: Signature sort -> SimpleType sort
sig2ty (bs :=> b) = map sort bs :-> b

class (Eq sort, Eq sig) => Theory sort sig | sig -> sort where
    signature :: sig -> Signature sort

data Atom sig
    = Bound Int     -- bound variables
    | Free  Int     -- free variables
    | Const sig     -- function constants
  deriving (Eq, Show)
  
-- NOTE: does not enforce function constants to be first-order
--       does not enforce the whole term to be first-order
data AlgebraicTerm sort sig
    = A [SimpleType sort] (Atom sig) [AlgebraicTerm sort sig]
  deriving (Eq, Show)
  
fv :: AlgebraicTerm sort sig -> [Int]
fv (A _ (Free f) es) = f : concatMap fv es
fv (A _ _        es) =     concatMap fv es

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

typeOf :: Theory sort sig => Env sort -> Atom sig -> State (Env sort) (SimpleType sort)
typeOf env (Bound b) = return $ env !! b
typeOf _   (Free  f) = do
    env <- get
    return $ env !! f
typeOf _   (Const c) = return $ sig2ty (signature c)

freshAtom :: SimpleType sort -> State (Env sort) (Atom sig)
freshAtom t = do
    env <- get
    put (env ++ [t])
    return $ Free (length env)

partialBinding :: Theory b s => SimpleType b -> Atom s -> State (Env b) (AlgebraicTerm b s)
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

trivial :: Theory sort sig => UnificationRule sort sig
trivial (u, u') s
    | u == u'   = return $ Just s
    | otherwise = return $ Nothing

decomposition :: Theory sort sig => UnificationRule sort sig
decomposition (A xs a us, A xs' a' vs) s
    | xs == xs' && a == a' = return $ Just $ zip us vs ++ s
    | otherwise            = return $ Nothing

variableElimination :: Theory sort sig => UnificationRule sort sig
variableElimination (u@(A xs _ _),v@(A xs' _ _)) s
    | xs /= xs' = error "variableElimination: xs /= xs'"
    | otherwise = variableElimination' (u,v) ||| variableElimination' (v,u)
  where
    variableElimination' (A xs (Free f) us, v)
        | us == map (bound xs) [0 .. length xs - 1] && f `notElem` fv v
            = do env <- get
                 let subst = substForFree env v f
                 return $ Just $ (u,v) : map (both (applySubstAndReduce subst)) s
        | otherwise = return $ Nothing

imitation :: Theory sort sig => UnificationRule sort sig
imitation (u@(A xs _ _),v@(A xs' _ _)) s
    | xs /= xs' = error "imitation: xs /= xs'"
    | otherwise = imitation' (u,v) ||| imitation' (v,u)     -- FIXME: can both succeed
  where
    imitation' r@(A xs (Free f) us, A xs' (Free  g) vs) | f /= g
        = do env <- get
             t <- partialBinding (env !! f) (Free g)
             return $ Just $ (free env f, t) : r : s
    imitation' r@(A xs (Free f) us, A xs' (Const c) vs)
        = do env <- get
             t <- partialBinding (env !! f) (Const c)
             return $ Just $ (free env f, t) : r : s
    imitation _ = return Nothing

projection :: Theory sort sig => Int -> UnificationRule sort sig
projection i (u@(A xs _ _),v@(A xs' _ _)) s
    | xs /= xs' = error "projection: xs /= xs'"
    | otherwise = projection' (u,v) ||| projection' (v,u)   -- FIXME: can both succeed
  where
    projection' r@(A xs (Free f) us, A xs' (Free  g) vs) | f /= g
        = do env <- get
             t <- partialBinding (env !! f) (Free g)
             return $ Just $ (free env f, t) : r : s
    projection' r@(A xs (Free f) us, A xs' a vs)    -- 'a' is Bound or Const
        = do env <- get
             t <- partialBinding (env !! f) a
             return $ Just $ (free env f, t) : r : s
    projection _ = return Nothing
    
flexFlex :: Theory sort sig => Atom sig -> UnificationRule sort sig
flexFlex a r@(A xs (Free f) us, A xs' (Free g) vs) s
    | xs /= xs' 
        = error "flexFlex: xs /= xs'"
    | a == Free f || a == Free g
        = error "flexFlex: a = F \\/ a = G"
    | otherwise
        = do env <- get
             let _ :-> b = env !! f
             t <- partialBinding (xs :-> b) a
             return $ Just $ (free env f, t) : r : s


-- | Higher-order dimension types | --------------------------------------------

data Sort
    = Real
  deriving (Eq, Show)
  
data Sig
    = Mul
    | Inv
  deriving (Eq, Show)

instance Theory Sort Sig where
    signature Mul = [Real, Real] :=> Real
    signature Inv = [Real]       :=> Real
