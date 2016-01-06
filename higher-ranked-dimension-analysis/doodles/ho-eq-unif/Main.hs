module Main where

-- | Utility | ----------------------------------------------------------------

both :: (a -> b) -> (a, a) -> (b, b)
both f (x, y) = (f x, f y)

(|||) :: Maybe a -> Maybe a -> Maybe a
Nothing ||| Nothing = Nothing
Just x  ||| Nothing = Just x
Nothing ||| Just y  = Just y
Just _  ||| Just _  = error "|||"

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

fo2simple :: FirstOrderType base -> SimpleType base
fo2simple (bs :=> b) = map base bs :-> b

data Atom sig
    = Bound Int     -- bound variables
    | Free  Int     -- free variables
    | Const sig   -- function constants
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


-- * Unification rules * -------------------------------------------------------

type UnificationRule b s = Env b -> TermPair b s -> TermSystem b s -> Maybe (TermSystem b s)

trivial :: (Eq b, Eq s) => UnificationRule b s
trivial _env (u, u') s
    | u == u'   = Just s
    | otherwise = Nothing

decomposition :: (Eq b, Eq s) => UnificationRule b s
decomposition _env (A xs a us, A xs' a' vs) s
    | xs == xs' && a == a' = Just $ zip us vs ++ s
    | otherwise            = Nothing

variableElimination :: (Eq b, Eq s) => UnificationRule b s
variableElimination env (u,v) s
    = variableElimination' (u,v) ||| variableElimination' (v,u)
  where variableElimination' (A xs (Free f) us, v)
            | us == map (bound xs) [0 .. length xs - 1] && f `notElem` fv v
                = let subst = substForFree env v f
                   in Just $ (u,v) : map (both (applySubstAndReduce subst)) s
            | otherwise = Nothing

imitation :: (Eq b, Eq s) => UnificationRule b s
imitation env (u,v) s
    = imitation' (u,v) ||| imitation' (v,u)
  where imitation' (A xs (Free f) us, A xs' (Free  g) vs) | f /= g
            = undefined
        imitation' (A xs (Free f) us, A xs' (Const c) vs)
            = undefined
        imitation _ = Nothing

imitationBinding = undefined

-- | Higher-order dimension types | --------------------------------------------

data Base = Real
  deriving (Eq, Show)
  
data Signature
    = Mul
    | Inv
  deriving (Eq, Show)
  
signature :: Signature -> FirstOrderType Base
signature Mul = [Real, Real] :=> Real
signature Inv = [Real]       :=> Real
