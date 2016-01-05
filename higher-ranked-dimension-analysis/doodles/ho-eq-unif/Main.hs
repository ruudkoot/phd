module Main where

-- | Utility | ----------------------------------------------------------------

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
    = variableElimination' (u,v) s ||| variableElimination' (v,u) s
  where variableElimination' (A xs (Free f) us, v) s
            | us == map (bound xs) [0 .. length xs - 1] && f `notElem` fv v
                = let subst = substForFree env v f
                   in Just $ (u,v) : map (normalize . applySubst subst) s
            | otherwise = Nothing
                   
normalize = undefined

-- applySubst :: Subst base sig
applySubst = undefined

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
