module Analysis.LambdaUnionNew.Types (
    Idx,
    Name(..),
    Ty(..),
    base,
    arity,
    Tm(..),
    Nf(..),
    Env,
    checkTm,
    con,
    free,
    bound,
    term,
    tm1,
    tm2
) where

type Idx = Int

data Name
    = Con   Idx     -- bound in "global" environment / not unifiable
    | Free  Idx     -- not bound                     / unifiable
    | Bound Idx     -- bound in "local" environment  / not unifiable
    deriving (Eq, Ord, Read, Show)

data Ty = Arr [Ty] Idx
    deriving (Eq, Show)

base :: Idx -> Ty
base = Arr []

arity :: Ty -> Int
arity (Arr ts _) = length ts

data Tm = Tm [Ty] [(Either Name Tm, [Tm])]
    deriving Show

data Nf = Nf [Ty] [(       Name,    [Nf])]
    deriving Show

type Env = [Ty]

-- * check everything is eta-long
checkTm :: Env -> Env -> Env -> Tm -> Bool
checkTm cenv fenv benv (Tm tys tms)
    = all (checkTm' (reverse tys ++ benv)) tms
  where checkTm' :: Env -> (Either Name Tm, [Tm]) -> Bool
        checkTm' benv (Left (Con idx), args)
            | arity (cenv !! idx) == length args = True
            | otherwise                          = error "A"
        checkTm' benv (Left (Free idx), args)
            | arity (fenv !! idx) == length args = True
            | otherwise                          = error "B"
        checkTm' benv (Left (Bound idx), args)
            | arity (benv !! idx) == length args = True
            | otherwise                          = error "C"
        checkTm' benv (Right tm@(Tm tys' _), args)
            | length tys' == length args && checkTm cenv fenv benv tm
                = True
            | otherwise                          = error "D"

-- * test terms

con   = Left . Con
free  = Left . Free
bound = Left . Bound
term  = Right

tm1 = Tm [base 0] [(free 0, [Tm [] [(bound 0, [])]])]
tm2 = Tm [] [(term tm1, [Tm [] [(con 1, []),(con 0, []),(con 0,[])]])]
