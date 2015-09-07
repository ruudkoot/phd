module Main where

import Control.Arrow
import Data.Bifunctor

type Idx = Int

data Name
    = Con   Idx     -- bound in "global" environment / not unifiable
    | Free  Idx     -- not bound                     / unifiable
    | Bound Idx     -- bound in "local" environment  / not unifiable
    deriving (Eq, Read, Show)

data Ty = Arr [Ty] Idx
    deriving Show

base :: Idx -> Ty
base = Arr []

arity :: Ty -> Int
arity (Arr ts _) = length ts

data Tm = Tm [Ty] [(Either Name Tm, [Tm])]
    deriving Show

data Nf = Nf [Ty] [(       Name,    [Nf])]

type Env = [Ty]

-- * check everything is eta-long
checkTm :: Env -> Env -> Env -> Tm -> Bool
checkTm cenv fenv benv (Tm tys tms)
    = all (checkTm' (reverse tys ++ benv)) tms
  where checkTm' :: Env -> (Either Name Tm, [Tm]) -> Bool
        checkTm' benv (Left (Con idx), args)
            = arity (cenv !! idx) == length args
        checkTm' benv (Left (Free idx), args)
            = arity (fenv !! idx) == length args
        checkTm' benv (Left (Bound idx), args)
            = arity (benv !! idx) == length args
        checkTm' benv (Right tm@(Tm tys' _), args)
            = length tys' == length args && checkTm cenv fenv benv tm

-- * reduction of terms to normal form (big-step)
reduce :: Tm -> Tm
reduce (Tm tys tms) = Tm tys (concatMap reduce' tms)     -- FIXME: set-reduction
  where reduce' :: (Either Name Tm, [Tm]) -> [(Either Name Tm, [Tm])]
        reduce' (Left name, args) = [(Left name, map reduce args)]
        reduce' (Right (Tm tys tms), args) =
            let args' = map reduce args
                subst = reverse (map Right args')
             in map (applySubst' subst) tms

tm1 = Tm [Arr [] 0] [(Left (Free 0), [Tm [] [(Left (Bound 0),[])]])]
tm2 = Tm [] [(Right tm1, [Tm [] [(Left (Con 0), [])]])]

-- * substitute bound variables
type Subst = [Either Name Tm]

applySubst :: Subst -> Tm -> Tm
applySubst subst (Tm tys tms)
    = let subst' = map (Left . Bound) [0 .. length tys - 1]
                    ++ map (increaseBinders (length tys)) subst
       in Tm tys $ map (applySubst' subst') tms

applySubst' :: Subst -> (Either Name Tm, [Tm]) -> (Either Name Tm, [Tm])
applySubst' subst (Left (Con idx), args)
    = (Left (Con idx), map (applySubst subst) args)
applySubst' subst (Left (Free idx), args)
    = (Left (Free idx), map (applySubst subst) args)
applySubst' subst (Left (Bound idx), args)
    = (subst !! idx, map (applySubst subst) args)                   -- new redex
applySubst' subst (Right tm, args)
    = (Right (applySubst subst tm), map (applySubst subst) args)

-- * increase the de Bruijn indices in a substitution environment
increaseBinders :: Int -> Either Name Tm -> Either Name Tm
increaseBinders n = increaseBinders' 0
  where increaseBinders' :: Int -> Either Name Tm -> Either Name Tm
        increaseBinders' m = bimap (increaseBindersL m) (increaseBindersR m)
  
        increaseBindersL :: Int -> Name -> Name
        increaseBindersL _ (Con idx)
            = Con idx
        increaseBindersL _ (Free idx)
            = Free idx
        increaseBindersL m (Bound idx)
            | idx < m   = Bound idx
            | otherwise = Bound (idx + n)

        increaseBindersR :: Int -> Tm -> Tm
        increaseBindersR m (Tm tys tms)
            = let m' = m + length tys
               in Tm tys $
                    map (increaseBinders' m' *** map (increaseBindersR m')) tms
