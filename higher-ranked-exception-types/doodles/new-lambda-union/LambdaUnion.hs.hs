module Main where

import Control.Arrow
import Data.Bifunctor

type Idx = Int

data Name
    = Con   Idx     -- bound in "global" environment / not unifiable
    | Free  Idx     -- not bound                     / unifiable
    | Bound Idx     -- bound in "local" environment  / not unifiable
    deriving (Eq, Read)

data Ty = Arr [Ty] Idx

base :: Idx -> Ty
base = Arr []

arity :: Ty -> Int
arity (Arr ts _) = length ts

data Tm = Tm [Ty] [(Either Name Tm, [Tm])]

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

-- * reduction of terms to normal form
reduce :: Tm -> Tm
reduce (Tm tys tms) = Tm tys (map reduce' tms)
  where reduce' :: (Either Name Tm, [Tm]) -> (Either Name Tm, [Tm])
        reduce' (Left name, args) = (Left name, map reduce args)
        reduce' (Right tm,  args) = 
            let _ = applyArgs [] tm args
             in undefined

-- * apply arguments to a lamda-abstration
applyArgs :: [Either Name Tm] -> Tm -> [Tm] -> [Tm]
applyArgs subst (Tm tys tms) args = map (applyArgs' (reverse args ++ subst)) tms
  where applyArgs' :: [Tm] -> (Either Name Tm, [Tm]) -> (Either Name Tm, [Tm])
        applyArgs' subst (Left (Con idx), args')
            = (Left (Con idx), map (applyArgs subst args'))
        applyArgs' subst (Left (Free idx), args')
            = (Left (Free idx), map (applyArgs subst args'))
        applyArgs' subst (Left (Bound idx), args')
            = (Right (subst !! idx), map (applyArgs subst args'))   -- new redex
        applyArgs' subst (Right (Tm tys' tms'), args')
            = let subst' = map (Left . Bound) [0 .. length tys' - 1]
                            ++ map (increaseBinders (length tys')) subst
               in ( Right (Tm tys' (map (applyArgs' subst') tms'))
                  , map (\tm -> applyArgs subst' tm args) args'
                  )

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
               in Tm tys (map (increaseBinders' m' *** map (increaseBindersR m')) tms)

-- * convert term in normal form to normal form
tm2nf :: Tm -> Nf
tm2nf = undefined
