module Analysis.LambdaUnionNew.Reduce (
    tm2nf,
    reduce
) where

import Analysis.LambdaUnionNew.Types

import Control.Arrow
import Data.Bifunctor
import Data.Either
import Data.List
import GHC.Exts (sortWith)

fromLeft :: Either a b -> a
fromLeft (Left x) = x

-- * term in normal form to normal form
tm2nf :: Tm -> Nf
tm2nf (Tm tys tms) = Nf tys (map tm2nf' tms)
  where tm2nf' :: (Either Name Tm, [Tm]) -> (Name, [Nf])
        tm2nf' (Left x, args) = (x, map tm2nf args)

-- * rewrite "set" into normal form 
setRewrite :: [(Either Name Tm, [Tm])] -> [(Either Name Tm, [Tm])]
setRewrite as =
    let (ns, ts) = partition (isLeft . fst) as
        ns'      = combineN (sortWith fst (map (fromLeft *** id) ns))
        ts'      = if null ts then [] else error "setRewrite: found redex"
     in map (Left *** id) ns' ++ ts'
  where combineN :: [(Name, [Tm])] -> [(Name, [Tm])]
        combineN []
            = []
        combineN [(x,xs)]
            = [(x,xs)]
        combineN ((x,xs):(y,ys):zzs)
            | x == y    = combineN ((x, zipWith combineArgs xs ys) : zzs)
            | otherwise = (x,xs) : combineN ((y,ys) : zzs)

        combineArgs :: Tm -> Tm -> Tm
        combineArgs (Tm tys1 tms1) (Tm tys2 tms2)
            | tys1 == tys2 = Tm tys1 (setRewrite (tms1 ++ tms2))    -- recursion
            | otherwise    = error "combineArgs"                    -- new redices?

-- * reduction of terms to normal form (big-step)
reduce :: Tm -> Tm  -- FIXME: Tm -> Nf? (setRewrite expects Nf!)
reduce (Tm tys tms) = Tm tys (setRewrite (concatMap reduce' tms))

reduce' :: (Either Name Tm, [Tm]) -> [(Either Name Tm, [Tm])]
reduce' (Left name, args) = [(Left name, map reduce args)]
reduce' (Right (Tm tys tms), args) =
    let args' = map reduce args
        subst = reverse (map Right args')
     in concatMap (applySubst' subst) tms

-- * substitute bound variables
type Subst = [Either Name Tm]

applySubst :: Subst -> Tm -> Tm
applySubst subst (Tm tys tms)
    = let subst' = map (Left . Bound) [0 .. length tys - 1]
                    ++ map (increaseBinders (length tys)) subst
       in Tm tys $ concatMap (applySubst' subst') tms

applySubst' :: Subst -> (Either Name Tm, [Tm]) -> [(Either Name Tm, [Tm])]
applySubst' subst (Left (Con idx), args)
    = [(Left (Con idx), map (applySubst subst) args)]
applySubst' subst (Left (Free idx), args)
    = [(Left (Free idx), map (applySubst subst) args)]
applySubst' subst (Left (Bound idx), args) -- possible new redex
    = reduce' (subst !! idx, map (applySubst subst) args)
applySubst' subst (Right tm, args)
    = [(Right (applySubst subst tm), map (applySubst subst) args)]

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
