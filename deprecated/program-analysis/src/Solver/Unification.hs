module Solver.Unification
    (unify)
where

import Data.Map as Map
import Data.Set as Set

import Language.Haskell.Exts.Annotated

import Common
import Refinement

-- | Unification | -------------------------------------------------------------

-- TODO: factor out the recursion (scheme)
-- TODO: Switch occCheck and otherwise?

unify :: [Constr] -> Subst

unify []
    = Subst { tySubst  = Map.empty
            , annSubst = Map.empty }
unify ((s :=: t)       : c')
    | s == t       = unify c'
unify ((s@(TyVar NoPhi x) :=: t) : c')
    | occCheck s t = let u = Subst { tySubst  = Map.singleton x t
                                   , annSubst = Map.empty         }
                      in unify (u `applySubst` c') $. u
    | otherwise    = error "unify: occurs check"
unify ((s :=: t@(TyVar NoPhi x)) : c')
    | occCheck t s = let u = Subst { tySubst  = Map.singleton x s
                                   , annSubst = Map.empty         }
                      in unify (u `applySubst` c') $. u
    | otherwise    = error "unify: occurs check"
unify ((s@(TyFun sr s1 s2) :=: t@(TyFun tr t1 t2)) : c')
    = let u = uniphi sr tr
       in unify (u `applySubst` ((s1 :=: t1) : (s2 :=: t2) : c')) $. u
unify ((s@(TyList sr s1) :=: t@(TyList tr t1)) : c')
    = let u = uniphi sr tr
       in unify (u `applySubst` ((s1 :=: t1) : c')) $. u
unify ((s@(TyTuple sr Boxed ss) :=: t@(TyTuple tr Boxed ts)) : c')
    | length ss == length ts
        = let u = uniphi sr tr
           in unify (u `applySubst` (zipWith (:=:) ss ts ++ c')) $. u
    | otherwise    = error "unify: tuple arity mismatch"
unify (((TyCon (Phi (RefVar phi)) s) :=: (TyCon (Phi (RefVar psi)) t)) : c')
    | s == t       = let u = Subst { tySubst  = Map.empty
                                   , annSubst = Map.singleton phi psi }
                      in unify (u `applySubst` c') $. u
    | otherwise    = error "unify: constructor clash"
unify ((s@(TyApp NoPhi s1 s2) :=: t@(TyApp NoPhi t1 t2)) : c')
    = unify ((s1 :=: t1) : (s2 :=: t2) : c')
unify x
    = error ("unify: fail (" ++ show x ++ ")")
    
-- | Unify annotation variables | ----------------------------------------------
uniphi :: Phi -> Phi -> Subst
uniphi (Phi (RefVar a)) (Phi (RefVar b))
    = Subst { tySubst  = Map.empty
            , annSubst = Map.singleton a b }
uniphi x y
    = error ("uniphi: " ++ show x ++ " | " ++ show y)
    
-- | Occurs check | ------------------------------------------------------------

occCheck :: Type Phi -> Type Phi -> Bool
occCheck (TyVar _ name) tau = not (name `Set.member` ftv tau)
