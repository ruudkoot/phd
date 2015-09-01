{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Mycroft1984 where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import qualified Data.Graph    as G
import qualified Data.List     as L
import qualified Data.Map      as M
import qualified Data.Map.Util as M
import           Data.Maybe
import qualified Data.Set      as S
import qualified Data.Set.Util as S
import qualified Data.Tree     as T

-- | Syntax

type Name = String

data Expr
    = Var Name
    | App Expr Expr
    | Lam Name Expr
    | Fix Name Expr
    | Let Name Expr Expr
    deriving (Eq, Ord, Show)
    
-- | Static Semantics

-- * Types

data Ty
    = TyVar Name
    | TyCon TyCon
    | TyFun Ty Ty
    deriving (Eq, Ord, Show)

data TyCon
    = TyBool
    | TyInt
    deriving (Eq, Ord, Show)

data TyScheme = Forall [Name] Ty deriving (Eq, Ord, Show)
    -- FIXME: Eq should be modulo alpha-renaming

type TyEnv = M.Map Name TyScheme

-- * Substitutions

infixr 0 $@
infixr 9 $.

type Subst = M.Map Name Ty

idSubst :: Subst
idSubst = M.empty

($.) :: Subst -> Subst -> Subst
subst2 $. subst1 = (subst2 $$ subst1) $+ subst2
    where ($$), ($+) :: Subst -> Subst -> Subst
          subst1 $$ subst2
            = M.map (subst1 $@) subst2
          subst1 $+ subst2
            = M.unionWith (error "overlapping substitutions") subst1 subst2

class Substitute t where
    ($@) :: Subst -> t -> t

instance Substitute Ty where
    subst $@ t@(TyVar a)     = M.findWithDefault t a subst
    _     $@ t@(TyCon _)     = t
    subst $@   (TyFun t1 t2) = TyFun (subst $@ t1) (subst $@ t2)

instance Substitute TyScheme where
    subst $@ Forall as t = Forall as (subst `M.restrict` as $@ t)

instance Substitute TyEnv where
    subst $@ a = M.map (subst $@) a

-- * Inference Monad

type InferM t = State [Name] t
    -- FIXME: Subst
    -- FIXME: Maybe/Either/ErrorT (also for unification)

-- * Inference algorithm

w :: TyEnv -> Expr -> InferM (Subst, Ty)
w a (Var x)
    | Just s <- M.lookup x a  = (idSubst,) <$> inst s
    | otherwise               = error "variable not in scope"
w a (e1 `App` e2)
    = do (s1, t1) <- w        a  e1
         (s2, t2) <- w (s1 $@ a) e2
         b <- fresh
         let v = u (s2 $@ t1) (TyFun t2 b)
         return (v $. s2 $. s1, v $@ b)
w a (Lam x e1)
    = do b <- fresh
         (s1, t1) <- w (M.insert x (Forall [] b) a) e1
         return (s1, TyFun (s1 $@ b) t1)
w a (Let x e1 e2)
    = do (s1, t1) <- w a e1
         let a1 = M.insert x (gen (s1 $@ a) t1) (s1 $@ a)
         (s2, t2) <- w a1 e2
         return (s2 $. s1, t2)
w a (Fix x e1)
    = do b <- fresh
         let ts0 = Forall [b] (TyVar b)
         let a0 = M.insert x ts0 a
         (s, t) <- mycroftIteration a0 ts0
         return (s, t)

        where mycroftIteration :: TyEnv -> TyScheme -> InferM (Subst, Ty)
              mycroftIteration a ts
                  = do (s', t') <- w a e1
                       let ts' = gen (s' $@ a) t'
                       let a' = M.insert x ts' (s' $@ a)
                       if (s' $@ ts) == ts' then
                            return (s', t')
                       else
                            mycroftIteration a' ts'

-- * Unification

u :: Ty -> Ty -> Subst
u (TyVar a) t2@(TyVar a')
    | a == a'   = M.empty
    | otherwise = M.singleton a t2
u (TyVar a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = M.singleton a t
u t (TyVar a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = M.singleton a t
u (TyCon c) (TyCon c')
    | c == c'   = idSubst
    | otherwise = error "constructor clash"
u (TyFun t1 t2) (TyFun t1' t2')
    = let s1 = u        t1         t1'
          s2 = u (s1 $@ t2) (s1 $@ t2')
       in s2 $. s1
u _ _
    = error "constructor clash"

-- * Instantiation

inst :: TyScheme -> InferM Ty
inst (Forall as t)
    = do as' <- replicateM (length as) fresh
         let r = M.fromList (zip as as')
         return (r $@ t)
         
-- * Generalization

gen :: TyEnv -> Ty -> TyScheme
gen a t = Forall (S.toList $ ftv t `S.difference` ftv a) t

-- | Free Variables

class Free t where
    ftv :: t -> S.Set Name

instance Free Ty where
    ftv (TyVar a)     = S.singleton a
    ftv (TyCon _)     = S.empty
    ftv (TyFun t1 t2) = ftv t1 `S.union` ftv t2

instance Free TyScheme where
    ftv (Forall as t) = ftv t `S.difference` S.fromList as

instance Free TyEnv where
    ftv = S.unions . M.elems . M.map ftv

-- | Fresh

class Fresh t where
    fresh :: InferM t

instance Fresh Name where
    fresh = do (x:xs) <- get
               put xs
               return x

instance Fresh Ty where
    fresh = TyVar <$> fresh
