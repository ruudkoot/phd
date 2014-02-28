{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeSynonymInstances  #-}

-- FIXME: make InferM into a substitution monad

module Types
    ( Ty(..)
    , TyCon(..)
    , Env
    , infer
    )
where

import qualified Data.Map as M
import qualified Data.Set as S

import Fresh
import FTV
import Subst
import Syntax

-- | Types

data Ty
    = TyVar  Name
    | TyCon  TyCon
    | TyFun  Ty Ty
    | TyPair Ty Ty
    | TyList Ty
    deriving (Eq, Ord)
    
data TyCon
    = TyUnit
    | TyBool
    | TyInt
    deriving (Eq, Ord, Show)

instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar a)
               
instance FTV Ty where
    ftv (TyVar a)
        = S.singleton a
    ftv (TyCon _)
        = S.empty
    ftv (TyFun t1 t2)
        = ftv t1 `S.union` ftv t2
    ftv (TyPair t1 t2)
        = ftv t1 `S.union` ftv t2
    ftv (TyList t)
        = ftv t
        
instance Substitute Ty Ty where
    subst $@ t@(TyVar a)
        | Just t' <- M.lookup a subst = t'
        | otherwise                   = t
    _     $@ t@(TyCon _) 
        = t
    subst $@   (TyFun  t1 t2)
        = TyFun  (subst $@ t1) (subst $@ t2)
    subst $@   (TyPair t1 t2)
        = TyPair (subst $@ t1) (subst $@ t2)
    subst $@   (TyList t)
        = TyList (subst $@ t)

instance Show Ty where
    show (TyVar a)
        = show a
    show (TyCon c) 
        = show c
    show (TyFun t1 t2)
        = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show (TyPair t1 t2) 
        = "(" ++ show t1 ++ ", "   ++ show t2 ++ ")"
    show (TyList t)
        = "[" ++ show t                       ++ "]"
        
-- | Environments

type Env t = M.Map Name t

instance FTV t => FTV (Env t) where
    ftv = M.foldr (S.union . ftv) S.empty

instance Substitute t e => Substitute t (Env e) where
    subst $@ env = M.map (subst $@) env
       
-- | Constant typings

typeOf :: Con -> InferM Ty
typeOf Unit
    = return (TyCon TyUnit)
typeOf (Bool _)
    = return (TyCon TyBool)
typeOf (Int _)
    = return (TyCon TyInt )
typeOf (ExnC _ _)
    = do a <- fresh
         return a

-- | Unification

unify :: Ty -> Ty -> Subst Ty
unify (TyVar a1) t2@(TyVar a2)
    | a1 == a2  = idSubst
    | otherwise = M.singleton a1 t2
unify (TyVar a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = M.singleton a t
unify t (TyVar a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = M.singleton a t
unify (TyCon c1) (TyCon c2)
    | c1 == c2  = idSubst
    | otherwise = error "constructor clash"
unify (TyFun t1 t2) (TyFun t1' t2')
    = let s1 = unify (      t1) (      t1')
          s2 = unify (s1 $@ t2) (s1 $@ t2')
       in s2 $. s1
unify (TyPair t1 t2) (TyPair t1' t2')
    = let s1 = unify (      t1) (      t1')
          s2 = unify (s1 $@ t2) (s1 $@ t2')
       in s2 $. s1
unify (TyList t1) (TyList t2)
    = let s1 = unify t1 t2
       in s1
unify _ _
    = error "constructor clash"

-- | Inference algorithm

infer :: Env Ty -> Expr () -> InferM (Subst Ty, Ty, Expr Ty)
infer env (Var x ())
    | Just t <- M.lookup x env
        = do return (idSubst, t, Var x t)
    | otherwise
        = error $ "identifier '" ++ show x ++ "' not in scope " ++ show env
infer _env (Con con ())
    = do t <- typeOf con
         return (idSubst, t, Con con t)
infer env (Abs x e0 ())
    = do a1 <- fresh
         let env0 = M.insert x a1 env
         (s0, t0, e0') <- infer env0 e0
         let t' = TyFun (s0 $@ a1) t0
         return (s0, t', Abs x e0' t')
infer env (Fix f e0 ())
    = do a0 <- fresh
         let env0 = M.insert f a0 env
         (s0, t0, e0') <- infer env0 e0
         let s1 = unify t0 (s0 $@ a0)
         let t' = s1 $@ t0
         return (s1 $. s0, t', Fix f e0' t')
infer env (App e1 e2 ())
    = do (s1, t1, e1') <- infer        env  e1
         (s2, t2, e2') <- infer (s1 $@ env) e2
         a <- fresh
         let s3 = unify (s2 $@ t1) (TyFun t2 a)
         let t' = s3 $@ a
         return (s3 $. s2 $. s1, t', App e1' e2' t')
infer env (Let x e1 e2 ())
    -- FIXME: no let-bound polymorphism/generalization
    = do (s1, t1, e1') <- infer env e1
         let env2 = M.insert x t1 (s1 $@ env)
         (s2, t2, e2') <- infer env2 e2
         return (s2 $. s1, t2, Let x e1' e2' t2)
infer env (If lbl e0 e1 e2 ())
    = do (s0, t0, e0') <- infer              env  e0
         (s1, t1, e1') <- infer (      s0 $@ env) e1
         (s2, t2, e2') <- infer (s1 $. s0 $@ env) e2
         let s3 = unify (s2 $. s1 $@ t0) (TyCon TyBool)
         let s4 = unify (s3 $. s2 $@ t1) (s3 $@ t2)
         let t' = s4 $. s3 $@ t2
         return (s4 $. s3 $. s2 $. s1 $. s0, t', If lbl e0' e1' e2' t')
-- Operators
infer env (Op op@LEQ e1 e2 ())
    = do (s1, t1, e1') <- infer        env  e1
         (s2, t2, e2') <- infer (s1 $@ env) e2
         let s3 = unify (s2 $@ t1) (TyCon TyInt)
         let s4 = unify (s3 $@ t2) (TyCon TyInt)
         let t' = TyCon TyBool
         return (s4 $. s3 $. s2 $. s1, t', Op op e1' e2' t')
infer env (Op op@ADD e1 e2 ())
    = do (s1, t1, e1') <- infer        env  e1
         (s2, t2, e2') <- infer (s1 $@ env) e2
         let s3 = unify (s2 $@ t1) (TyCon TyInt)
         let s4 = unify (s3 $@ t2) (TyCon TyInt)
         let t' = TyCon TyInt
         return (s4 $. s3 $. s2 $. s1, t', Op op e1' e2' t')
-- Pairs
infer env (Pair e1 e2 ())
    = do (s1, t1, e1') <- infer        env  e1
         (s2, t2, e2') <- infer (s1 $@ env) e2
         let t' = TyPair (s2 $@ t1) t2
         return (s2 $. s1, t', Pair e1' e2' t')
infer env (Fst e0 ())
    = do (s0, t0, e0') <- infer env e0
         (a1, a2) <- fresh
         let s1 = unify t0 (TyPair a1 a2)
         let t' = s1 $@ a1
         return (s1 $. s0, t', Fst e0' t')
infer env (Snd e0 ())
    = do (s0, t0, e0') <- infer env e0
         (a1, a2) <- fresh
         let s1 = unify t0 (TyPair a1 a2)
         let t' = s1 $@ a2
         return (s1 $. s0, t', Snd e0' t')
-- Lists
infer _env (Nil ())
    = do a <- fresh
         let t = TyList a
         return (idSubst, t, Nil t)
infer env (Cons e1 e2 ())
    = do (s1, t1, e1') <- infer        env  e1
         (s2, t2, e2') <- infer (s1 $@ env) e2
         let s3 = unify t2 (TyList (s2 $@ t1))
         let t = TyList (s3 $. s2 $@ t1)
         return (s3 $. s2 $. s1, t, Cons e1' e2' t)
infer env (Case lbl e0 arm1 arm2 ())
    = do (s0, t0, e0') <- infer env e0
         a0 <- fresh
         let s0' = unify t0 (TyList a0)
         -- Nil arm
         (s1, t1, e1') <- case arm1 of
                            Just e1 -> infer (s0' $. s0 $@ env) e1
                            Nothing -> do a <- fresh
                                          let e = ExnC lbl PatternMatchFail
                                          return (idSubst, a, Con e a)
         -- Cons arm
         (x', xs') <- maybe fresh (\(x, xs, _) -> return (x, xs)) arm2
            -- FIXME: fresh names not guaranteed to be clash-free
         (s2, t2, e2') <- case arm2 of
                            Just (x, xs, e2) ->
                                infer (M.insert x  (s1 $. s0' $@ a0)
                                        (M.insert xs (TyList (s1 $. s0' $@ a0))
                                          (s1 $. s0' $. s0 $@ env)))
                                      e2
                            Nothing ->
                                do a <- fresh
                                   let e = ExnC lbl PatternMatchFail
                                   return (idSubst, a, Con e a)
         -- Return type
         let s3 = unify (s2 $@ t1) t2
         let t' = s3 $@ t2
         return ( s3 $. s2 $. s1 $. s0' $. s0, t'
                , Case lbl e0' (Just e1') (Just (x', xs', e2')) t' )
