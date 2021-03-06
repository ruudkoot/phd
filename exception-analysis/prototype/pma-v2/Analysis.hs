{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Analysis where

import Prelude hiding (($!))

import Control.Monad
import Control.Monad.State

import qualified Data.Graph      as G
import qualified Data.Graph.Util as G
import qualified Data.List       as L
import qualified Data.Map        as M
import qualified Data.Map.Util   as M
import           Data.Maybe
import qualified Data.Set        as S
import qualified Data.Set.Util   as S
import qualified Data.Tree       as T

import Common
import Constr

-- | Legacy 

injExn :: Exn -> Exn
injExn (Unif e) = Conc (S.singleton (ExnVar e))

-- | Abstract Syntax

data Expr' ann    -- annotated expression
    = Var'  Name                                     ann
    | Con'  Con                                      ann
    | Abs'  Name (Expr' ann)                         ann
    | Fix'  Name (Expr' ann)                         ann
    | App'       (Expr' ann) (Expr' ann)             ann
    | Let'  Name (Expr' ann) (Expr' ann)             ann
    | If'   Lbl  (Expr' ann) (Expr' ann) (Expr' ann) ann
    -- Operators
    | Op'   Op   (Expr' ann) (Expr' ann)             ann
    -- Pairs
    | Pair'      (Expr' ann) (Expr' ann)             ann
    | Fst'       (Expr' ann)                         ann
    | Snd'       (Expr' ann)                         ann
    -- List
    | Nil'                                           ann
    | Cons'      (Expr' ann) (Expr' ann)             ann
    | Case' Lbl  (Expr' ann) (Maybe (Expr' ann)) (Maybe (Name, Name, Expr' ann)) ann
    deriving (Eq, Ord, Show)

fakeType :: Expr -> Expr' Ty'
fakeType (Var x) = Var' x fake
fakeType (Con c) = Con' c fake
fakeType (Abs x e) = Abs' x (fakeType e) fake
fakeType (Fix f e) = Fix' f (fakeType e) fake
fakeType (App e1 e2) = App' (fakeType e1) (fakeType e2) fake
fakeType (Let x e1 e2) = Let' x (fakeType e1) (fakeType e2) fake
fakeType (If lbl e0 e1 e2) = If' lbl (fakeType e0) (fakeType e1) (fakeType e2) fake
fakeType (Op op e1 e2) = Op' op (fakeType e1) (fakeType e2) fake
fakeType (Pair e1 e2) = Pair' (fakeType e1) (fakeType e2) fake
fakeType (Fst e) = Fst' (fakeType e) fake
fakeType (Snd e) = Snd' (fakeType e) fake
fakeType Nil = Nil' fake
fakeType (Cons e1 e2) = Cons' (fakeType e1) (fakeType e2) fake
fakeType (Case lbl e0 arm1 arm2) = Case' lbl (fakeType e0) (fmap fakeType arm1) (fmap (\(x,xs,e2) -> (x, xs, fakeType e2)) arm2) fake

fake = TyCon' TyBool

-- | Static Semantics

-- * Annotations

type Ann = (Ref, Exn, Vrf)

-- * Types

data Ty'
    = TyVar' Name
    | TyCon' TyCon
    | TyFun' Ty' Ty'
    -- Pairs
    | TyPair' Ty' Ty'
    -- Lists
    | TyList' Ty'
    deriving (Eq, Ord, Show)

data Ty
    = TyVar Name
    | TyCon TyCon
    | TyFun Ty Ann Ty Ann
    -- Pairs
    | TyPair Ty Ann Ty Ann
    -- Lists
    | TyList Ty Ann
    deriving (Eq, Ord, Show)

data TyCon
    = TyBool
    | TyInt
    deriving (Eq, Ord, Show)
    
underlyingType :: Ty -> Ty'
underlyingType (TyVar  a        ) = TyVar' a
underlyingType (TyCon  c        ) = TyCon' c
underlyingType (TyFun  t1 _ t2 _) = TyFun' (underlyingType t1) (underlyingType t2)
underlyingType (TyPair t1 _ t2 _) = TyPair' (underlyingType t1) (underlyingType t2)
underlyingType (TyList t  _     ) = TyList' (underlyingType t)

alphaEquiv :: Ty' -> Ty' -> Bool    -- FIXME: crashes with an exception instead of False
alphaEquiv t1 t2
    = let s = unifyTy' t1 t2
       in all (\x -> case x of {TyVar' _ -> True; _ -> False}) (M.elems s)


-- * Refinements

type Ref = Elem Ref'

data Ref'
    = RefVar Name
    | RefTop
    | RefBool Bool
    | RefInt  Int'
    -- Lists
    | RefList List'
    deriving (Eq, Ord, Show)
    
data Int'
    = Neg
    | Zero
    | Pos
    deriving (Eq, Ord, Show)
    
data List'
    = E
    | NE
    deriving (Eq, Ord, Show)

injInt :: Int -> Int'
injInt n | n < 0     = Neg
         | n > 0     = Pos
         | otherwise = Zero

instance ConstrElem Ref' where
    demote (RefVar v) = Unif v
    demote refcon     = Conc (S.singleton refcon)
    
    injVar = RefVar
    prjVar (RefVar r) = r
              
type RefConstr = Constr Ref' -- FIXME: legacy?

-- * Exceptions

type Exn = Elem Exn'

data Exn'
    = ExnVar Name
    | ExnCrash Lbl
    deriving (Eq, Ord, Show)
    
instance ConstrElem Exn' where
    demote (ExnVar v) = Unif v
    demote exncon     = Conc (S.singleton exncon)
    
    injVar = ExnVar
    prjVar (ExnVar r) = r
    
type ExnConstr = Constr Exn' -- FIXME: legacy?
type ExnConstr' = Constr' Exn' -- FIXME: legacy?

-- * Verification conditions

type Vrf = Elem Vrf'

data Vrf'
    = VrfVar Name
    | VrfCon Lbl Ref (M.Map Ref' Exn) Exn
        -- FIXME: reconsider the type of the map in light of Main.solve2a
        --        (RefUnif -> Unif?)
    deriving (Eq, Ord, Show)

instance ConstrElem Vrf' where
    demote (VrfVar v) = Unif v
    demote exncon     = Conc (S.singleton exncon)
    
    injVar = VrfVar
    prjVar (VrfVar r) = r

type VrfConstr  = Constr  Vrf' -- FIXME: legacy?
type VrfConstr' = Constr' Vrf' -- FIXME: legacy?

-- * Type schemes

data TyScheme
    = Forall [Name] [Name] [Name] [Name] RefConstr ExnConstr VrfConstr Ty Ref Exn Vrf
    deriving (Eq, Ord, Show)

type TyEnv = M.Map Name TyScheme
    
-- | Miscellaneous injection and projection helpers

-- * Type schemes

injTS :: Ty -> Ref -> Exn -> Vrf -> TyScheme
injTS a ref exn vrf = Forall [] [] [] [] S.empty S.empty S.empty a ref exn vrf

-- | Derivation trees

data Rule
    = W' RefConstr ExnConstr VrfConstr TyEnv (Expr' Ty') Ty Ref Exn Vrf
    deriving (Eq, Ord, Show)

type Deriv = T.Tree (String, Rule)

-- * Debugging

extrEnv :: Deriv -> TyEnv
extrEnv = M.unionsWith mergeEnv . map extrEnv' . T.flatten where
    extrEnv' (_, W' _ _ _ env _ _ _ _ _) = env
    mergeEnv ts1 ts2 = if ts1 == ts2 then ts1 else error "incompatible environments"
    
-- | Inference Algorithm

-- * Types

type TyEnv' = M.Map Name Ty'

inferTy :: TyEnv' -> Expr -> InferM (TySubst, Ty', Expr' Ty')
inferTy env e@(Var x)
    | Just t <- M.lookup x env
        = do return (idSubst', t, Var' x t)
    | otherwise
        = error $ "identifier '" ++ show x ++ "' not in scope " ++ show env
inferTy env e@(Con con)
    = do t <- typeOf' con
         return (idSubst', t, Con' con t)
inferTy env e@(Abs x e0)
    = do a1 <- fresh
         let env0 = M.insert x a1 env
         (s0, t0, e0') <- inferTy env0 e0
         let t' = TyFun' (s0 $! a1) t0
         return (s0, t', Abs' x e0' t')
inferTy env e@(Fix f e0)
    = do a0 <- fresh
         let env0 = M.insert f a0 env
         (s0, t0, e0') <- inferTy env0 e0
         let s1 = unifyTy' t0 (s0 $! a0)
         let t' = s1 $! t0
         return (s1 $+ s0, t', Fix' f e0' t')
inferTy env e@(App e1 e2)
    = do (s1, t1, e1') <- inferTy        env  e1
         (s2, t2, e2') <- inferTy (s1 $! env) e2
         a <- fresh
         let s3 = unifyTy' (s2 $! t1) (TyFun' t2 a)
         let t' = s3 $! a
         return (s3 $+ s2 $+ s1, t', App' e1' e2' t')
inferTy env e@(Let x e1 e2)
    = do (s1, t1, e1') <- inferTy env e1
         -- no generalization here
         let env2 = M.insert x t1 (s1 $! env)
         (s2, t2, e2') <- inferTy env2 e2
         return (s2 $+ s1, t2, Let' x e1' e2' t2)
inferTy env e@(If lbl e0 e1 e2)
    = do (s0, t0, e0') <- inferTy              env  e0
         (s1, t1, e1') <- inferTy (      s0 $! env) e1
         (s2, t2, e2') <- inferTy (s1 $+ s0 $! env) e2
         let s3 = unifyTy' (s2 $+ s1 $! t0) (TyCon' TyBool)
         let s4 = unifyTy' (s3 $+ s2 $! t1) (s3 $! t2)
         let t' = s4 $+ s3 $! t2
         return (s4 $+ s3 $+ s2 $+ s1 $+ s0, t', If' lbl e0' e1' e2' t')
-- Operators
inferTy env e@(Op op@LEQ e1 e2)
    = do (s1, t1, e1') <- inferTy        env  e1
         (s2, t2, e2') <- inferTy (s1 $! env) e2
         let s3 = unifyTy' (s2 $! t1) (TyCon' TyInt)
         let s4 = unifyTy' (s3 $! t2) (TyCon' TyInt)
         let t' = TyCon' TyBool
         return (s4 $+ s3 $+ s2 $+ s1, t', Op' op e1' e2' t')
inferTy env e@(Op op@ADD e1 e2)
    = do (s1, t1, e1') <- inferTy        env  e1
         (s2, t2, e2') <- inferTy (s1 $! env) e2
         let s3 = unifyTy' (s2 $! t1) (TyCon' TyInt)
         let s4 = unifyTy' (s3 $! t2) (TyCon' TyInt)
         let t' = TyCon' TyInt
         return (s4 $+ s3 $+ s2 $+ s1, t', Op' op e1' e2' t')
-- Pairs
inferTy env e@(Pair e1 e2)
    = do (s1, t1, e1') <- inferTy        env  e1
         (s2, t2, e2') <- inferTy (s1 $! env) e2
         let t' = TyPair' (s2 $! t1) t2
         return (s2 $+ s1, t', Pair' e1' e2' t')
inferTy env e@(Fst e0)
    = do (s0, t0, e0') <- inferTy env e0
         (a1, a2) <- fresh
         let s1 = unifyTy' t0 (TyPair' a1 a2)
         let t' = s1 $! a1
         return (s1 $+ s0, t', Fst' e0' t')
inferTy env e@(Snd e0)
    = do (s0, t0, e0') <- inferTy env e0
         (a1, a2) <- fresh
         let s1 = unifyTy' t0 (TyPair' a1 a2)
         let t' = s1 $! a2
         return (s1 $+ s0, t', Snd' e0' t')
-- Lists
inferTy env e@Nil
    = do a <- fresh
         let t = TyList' a
         return (idSubst', t, Nil' t)
inferTy env e@(Cons e1 e2)
    = do (s1, t1, e1') <- inferTy        env  e1
         (s2, t2, e2') <- inferTy (s1 $! env) e2
         let s3 = unifyTy' t2 (TyList' (s2 $! t1))
         let t = TyList' (s3 $+ s2 $! t1)
         return (s3 $+ s2 $+ s1, t, Cons' e1' e2' t)
inferTy env e@(Case lbl e0 arm1 arm2)
    = do (s0, t0, e0') <- inferTy env e0
         a0 <- fresh
         let s0' = unifyTy' t0 (TyList' a0)
         -- Nil arm
         (s1, t1, e1') <- case arm1 of
                            Just e1 -> inferTy (s0' $+ s0 $! env) e1
                            Nothing -> do a <- fresh
                                          let e = ExnC lbl PatternMatchFail
                                          return (idSubst', a, Con' e a)
         -- Cons arm
         (x', xs') <- maybe (do {(q,w) <- fresh; return (augment "Q" q, augment "W" w)})(\(x, xs, _) -> return (x, xs)) arm2    -- FIXME: fresh not nicely named
         (s2, t2, e2') <- case arm2 of
                            Just (x, xs, e2) ->
                                inferTy (M.insert x  (s1 $+ s0' $! a0)
                                          (M.insert xs (TyList' (s1 $+ s0' $! a0))
                                            (s1 $+ s0' $+ s0 $! env)))
                                      e2
                            Nothing ->
                                do a <- fresh
                                   let e = ExnC lbl PatternMatchFail
                                   return (idSubst', a, Con' e a)
         -- Return type
         let s3 = unifyTy' (s2 $! t1) t2
         let t' = s3 $! t2
         return ( s3 $+ s2 $+ s1 $+ s0' $+ s0, t'
                , Case' lbl e0' (Just e1') (Just (x', xs', e2')) t' )

-- * Annotations

infer :: TyEnv -> Expr' Ty' -> InferM ( Subst
                                      , Ty
                                      , Ref, RefConstr
                                      , Exn, ExnConstr
                                      , Vrf, VrfConstr
                                      , Deriv, [Deriv]
                                      , Expr' Ann      )
infer env e
    = do (s1, t1, ref1, rc1, exn1, ec1, vrf1, vc1, d1, d1', e1') <- infer' env e

         -- FIXME: Constraint simplification (and sanity checks) go here

         -- Refinements
         let (rc2, rns2) = contractCycles . removeReflexive . decompose $ (s1 $@ rc1)
         let rs2 = Subst M.empty rns2
         let rc3 = removeReflexive (rs2 $@ rc2)
    
         -- Exceptions
         let (ec2, ens2) = contractCycles . removeReflexive . decompose $ (s1 $@ ec1)  -- FIXME apply rs2 as well?
         let es2 = Subst M.empty ens2
         let ec3 = removeReflexive (es2 $@ ec2)

         -- Verification conditions
         let (vc2, vns2) = contractCycles . removeReflexive . decompose $ (es2 $@ rs2 $@ s1 $@ vc1)
         let vs2 = Subst M.empty vns2
         let vc3 = removeReflexive (vs2 $@ vc2)

         return ( vs2 $. es2 $. rs2 $. s1, vs2 $@ es2 $@ rs2 $@ t1
                , rs2 $@ ref1, rc3
                , es2 $@ exn1, ec3
                , vs2 $@ vrf1, vc3
                , d1, d1', e1')

infer' :: TyEnv -> Expr' Ty' -> InferM ( Subst
                                       , Ty
                                       , Ref, RefConstr
                                       , Exn, ExnConstr
                                       , Vrf, VrfConstr
                                       , Deriv, [Deriv]
                                       , Expr' Ann      )
infer' env e@(Var' x ut)
    | Just ts <- M.lookup x env
        = do (t, ref, rc, exn, ec, vrf, vc) <- inst ts
             return ( idSubst, t, ref, rc, exn, ec, vrf, vc
                    , T.Node ("T-Var", W' rc ec vc env e t ref exn vrf) []
                    , []
                    , Var' x (ref, exn, vrf)                               )
    | otherwise
        = error $ "identifier '" ++ show x ++ "' not in scope " ++ show env

infer' env e@(Con' con ut)
    = do (t, ref, rc, exn, ec, vrf, vc) <- typeOf con
         return ( idSubst, t, ref, rc, exn, ec, vrf, vc
                , T.Node ("T-Con", W' rc ec vc env e t ref exn vrf) []
                , []
                , Con' con (ref, exn, vrf)                             )

infer' env e@(Abs' x e0 ut)
    = do (a1, ref1, exn1, vrf1) <- fresh
         let env0 = M.insert x (injTS a1 ref1 exn1 vrf1) env
         (s0, t0, ref0, rc0, exn0, ec0, vrf0, vc0, d0, d0', e0') <- infer env0 e0
         (ref', exn', vrf') <- fresh -- FIXME: {lambda} :<: ref'
         let t' = TyFun (s0 $@ a1) (s0 $@ ref1, s0 $@ exn1, s0 $@ vrf1)
                               t0  (      ref0,       exn0,       vrf0)
         return ( s0, t', ref', rc0, exn', ec0, vrf', vc0
                , T.Node ("T-Abs", W' rc0 ec0 vc0 env e t' ref' exn' vrf') [d0]
                , d0'
                , Abs' x e0' (ref', exn', vrf')                                 )

infer' env e@(Fix' f e0 ut)
    = do (a0, refy, exny, vrfy) <- fresh
         
         let env0 = M.insert f (injTS a0 refy exny vrfy) env

         (s0, t0, ref0, rc0, exn0, ec0, vrf0, vc0, d0, d0', e0') <- infer env0 e0

         let s1 = unify                        t0   (                   s0 $@   a0)
         let s2 = unify' (s1 $@ (ref0, exn0, vrf0)) (s1 $@ s0 $@ (refy, exny, vrfy))

         let t' = s2 $@ s1       $@   t0

         let ref' = s2 $@ s1 $@ s0 $@ ref0
         let exn' = s2 $@ s1 $@ s0 $@ exn0
         let vrf' = s2 $@ s1 $@ s0 $@ vrf0

         let rc'  = s2 $@ s1 $@ rc0
         let ec'  = s2 $@ s1 $@ ec0
         let vc'  = s2 $@ s1 $@ vc0

         return ( s2 $. s1 $. s0, t', ref', rc', exn', ec', vrf', vc'
                , T.Node ("T-Fix", W' rc' ec' vc' env e t' ref' exn' vrf') [d0]
                , d0'
                , Fix' f e0' (ref', exn', vrf')                                 )

infer' env e@(App' e1 e2 ut)
    = do (s1, t1, ref1, rc1, exn1, ec1, vrf1, vc1, d1, d1', e1') <- infer        env  e1
         (s2, t2, ref2, rc2, exn2, ec2, vrf2, vc2, d2, d2', e2') <- infer (s1 $@ env) e2

         (a, ref, exn, vrf) <- fresh

         let s3 = unify (s2 $@ t1) (TyFun t2 (ref2, exn2, vrf2) a (ref, exn, vrf))

         let t' = s3 $@ a
         (ref', exn', vrf') <- fresh
         let rc' = (Conc (effectRef [s3 $@ ref, s3 $@ s2 $@ ref1]) :<: ref')
                    `S.insert` (s3 $@ s2 $@ rc1) `S.union` (s3 $@ rc2)
         let ec' = (Conc (effectExn [s3 $@ exn, s3 $@ s2 $@ exn1]) :<: exn')
                    `S.insert` (s3 $@ s2 $@ ec1) `S.union` (s3 $@ ec2)
         let vc' = (Conc (effectVrf [s3 $@ vrf, s3 $@ s2 $@ vrf1]) :<: vrf')
                    `S.insert` (s3 $@ s2 $@ vc1) `S.union` (s3 $@ vc2)

         return ( s3 $. s2 $. s1, t', ref', rc', exn', ec', vrf', vc'
                , T.Node ("T-App", W' rc' ec' vc' env e t' ref' exn' vrf') [d1, d2]
                , d1' ++ d2'
                , App' e1' e2' (ref', exn', vrf')                                   )

infer' env e@(Let' x e1 e2 ut)
    = do (s1, t1, ref1, rc1, exn1, ec1, vrf1, vc1, d1, d1', e1') <- infer env e1

         let ts1  = gen (s1 $@ env) ref1 rc1 exn1 ec1 vrf1 vc1 t1
         let env2 = M.insert x ts1 (s1 $@ env)
         (s2, t2, ref2, rc2, exn2, ec2, vrf2, vc2, d2, d2', e2') <- infer env2 e2

         let rc' = rc2 `S.union` (s2 $@ rc1)
         let ec' = ec2 `S.union` (s2 $@ ec1)
         let vc' = vc2 `S.union` (s2 $@ vc1)

         return ( s2 $. s1, t2, ref2, rc', exn2, ec', vrf2, vc'
                , T.Node ("T-Let", W' rc' ec' vc' env e t2 ref2 exn2 vrf2) [d2]
                , d1 : (d1' ++ d2')
                , Let' x e1' e2' (ref2, exn2, vrf2)                                 )

infer' env e@(If' lbl e0 e1 e2 ut)  -- FIXME: ref0 not used (not context-sensitive)
    = do (s0, t0, ref0, rc0, exn0, ec0, vrf0, vc0, d0, d0', e0') <- infer            env  e0
         (s1, t1, ref1, rc1, exn1, ec1, vrf1, vc1, d1, d1', e1') <- infer (    s0 $@ env) e1
         (s2, t2, ref2, rc2, exn2, ec2, vrf2, vc2, d2, d2', e2') <- infer (s1$@s0 $@ env) e2

         let s3 = unify (s2 $@ s1 $@ t0) (TyCon TyBool)
         let s4 = unify (s3 $@ s2 $@ t1) (s3 $@ t2)

         let t' = s4 $@ s3 $@ t2

         -- Refinements
         ref' <- fresh
         let rc' = (s4 $@ s3 $@ s2 $@ s1 $@ rc0)
                  `S.union` (s4 $@ s3 $@ s2 $@ rc1) `S.union` (s4 $@ s3 $@ rc2)
                  `S.union` S.fromList [ s4 $@ s3 $@ s2 $@ ref1 :<: ref'
                                       , s4 $@ s3 $@ ref2       :<: ref' ]

         -- Exceptions
         exn' <- fresh
         let ec' = (s4 $@ s3 $@ s2 $@ s1 $@ ec0)
                  `S.union` (s4 $@ s3 $@ s2 $@ ec1) `S.union` (s4 $@ s3 $@ ec2)
                  `S.union` S.fromList [ s4 $@ s3 $@ s2 $@ s1 $@ exn0 :<: exn' ]

         -- Verification conditions
         let vc = VrfCon lbl
                         ref0
                         (M.fromList [ (RefBool True , exn1)
                                     , (RefBool False, exn2) ])
                         exn'
         vrf' <- fresh
         let vc' = S.singleton (Conc (S.singleton vc) :<: vrf')
                  `S.union` S.fromList [ s4 $@ s3 $@ s2 $@ s1 $@ vrf0 :<: vrf'
                                       , s4 $@ s3 $@ s2       $@ vrf1 :<: vrf'
                                       , s4 $@ s3             $@ vrf2 :<: vrf' ]
                  `S.union` (s4 $@ s3 $@ s2 $@ s1 $@ vc0)
                  `S.union` (s4 $@ s3 $@ s2 $@ vc1)
                  `S.union` (s4 $@ s3 $@ vc2)

         return ( s4 $. s3 $. s2 $. s1 $. s0, t', ref', rc', exn', ec', vrf', vc'
                , T.Node ("T-If", W' rc' ec' vc' env e t' ref' exn' vrf') [d0, d1, d2]
                , d0' ++ d1' ++ d2'
                , If' lbl e0' e1' e2' (ref', exn', vrf')                               )

-- Operators
infer' env e@(Op' op@LEQ e1 e2 ut) -- FIXME: ref1 and ref2 not used
    = do (s1, t1, ref1, rc1, exn1, ec1, vrf1, vc1, d1, d1', e1') <- infer        env  e1
         (s2, t2, ref2, rc2, exn2, ec2, vrf2, vc2, d2, d2', e2') <- infer (s1 $@ env) e2

         let s3 = unify (s2 $@ t1) (TyCon TyInt)
         let s4 = unify (s3 $@ t2) (TyCon TyInt)

         let t' = TyCon TyBool

         -- Refinements
         ref' <- fresh
         let rc' = (s4 $@ s3 $@ s2 $@ rc1) `S.union` (s4 $@ s3 $@ rc2) `S.union`
                     S.singleton (Conc (S.fromList [ RefBool True
                                                     , RefBool False ]) :<: ref')

         -- Exceptions
         exn' <- fresh
         let ec' = (s4 $@ s3 $@ s2 $@ ec1) `S.union` (s4 $@ s3 $@ ec2) `S.union`
                    S.fromList [ s4 $@ s3 $@ s2 $@ exn1 :<: exn'
                               , s4 $@ s3 $@       exn2 :<: exn' ]
         
         -- Verfication conditions
         vrf' <- fresh
         let vc' = (s4 $@ s3 $@ s2 $@ vc1) `S.union` (s4 $@ s3 $@ vc2)

         return ( s4 $. s3 $. s2 $. s1, t', ref', rc', exn', ec', vrf', vc'
                , T.Node ("T-Op", W' rc' ec' vc' env e t' ref' exn' vrf') [d1, d2]
                , d1' ++ d2'
                , Op' op e1' e2' (ref', exn', vrf')                                )

infer' env e@(Op' op@ADD e1 e2 ut) -- FIXME: ref1 and ref2 not used
    = do (s1, t1, ref1, rc1, exn1, ec1, vrf1, vc1, d1, d1', e1') <- infer        env  e1
         (s2, t2, ref2, rc2, exn2, ec2, vrf2, vc2, d2, d2', e2') <- infer (s1 $@ env) e2

         let s3 = unify (s2 $@ t1) (TyCon TyInt)
         let s4 = unify (s3 $@ t2) (TyCon TyInt)

         let t' = TyCon TyInt

         -- Refinements
         ref' <- fresh
         let rc' = (s4 $@ s3 $@ s2 $@ rc1) `S.union` (s4 $@ s3 $@ rc2) `S.union`
                     S.singleton (Conc (S.fromList [ RefInt Neg
                                                     , RefInt Zero
                                                     , RefInt Pos  ]) :<: ref')

         -- Exceptions
         exn' <- fresh
         let ec' = (s4 $@ s3 $@ s2 $@ ec1) `S.union` (s4 $@ s3 $@ ec2) `S.union`
                    S.fromList [ s4 $@ s3 $@ s2 $@ exn1 :<: exn'
                               , s4 $@ s3 $@       exn2 :<: exn' ]

         -- Verification conditions
         vrf' <- fresh
         let vc' = (s4 $@ s3 $@ s2 $@ vc1) `S.union` (s4 $@ s3 $@ vc2)

         return ( s4 $. s3 $. s2 $. s1, t', ref', rc', exn', ec', vrf', vc'
                , T.Node ("T-Op", W' rc' ec' vc' env e t' ref' exn' vrf') [d1, d2]
                , d1' ++ d2'
                , Op' op e1' e2' (ref', exn', vrf')                                )

-- Pairs
infer' env e@(Pair' e1 e2 ut)
    = do (s1, t1, ref1, rc1, exn1, ec1, vrf1, vc1, d1, d1', e1') <- infer        env  e1
         (s2, t2, ref2, rc2, exn2, ec2, vrf2, vc2, d2, d2', e2') <- infer (s1 $@ env) e2

         let t' = TyPair (s2 $@ t1) (s2 $@ ref1,  s2$@ exn1, s2 $@ vrf1)
                                t2  (      ref2,       exn2,       vrf2)

         (ref', exn', vrf') <- fresh
         let rc' = s2 $@ rc1 `S.union` rc2
         let ec' = s2 $@ ec1 `S.union` ec2
         let vc' = s2 $@ vc1 `S.union` vc2

         return ( s2 $. s1, t', ref', rc', exn', ec', vrf', vc'
                , T.Node ("T-Pair", W' rc' ec' vc' env e t' ref' exn' vrf') [d1, d2]
                , d1' ++ d2'
                , Pair' e1' e2' (ref', exn', vrf')                                   )

infer' env e@(Fst' e0 ut)
    = do (s0, t0, ref0, rc0, exn0, ec0, vrf0, vc0, d0, d0', e0') <- infer env e0

         (a1, b1@(ref1, exn1, vrf1), a2, b2) <- fresh
         let s1 = unify t0 (TyPair a1 b1 a2 b2)

         let t' = s1 $@ a1

         -- Refinements
         let ref' = s1 $@ ref1
         let rc'  = s1 $@ rc0
         
         -- Exceptions
         exn' <- fresh
         let ec' = s1 $@ ec0 `S.union` S.fromList [exn0 :<: exn', exn1 :<: exn']
         
         -- Verification conditions
         vrf' <- fresh
         let vc' = s1 $@ vc0 `S.union` S.fromList [vrf0 :<: vrf', vrf1 :<: vrf']

         return ( s1 $. s0, t', ref', rc', exn', ec', vrf', vc'
                , T.Node ("T-Fst", W' rc' ec' vc' env e t' ref' exn' vrf') [d0]
                , d0'
                , Fst' e0' (ref', exn', vrf')                                   )

infer' env e@(Snd' e0 ut)
    = do (s0, t0, ref0, rc0, exn0, ec0, vrf0, vc0, d0, d0', e0') <- infer env e0

         (a1, b1, a2, b2@(ref2, exn2, vrf2)) <- fresh
         let s1 = unify t0 (TyPair a1 b1 a2 b2)

         let t' = s1 $@ a2

         -- Refinements
         let ref' = s1 $@ ref2
         let rc'  = s1 $@ rc0
         
         -- Exceptions
         exn' <- fresh
         let ec' = s1 $@ ec0 `S.union` S.fromList [exn0 :<: exn', exn2 :<: exn']
         
         -- Verification conditions
         vrf' <- fresh
         let vc' = s1 $@ vc0 `S.union` S.fromList [vrf0 :<: vrf', vrf2 :<: vrf']

         return ( s1 $. s0, t', ref', rc', exn', ec', vrf', vc'
                , T.Node ("T-Snd", W' rc' ec' vc' env e t' ref' exn' vrf') [d0]
                , d0'
                , Snd' e0' (ref', exn', vrf')                                   )

-- Lists
infer' env e@(Nil' ut)
    = do (a, b@(_,_,_)) <- fresh
         let t = TyList a b

         -- Refinements
         ref' <- fresh
         let rc = S.singleton (Conc (S.singleton (RefList E)) :<: ref')
         
         -- Exceptions
         exn' <- fresh
         let ec = S.empty
         
         -- Verification conditions
         vrf' <- fresh
         let vc = S.empty

         return ( idSubst, t, ref', rc, exn', ec, vrf', vc
                , T.Node ("T-Nil", W' rc ec vc env e t ref' exn' vrf') []
                , []
                , Nil' (ref', exn', vrf')                                 )

infer' env e@(Cons' e1 e2 ut)
    = do (s1, t1, ref1, rc1, exn1, ec1, vrf1, vc1, d1, d1', e1') <- infer        env  e1
         (s2, t2, ref2, rc2, exn2, ec2, vrf2, vc2, d2, d2', e2') <- infer (s1 $@ env) e2

         q@(qr,qe,qv) <- fresh
         let s3 = unify t2 (TyList (s2 $@ t1) q)

         b1q@(b1qr,b1qe,b1qv) <- fresh
         let t = TyList (s3 $@ s2 $@ t1) b1q

         -- Refinements
         ref' <- fresh
         let rc' = S.fromList [ Conc (S.singleton (RefList NE)) :<: ref'
                              , s3 $@ s2 $@ ref1                  :<: b1qr
                              , s3 $@ qr                          :<: b1qr ]
                   `S.union` (s3 $@ s2 $@ rc1) `S.union` (s3 $@ rc2)
                 
         -- Exceptions
         let exn' = exn2
         let ec' = S.fromList [ s3 $@ s2 $@ exn1 :<: b1qe
                              , s3 $@ qe         :<: b1qe
                           -- , s3 $@ exn2       :<: b2 -- FIXME: or should b2 B fresh?
                              ]
                   `S.union` (s3 $@ s2 $@ ec1) `S.union` (s3 $@ ec2)
         
         -- Verification conditions
         let vrf' = vrf2
         let vc' = S.fromList [ s3 $@ s2 $@ vrf1 :<: b1qv
                              , s3 $@ qv         :<: b1qv
                           -- , s3 $@ exn2       :<: b2 -- FIXME: or should b2 B fresh?
                              ]
                   `S.union` (s3 $@ s2 $@ vc1) `S.union` (s3 $@ vc2)
         
         return ( s3 $. s2 $. s1, t, ref', rc', exn', ec', vrf', vc'
                , T.Node ("T-Cons", W' rc' ec' vc' env e t ref' exn' vrf') [d1, d2]
                , d1' ++ d2'
                , Cons' e1' e2' (ref', exn', vrf')                                  )

infer' env e@(Case' lbl e0 arm1 arm2 ut)
    = do -- Scrutinee
         (s0, t0, ref0, rc0, exn0, ec0, vrf0, vc0, d0, d0', e0') <- infer env e0
         (a0, br0, be0, bv0) <- fresh
         let s0' = unify t0 (TyList a0 (br0, be0, bv0))
         
         -- Nil arm
         (s1, t1, ref1, rc1, exn1, ec1, vrf1, vc1, d1, d1', e1')
            <- case arm1 of
                Just e1 ->
                    infer (s0' $@ s0 $@ env) e1
                Nothing ->
                    do (a, (br, be, bv)) <- fresh
                       let e = ExnC lbl PatternMatchFail
                       let ec = S.singleton (Conc (S.singleton (ExnCrash lbl)) :<: be)
                       return ( idSubst, a, br, S.empty, be, ec, bv, S.empty
                              , T.Node ( "T-Case-Nil"
                                       , W' S.empty ec S.empty env
                                           (Con' e (underlyingType a)) a br be bv
                                       ) []
                              , []
                              , Con' e (br, be, bv)                                    )

         -- Cons arm
         (x', xs') <- maybe (do {(q,w) <- fresh; return (augment "Q" q, augment "W" w)})(\(x, xs, _) -> return (x, xs)) arm2    -- FIXME: fresh not nicely named
         
         refCONS <- fresh

         (s2, t2, ref2, rc2, exn2, ec2, vrf2, vc2, d2, d2', e2')
            <- case arm2 of
                Just (x, xs, e2) ->
                    infer (M.insert x  (injTS (s1 $@ s0' $@ a0)  (s1 $@ s0' $@ br0)
                                              (s1 $@ s0' $@ be0) (s1 $@ s0' $@ bv0))
                          (M.insert xs
                                (injTS (TyList (s1 $@ s0' $@ a0)
                                               (s1 $@ s0' $@ (br0,be0,bv0)))
                                       refCONS (s1 $@ s0' $@ exn0) (s1 $@ s0' $@ vrf0))
                                                 -- FIXME: test with ref0 to
                                                 -- see if we can detect the
                                                 -- unsoundness (yes we can)
                          (s1 $@ s0' $@ s0 $@ env)))
                          e2
                Nothing ->
                    do (a, (br,be,bv)) <- fresh
                       let e = ExnC lbl PatternMatchFail
                       let ec = S.singleton (Conc (S.singleton (ExnCrash lbl)) :<: be)
                       return ( idSubst, a, br, S.empty, be, ec, bv, S.empty
                              , T.Node ( "T-Case-Cons"
                                       , W' S.empty ec S.empty env
                                           (Con' e (underlyingType a)) a br be bv
                                       ) []
                              , []
                              , Con' e (br, be, bv)                                  )

         -- Return type
         let s3 = unify (s2 $@ t1) t2
         let t' = s3 $@ t2

         ref' <- fresh
         let rc' = (s3 $@ s2 $@ s1 $@ s0' $@ rc0)
                   `S.union` (s3 $@ s2 $@ rc1) `S.union` (s3 $@ rc2)
                   `S.union` S.fromList [ s3 $@ s2 $@ ref1                 :<: ref'
                                        , s3 $@       ref2                 :<: ref'
                                        , Conc (S.fromList [ RefList E
                                                             , RefList NE ] ) :<: refCONS ]

         exn' <- fresh
         let ec' = (s3 $@ s2 $@ s1 $@ s0' $@ ec0)
                   `S.union` (s3 $@ s2 $@ ec1) `S.union` (s3 $@ ec2)
                   `S.union` S.fromList [ s3 $@ s2 $@ s1 $@ s0' $@ exn0 :<: exn' ]

         vrf' <- fresh
         let vc = VrfCon lbl
                         ref0
                         (M.fromList [ (RefList E , exn1)
                                     , (RefList NE, exn2) ])
                         exn'
         let vc' = S.singleton (Conc (S.singleton vc) :<: vrf')
                   `S.union` S.fromList [ s3 $@ s2 $@ s1 $@ s0' $@ vrf0 :<: vrf'
                                        , s3 $@ s2              $@ vrf1 :<: vrf'
                                        , s3                    $@ vrf2 :<: vrf' ]
                   `S.union` (s3 $@ s2 $@ s1 $@ s0' $@ vc0)
                   `S.union` (s3 $@ s2 $@ vc1)
                   `S.union` (s3 $@ vc2)

         return ( s3 $. s2 $. s1 $. s0' $. s0, t', ref', rc', exn', ec', vrf', vc'
                , T.Node ("T-Case", W' rc' ec' vc' env e t' ref' exn' vrf') [d0, d1, d2]
                , d0' ++ d1' ++ d2'
                , Case' lbl e0' (Just e1') (Just (x', xs', e2')) (ref', exn', vrf'))

effectRef = S.fromList . map (\(Unif u) -> RefVar u)
effectExn = S.fromList . map (\(Unif u) -> ExnVar u)
effectVrf = S.fromList . map (\(Unif u) -> VrfVar u)

-- * Instantiation

inst :: TyScheme -> InferM (Ty, Ref, RefConstr, Exn, ExnConstr, Vrf, VrfConstr)
inst (Forall as rq eq vq rc ec vc t ref exn vrf)
    = do as' <- replicateM (length as) fresh
         rq' <- replicateM (length rq) (fresh' "beta")
         eq' <- replicateM (length eq) (fresh' "chi" )
         vq' <- replicateM (length vq) (fresh' "nu"  )
         let r = Subst (M.fromList (zip as as'))
                       (M.fromList (zip rq rq' ++ zip eq eq' ++ zip vq vq'))
         return (r $@ t, r $@ ref, r $@ rc, r $@ exn, r $@ ec, r $@ vrf, r $@ vc)

fresh' :: String -> InferM Name
fresh' tag = do b <- fresh
                return (augment ("\\" ++ tag) b)

-- | Generalization

-- TODO: let-bound polymorphism and polyvariance
gen :: TyEnv -> Ref -> RefConstr -> Exn -> ExnConstr -> Vrf -> VrfConstr -> Ty
                                                                    -> TyScheme
gen env ref rc exn ec vrf vc t
    = let (rt, et, vt) = biClose rc ec vc (frv t) (fxv t) (fvv t)
          (rd, ed, vd) = downClose rc ec vc (frv env `S.union` frv ref)
                                            (fxv env `S.union` fxv exn)
                                            (fvv env `S.union` fvv vrf)

          tq  = ftv t `S.difference` ftv env          

          rq  = rt `S.difference` rd
          eq  = et `S.difference` ed
          vq  = vt `S.difference` vd
          
          rc' = S.filter (\c -> frv c `S.overlap` rq) rc
          ec' = S.filter (\c -> fxv c `S.overlap` eq) ec
          vc' = S.filter (\c -> fav c `S.overlap` (rq `S.union` eq `S.union` vq)) vc

          ts  = Forall (S.toList tq) (S.toList rq) (S.toList eq) (S.toList vq)
                       rc' ec' vc' t ref exn vrf
          
          (ru, eu, vu) = upClose rc' ec' vc' rq eq vq
       in if rq == ru && eq == eu && vq == vu then ts
                                              else error "type scheme ill-formed"
       
-- * Closures (2nd attempt)

fixPoint f x
    = let x' = f x in if x == x' then x else fixPoint f x'

noClose rc ec vc rq eq vq
    = (rq, rq, vq)

biClose :: RefConstr -> ExnConstr -> VrfConstr ->
    S.Set Name -> S.Set Name -> S.Set Name ->
    (S.Set Name, S.Set Name, S.Set Name)
biClose rc ec vc rq eq vq
    = fixPoint f (rq, eq, vq) where
        f q@(rq, eq, vq)
            = S.foldr gv (S.foldr ge (S.foldr gr q rc) ec) vc
        gr c (rq, eq, vq)
            = (rq `S.union` frv c, eq                , vq                )
        ge c (rq, eq, vq)
            = (rq                , eq `S.union` fxv c, vq                )
        gv c (rq, eq, vq)
            = (rq `S.union` frv c, eq `S.union` fxv c, vq `S.union` fvv c)
            
downClose rc ec vc rq eq vq
    = fixPoint f (rq, eq, vq) where
        f q@(rq, eq, vq)
            = S.foldr gv (S.foldr ge (S.foldr gr q rc) ec) vc
        gr (ref1 :<: ref2) q@(rq, eq, vq)
            | fav ref2 `S.overlap` (rq `S.union` eq `S.union` vq)
                = (rq `S.union` frv ref1, eq `S.union` fxv ref1, vq `S.union` fvv ref1)
            | otherwise = q
        ge (exn1 :<: exn2) q@(rq, eq, vq)
            | fav exn2 `S.overlap` (rq `S.union` eq `S.union` vq)
                = (rq `S.union` frv exn1, eq `S.union` fxv exn1, vq `S.union` fvv exn1)
            | otherwise = q
        gv (vrf1 :<: vrf2) q@(rq, eq, vq)
            | fav vrf2 `S.overlap` (rq `S.union` eq `S.union` vq)
                = (rq `S.union` frv vrf1, eq `S.union` fxv vrf1, vq `S.union` fvv vrf1)
            | otherwise = q

upClose rc ec vc rq eq vq
    = fixPoint f (rq, eq, vq) where
        f q@(rq, eq, vq)
            = S.foldr gv (S.foldr ge (S.foldr gr q rc) ec) vc
        gr (ref2 :<: ref1) q@(rq, eq, vq)
            | fav ref2 `S.overlap` (rq `S.union` eq `S.union` vq)
                = (rq `S.union` frv ref1, eq `S.union` fxv ref1, vq `S.union` fvv ref1)
            | otherwise = q
        ge (exn2 :<: exn1) q@(rq, eq, vq)
            | fav exn2 `S.overlap` (rq `S.union` eq `S.union` vq)
                = (rq `S.union` frv exn1, eq `S.union` fxv exn1, vq `S.union` fvv exn1)
            | otherwise = q
        gv (vrf2 :<: vrf1) q@(rq, eq, vq)
            | fav vrf2 `S.overlap` (rq `S.union` eq `S.union` vq)
                = (rq `S.union` frv vrf1, eq `S.union` fxv vrf1, vq `S.union` fvv vrf1)
            | otherwise = q

-- | Unification

-- * Underlying types

unifyTy' :: Ty' -> Ty' -> TySubst
unifyTy' (TyVar' a1) t2@(TyVar' a2)
    | a1 == a2  = idSubst'
    | otherwise = M.singleton a1 t2
unifyTy' (TyVar' a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = M.singleton a t
unifyTy' t (TyVar' a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = M.singleton a t
unifyTy' (TyCon' c1) (TyCon' c2)
    | c1 == c2  = idSubst'
    | otherwise = error "constructor clash"
unifyTy' (TyFun' t1 t2) (TyFun' t1' t2')
    = let s3 = unifyTy' (      t1) (      t1')
          s4 = unifyTy' (s3 $! t2) (s3 $! t2')
       in s4 $+ s3
-- Pairs
unifyTy' (TyPair' t1 t2) (TyPair' t1' t2')
    = let s3 = unifyTy' (      t1) (      t1')
          s4 = unifyTy' (s3 $! t2) (s3 $! t2')
       in s4 $+ s3
-- Lists
unifyTy' (TyList' t1) (TyList' t2)
    = let s1 = unifyTy' t1 t2
       in s1
unifyTy' _ _
    = error "constructor clash"

-- * Annotated types

unify :: Ty -> Ty -> Subst
unify (TyVar a1) t2@(TyVar a2)
    | a1 == a2  = Subst M.empty             M.empty
    | otherwise = Subst (M.singleton a1 t2) M.empty
unify (TyVar a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = Subst (M.singleton a t) M.empty
unify t (TyVar a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = Subst (M.singleton a t) M.empty
unify (TyCon c1) (TyCon c2)
    | c1 == c2  = idSubst
    | otherwise = error "constructor clash"
unify (TyFun t1 ann1 t2 ann2) (TyFun t1' ann1' t2' ann2')
    = let s1 = unify' (                  ann1) (                  ann1')
          s2 = unify' (            s1 $@ ann2) (            s1 $@ ann2')
          s3 = unify  (      s2 $@ s1 $@ t1  ) (      s2 $@ s1 $@ t1'  )
          s4 = unify  (s3 $@ s2 $@ s1 $@ t2  ) (s3 $@ s2 $@ s1 $@ t2'  )
       in s4 $. s3 $. s2 $. s1
-- Pairs
unify (TyPair t1 ann1 t2 ann2) (TyPair t1' ann1' t2' ann2')
    = let s1 = unify' (                  ann1) (                  ann1')
          s2 = unify' (            s1 $@ ann2) (            s1 $@ ann2')
          s3 = unify  (      s2 $@ s1 $@ t1  ) (      s2 $@ s1 $@ t1'  )
          s4 = unify  (s3 $@ s2 $@ s1 $@ t2  ) (s3 $@ s2 $@ s1 $@ t2'  )
       in s4 $. s3 $. s2 $. s1
-- Lists
unify (TyList t1 ann1) (TyList t2 ann2)
    = let s1 = unify'        ann1         ann2
          s2 = unify  (s1 $@ t1  ) (s1 $@ t2  )
       in s2 $. s1
unify _ _
    = error "constructor clash"

unify' :: Ann -> Ann -> Subst
unify' (Unif r1, Unif e1, Unif v1) (Unif r2, Unif e2, Unif v2)
    = Subst M.empty ((if r1 /= r2 then M.insert r1 r2 else id)
                     ((if e1 /= e2 then M.insert e1 e2 else id)
                     ((if v1 /= v2 then M.insert v1 v2 else id) M.empty)))
unify' ann1 ann2
    = error $ "not a simple type: ann1 = " ++ show ann1 ++ ", ann2 = " ++ show ann2

-- | Typing of constants

typeOf :: Con -> InferM (Ty, Ref, RefConstr, Exn, ExnConstr, Vrf, VrfConstr)
typeOf (Bool x)
    = do (ref, exn, vrf) <- fresh
         return ( TyCon TyBool
                , ref, S.singleton (Conc (S.singleton (RefBool x        )) :<: ref)
                , exn, S.empty
                , vrf, S.empty                                                     )
typeOf (Int n)
    = do (ref, exn, vrf) <- fresh
         return ( TyCon TyInt
                , ref, S.singleton (Conc (S.singleton (RefInt (injInt n))) :<: ref)
                , exn, S.empty
                , vrf, S.empty                                                     )
typeOf (ExnC lbl _)
    = do (a, ref, exn, vrf) <- fresh
         return ( a
                , ref, S.empty
                , exn, S.singleton (Conc (S.singleton (ExnCrash lbl)) :<: exn)
                , vrf, S.empty                                                )

typeOf' :: Con -> InferM Ty'
typeOf' (Bool x)
    = return (TyCon' TyBool)
typeOf' (Int n)
    = return (TyCon' TyInt)
typeOf' (ExnC lbl _)
    = do a <- fresh
         return a

-- | Constraint solving (assumes constraints have been decomposed and decycled!)
                   -- FIXME: solver should take care of prepocessing the constraint set

type RefSubst = M.Map Name Ref -- FIXME: newtype

initSubst :: Ty -> RefConstr -> Expr' Ann -> RefSubst
initSubst t c e' = S.foldr (\k -> M.insert k (Conc S.empty)) M.empty (frv t `S.union` frv c `S.union` frv e')

type ExnSubst = M.Map Name Exn

exnInitSubst :: Ty -> ExnConstr -> Expr' Ann -> ExnSubst
exnInitSubst t c e' = S.foldr (\k -> M.insert k (Conc S.empty)) M.empty (fxv t `S.union` fxv c `S.union` fxv e')

type VrfSubst = M.Map Name Vrf

vrfInitSubst :: Ty -> VrfConstr -> Expr' Ann -> VrfSubst
vrfInitSubst t c e' = S.foldr (\k -> M.insert k (Conc S.empty)) M.empty (fvv t `S.union` fvv c `S.union` fvv e')

-- | Free variables

class FreeVars a where
    ftv :: a -> S.Set Name
    frv :: a -> S.Set Name
    fxv :: a -> S.Set Name
    fvv :: a -> S.Set Name
    fav :: a -> S.Set Name
    fav x = frv x `S.union` fxv x `S.union` fvv x
    
instance FreeVars (Expr' Ann) where
    ftv = error "DF.ftv_Expr'"

    frv (Var'    _        (ref,_,_)) 
        = frv ref
    frv (Con'    _        (ref,_,_))
        = frv ref
    frv (Abs'    _  e     (ref,_,_))
        = frv ref `S.union` frv e
    frv (Fix'    _  e     (ref,_,_))
        = frv ref `S.union` frv e
    frv (App'    e1 e2    (ref,_,_))  
        = frv ref `S.union` frv e1 `S.union` frv e2
    frv (Let'    _  e1 e2 (ref,_,_))
        = frv ref `S.union` frv e1 `S.union` frv e2
    frv (If'   _ e0 e1 e2 (ref,_,_))
        = frv ref `S.union` frv e0 `S.union` frv e1 `S.union` frv e2
    -- Operators
    frv (Op'     op e1 e2 (ref,_,_))
        = frv ref `S.union` frv e1 `S.union` frv e2
    -- Pairs
    frv (Pair'   e1 e2    (ref,_,_))
        = frv ref `S.union` frv e1 `S.union` frv e2
    frv (Fst'    e        (ref,_,_))
        = frv ref `S.union` frv e
    frv (Snd'    e        (ref,_,_))  
        = frv ref `S.union` frv e
    -- Lists
    frv (Nil'             (ref,_,_))  
        = frv ref
    frv (Cons'   e1 e2    (ref,_,_))
        = frv ref `S.union` frv e1 `S.union` frv e2
    frv (Case' _ e0 e1 e2 (ref,_,_))
        = frv ref `S.union` frv e0 `S.union` frv e1 `S.union` frv e2
        
    fxv (Var'    _        (_,exn,_)) 
        = fxv exn
    fxv (Con'    _        (_,exn,_))
        = fxv exn
    fxv (Abs'    _  e     (_,exn,_))
        = fxv exn `S.union` fxv e
    fxv (Fix'    _  e     (_,exn,_))
        = fxv exn `S.union` fxv e
    fxv (App'    e1 e2    (_,exn,_))  
        = fxv exn `S.union` fxv e1 `S.union` fxv e2
    fxv (Let'    _  e1 e2 (_,exn,_))
        = fxv exn `S.union` fxv e1 `S.union` fxv e2
    fxv (If'   _ e0 e1 e2 (_,exn,_))
        = fxv exn `S.union` fxv e0 `S.union` fxv e1 `S.union` fxv e2
    -- Operators
    fxv (Op'     op e1 e2 (_,exn,_))
        = fxv exn `S.union` fxv e1 `S.union` fxv e2
    -- Pairs
    fxv (Pair'   e1 e2    (_,exn,_))
        = fxv exn `S.union` fxv e1 `S.union` fxv e2
    fxv (Fst'    e        (_,exn,_))
        = fxv exn `S.union` fxv e
    fxv (Snd'    e        (_,exn,_))  
        = fxv exn `S.union` fxv e
    -- Lists
    fxv (Nil'             (_,exn,_))  
        = fxv exn
    fxv (Cons'   e1 e2    (_,exn,_))
        = fxv exn `S.union` fxv e1 `S.union` fxv e2
    fxv (Case' _ e0 e1 e2 (_,exn,_))
        = fxv exn `S.union` fxv e0 `S.union` fxv e1 `S.union` fxv e2

    fvv (Var'    _        (_,_,vrf)) 
        = fvv vrf
    fvv (Con'    _        (_,_,vrf))
        = fvv vrf
    fvv (Abs'    _  e     (_,_,vrf))
        = fvv vrf `S.union` fvv e
    fvv (Fix'    _  e     (_,_,vrf))
        = fvv vrf `S.union` fvv e
    fvv (App'    e1 e2    (_,_,vrf))  
        = fvv vrf `S.union` fvv e1 `S.union` fvv e2
    fvv (Let'    _  e1 e2 (_,_,vrf))
        = fvv vrf `S.union` fvv e1 `S.union` fvv e2
    fvv (If'   _ e0 e1 e2 (_,_,vrf))
        = fvv vrf `S.union` fvv e0 `S.union` fvv e1 `S.union` fvv e2
    -- Operators
    fvv (Op'     op e1 e2 (_,_,vrf))
        = fvv vrf `S.union` fvv e1 `S.union` fvv e2
    -- Pairs
    fvv (Pair'   e1 e2    (_,_,vrf))
        = fvv vrf `S.union` fvv e1 `S.union` fvv e2
    fvv (Fst'    e        (_,_,vrf))
        = fvv vrf `S.union` fvv e
    fvv (Snd'    e        (_,_,vrf))  
        = fvv vrf `S.union` fvv e
    -- Lists
    fvv (Nil'             (_,_,vrf))  
        = fvv vrf
    fvv (Cons'   e1 e2    (_,_,vrf))
        = fvv vrf `S.union` fvv e1 `S.union` fvv e2
    fvv (Case' _ e0 e1 e2 (_,_,vrf))
        = fvv vrf `S.union` fvv e0 `S.union` fvv e1 `S.union` fvv e2

instance FreeVars Ty' where
    ftv (TyVar' a)
        = S.singleton a
    ftv (TyCon' _)
        = S.empty
    ftv (TyFun' t1 t2)
        = ftv t1 `S.union` ftv t2
    -- Pairs
    ftv (TyPair' t1 t2)
        = ftv t1 `S.union` ftv t2
    -- Lists
    ftv (TyList' t)
        = ftv t

instance FreeVars Ty where
    ftv (TyVar a)
        = S.singleton a
    ftv (TyCon _)
        = S.empty
    ftv (TyFun t1 e1 t2 e2)
        = ftv t1 `S.union` ftv t2
    -- Pairs
    ftv (TyPair t1 e1 t2 e2)
        = ftv t1 `S.union` ftv t2
    -- Lists
    ftv (TyList t e)
        = ftv t `S.union` ftv e -- FIXME: ftv e?
    
    frv (TyVar _)
        = S.empty
    frv (TyCon _)
        = S.empty
    frv (TyFun t1 e1 t2 e2)
        = frv t1 `S.union` frv e1 `S.union` frv t2 `S.union` frv e2
    -- Pairs
    frv (TyPair t1 e1 t2 e2)
        = frv t1 `S.union` frv e1 `S.union` frv t2 `S.union` frv e2
    -- Lists
    frv (TyList t e)
        = frv t `S.union` frv e
        
    fxv (TyVar _)
        = S.empty
    fxv (TyCon _)
        = S.empty
    fxv (TyFun t1 e1 t2 e2)
        = fxv t1 `S.union` fxv e1 `S.union` fxv t2 `S.union` fxv e2
    -- Pairs
    fxv (TyPair t1 e1 t2 e2)
        = fxv t1 `S.union` fxv e1 `S.union` fxv t2 `S.union` fxv e2
    -- Lists
    fxv (TyList t e)
        = fxv t `S.union` fxv e

    fvv (TyVar _)
        = S.empty
    fvv (TyCon _)
        = S.empty
    fvv (TyFun t1 e1 t2 e2)
        = fvv t1 `S.union` fvv e1 `S.union` fvv t2 `S.union` fvv e2
    -- Pairs
    fvv (TyPair t1 e1 t2 e2)
        = fvv t1 `S.union` fvv e1 `S.union` fvv t2 `S.union` fvv e2
    -- Lists
    fvv (TyList t e)
        = fvv t `S.union` fvv e
        
instance FreeVars TyScheme where
    ftv (Forall tq _  _  _  _  _  _  t _   _   _  )
        = ftv t `S.difference` S.fromList tq
    frv (Forall _  rq _  _  rc _  _  _ ref _   vrf)
        = (frv rc `S.union` frv ref `S.union` frv vrf) `S.difference` S.fromList rq
    fxv (Forall _  _  eq _  _  ec _  _ _   exn vrf)
        = (fxv ec `S.union` fxv exn `S.union` fxv vrf) `S.difference` S.fromList eq
    fvv (Forall _  _  _  vq _  _  vc _ _   _   vrf)
        = (fvv vc `S.union` fvv vrf) `S.difference` S.fromList vq

instance FreeVars TyEnv where
    ftv env = M.unionMap ftv env
    frv env = M.unionMap frv env
    fxv env = M.unionMap fxv env
    fvv env = M.unionMap fvv env

instance FreeVars Ref where
    ftv (Unif e ) = S.empty
    ftv (Conc es) = S.unionMap ftv es
    
    frv (Unif e ) = S.singleton e
    frv (Conc es) = S.unionMap frv es
    
    fxv (Unif e ) = S.empty
    fxv (Conc es) = S.unionMap fxv es

    fvv (Unif e ) = S.empty
    fvv (Conc es) = S.unionMap fvv es

instance FreeVars Ref' where
    ftv _           = S.empty

    frv (RefVar  z) = S.singleton z
    frv (RefTop   ) = S.empty
    frv (RefBool _) = S.empty
    frv (RefInt  _) = S.empty
    frv (RefList _) = S.empty
    
    fxv _           = S.empty
    
    fvv _           = S.empty

instance FreeVars Exn where
    ftv (Unif e ) = S.empty
    ftv (Conc es) = S.unionMap ftv es

    frv (Unif e ) = S.empty
    frv (Conc es) = S.unionMap frv es
    
    fxv (Unif e ) = S.singleton e
    fxv (Conc es) = S.unionMap fxv es

    fvv (Unif e ) = S.empty
    fvv (Conc es) = S.unionMap fvv es

instance FreeVars Exn' where
    ftv _            = S.empty

    frv _            = S.empty

    fxv (ExnVar   z) = S.singleton z
    fxv (ExnCrash _) = S.empty

    fvv _            = S.empty

instance FreeVars Vrf where
    ftv _         = S.empty

    frv (Unif e ) = S.empty
    frv (Conc es) = S.unionMap frv es
    
    fxv (Unif e ) = S.empty
    fxv (Conc es) = S.unionMap fxv es
    
    fvv (Unif e ) = S.singleton e
    fvv (Conc es) = S.unionMap fvv es

instance FreeVars Vrf' where
    ftv _          
        = S.empty

    frv (VrfVar z)
        = S.empty
    frv (VrfCon _ ref xpm exn)
        = M.foldrWithKey (\k a r -> r `S.union` frv k `S.union` frv a) S.empty xpm
            `S.union` frv ref `S.union` frv exn

    fxv (VrfVar z)
        = S.empty
    fxv (VrfCon _ ref xpm exn)
        = M.foldrWithKey (\k a r -> r `S.union` fxv k `S.union` fxv a) S.empty xpm
            `S.union` fxv ref `S.union` fxv exn

    fvv (VrfVar z)
        = S.singleton z
    fvv (VrfCon _ ref xpm exn)
        = M.foldrWithKey (\k a r -> r `S.union` fvv k `S.union` fvv a) S.empty xpm
            `S.union` fvv ref `S.union` fvv exn

instance FreeVars Ann where
    ftv (ref, exn, vrf) = ftv ref `S.union` ftv exn `S.union` ftv vrf
    frv (ref, exn, vrf) = frv ref `S.union` frv exn `S.union` frv vrf
    fxv (ref, exn, vrf) = fxv ref `S.union` fxv exn `S.union` fxv vrf
    fvv (ref, exn, vrf) = fvv ref `S.union` fvv exn `S.union` fvv vrf

instance FreeVars (Constr' Ref') where
    ftv = error "supress warnings"
    frv (ref1 :<: ref2) = frv ref1 `S.union` frv ref2
    fxv (ref1 :<: ref2) = fxv ref1 `S.union` fxv ref2
    fvv (ref1 :<: ref2) = fvv ref1 `S.union` fvv ref2

instance FreeVars RefConstr where
    ftv = error "supress warnings"
    frv c = S.unionMap frv c
    fxv c = S.unionMap fxv c
    fvv c = S.unionMap fvv c

instance FreeVars ExnConstr' where
    ftv = error "supress warnings"
    frv (exn1 :<: exn2) = frv exn1 `S.union` frv exn2
    fxv (exn1 :<: exn2) = fxv exn1 `S.union` fxv exn2
    fvv (exn1 :<: exn2) = fvv exn1 `S.union` fvv exn2

instance FreeVars ExnConstr where
    ftv = error "supress warnings"
    frv c = S.unionMap frv c
    fxv c = S.unionMap fxv c
    fvv c = S.unionMap fvv c
    
instance FreeVars VrfConstr' where
    ftv = error "supress warnings"
    frv (vrf1 :<: vrf2) = frv vrf1 `S.union` frv vrf2
    fxv (vrf1 :<: vrf2) = fxv vrf1 `S.union` fxv vrf2
    fvv (vrf1 :<: vrf2) = fvv vrf1 `S.union` fvv vrf2

instance FreeVars VrfConstr where
    ftv = error "supress warnings"
    frv c = S.unionMap frv c
    fxv c = S.unionMap fxv c
    fvv c = S.unionMap fvv c

-- Lists
instance FreeVars (Maybe (Expr' Ann)) where
    ftv = error "supress warnings"

    frv Nothing   = S.empty
    frv (Just e') = frv e'
    
    fxv Nothing   = S.empty
    fxv (Just e') = fxv e'
    
    fvv Nothing   = S.empty
    fvv (Just e') = fvv e'

instance FreeVars (Maybe (Name, Name, Expr' Ann))  where
    ftv = error "supress warnings"

    frv Nothing           = S.empty
    frv (Just (_, _, e')) = frv e'

    fxv Nothing           = S.empty
    fxv (Just (_, _, e')) = fxv e'

    fvv Nothing           = S.empty
    fvv (Just (_, _, e')) = fvv e'

-- | Substitutions

infixr 0 $@
infixr 9 $.

type TySubst = M.Map Name Ty'
data Subst = Subst (M.Map Name Ty) (M.Map Name Name) deriving Show

idSubst' :: TySubst
idSubst' = M.empty

idSubst :: Subst
idSubst = Subst M.empty M.empty

($+) :: TySubst -> TySubst -> TySubst
s2 $+ s1 = (s2 $$ s1) +$+ s2
    where ($$), (+$+) :: TySubst -> TySubst -> TySubst
          subst $$ tv
            = M.map (subst $!) tv
          tv1 +$+ tv2
            = M.unionWith overlapError tv1 tv2
                where overlapError a b = error $ "DF.+$+: overlapping substitutions: a = " ++ show a ++ ", b = " ++ show b ++ ", tv1 = " ++ show tv1 ++ ", tv2 = " ++ show tv2

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $$ s1) $+ s2
    where ($$), ($+) :: Subst -> Subst -> Subst
          subst $$ Subst tv ev
            = Subst (M.map (subst $@) tv) (M.map (subst $@) ev)
          Subst tv1 ev1 $+ Subst tv2 ev2
            = Subst (M.unionWith overlapError tv1 tv2)
                    (M.unionWith overlapError ev1 ev2)
                where overlapError a b = error $ "DF.$+: overlapping substitutions: a = " ++ show a ++ ", b = " ++ show b ++ ", tv1 = " ++ show tv1 ++ ", tv2 = " ++ show tv2 ++ ", ev1 = " ++ show ev1 ++ ", ev2 = " ++ show ev2
                
type AnnSubst = (RefSubst, ExnSubst, VrfSubst)

class Substitute t where
    ($!) :: TySubst  -> t -> t
    ($@) :: Subst    -> t -> t
    ($#) :: AnnSubst -> t -> t
    
instance Substitute (Expr' Ty') where
    subst $! (Var' x ref)
        = Var' x (subst $! ref)
    subst $! (Con' c ref)
        = Con' c (subst $! ref)
    subst $! (Abs' x e ref)
        = Abs' x (subst $! e) (subst $! ref)
    subst $! (Fix' f e ref)
        = Fix' f (subst $! e) (subst $! ref)
    subst $! (App' e1 e2 ref)
        = App' (subst $! e1) (subst $! e2) (subst $! ref)
    subst $! (Let' x e1 e2 ref)
        = Let' x (subst $! e1) (subst $! e2) (subst $! ref)
    subst $! (If' lbl e0 e1 e2 ref)
        = If' lbl (subst $! e0) (subst $! e1) (subst $! e2) (subst $! ref)
    -- Operators
    subst $! (Op' op e1 e2 ref)
        = Op' op (subst $! e1) (subst $! e2) (subst $! ref)
    -- Pairs
    subst $! (Pair' e1 e2 ref)
        = Pair' (subst $! e1) (subst $! e2) (subst $! ref)
    subst $! (Fst' e ref)
        = Fst' (subst $! e) (subst $! ref)
    subst $! (Snd' e ref)
        = Snd' (subst $! e) (subst $! ref)
    -- Lists
    subst $! (Nil' ref)
       = Nil' (subst $! ref)
    subst $! (Cons' e1 e2 ref)
        = Cons' (subst $! e1) (subst $! e2) (subst $! ref)
    subst $! (Case' lbl e0 e1 e2 ref)
        = Case' lbl (subst $! e0) (subst $! e1) (subst $! e2) (subst $! ref)
    
instance Substitute (Expr' Ann) where -- FIXME: instance Functor Expr'
    subst $@ (Var' x ref)
        = Var' x (subst $@ ref)
    subst $@ (Con' c ref)
        = Con' c (subst $@ ref)
    subst $@ (Abs' x e ref)
        = Abs' x (subst $@ e) (subst $@ ref)
    subst $@ (Fix' f e ref)
        = Fix' f (subst $@ e) (subst $@ ref)
    subst $@ (App' e1 e2 ref)
        = App' (subst $@ e1) (subst $@ e2) (subst $@ ref)
    subst $@ (Let' x e1 e2 ref)
        = Let' x (subst $@ e1) (subst $@ e2) (subst $@ ref)
    subst $@ (If' lbl e0 e1 e2 ref)
        = If' lbl (subst $@ e0) (subst $@ e1) (subst $@ e2) (subst $@ ref)
    -- Operators
    subst $@ (Op' op e1 e2 ref)
        = Op' op (subst $@ e1) (subst $@ e2) (subst $@ ref)
    -- Pairs
    subst $@ (Pair' e1 e2 ref)
        = Pair' (subst $@ e1) (subst $@ e2) (subst $@ ref)
    subst $@ (Fst' e ref)
        = Fst' (subst $@ e) (subst $@ ref)
    subst $@ (Snd' e ref)
        = Snd' (subst $@ e) (subst $@ ref)
    -- Lists
    subst $@ (Nil' ref)
       = Nil' (subst $@ ref)
    subst $@ (Cons' e1 e2 ref)
        = Cons' (subst $@ e1) (subst $@ e2) (subst $@ ref)
    subst $@ (Case' lbl e0 e1 e2 ref)
        = Case' lbl (subst $@ e0) (subst $@ e1) (subst $@ e2) (subst $@ ref)
        
    subst $# (Var' x ref)
        = Var' x (subst $# ref)
    subst $# (Con' c ref)
        = Con' c (subst $# ref)
    subst $# (Abs' x e ref)
        = Abs' x (subst $# e) (subst $# ref)
    subst $# (Fix' f e ref)
        = Fix' f (subst $# e) (subst $# ref)
    subst $# (App' e1 e2 ref)
        = App' (subst $# e1) (subst $# e2) (subst $# ref)
    subst $# (Let' x e1 e2 ref)
        = Let' x (subst $# e1) (subst $# e2) (subst $# ref)
    subst $# (If' lbl e0 e1 e2 ref)
        = If' lbl (subst $# e0) (subst $# e1) (subst $# e2) (subst $# ref)
    -- Operators
    subst $# (Op' op e1 e2 ref)
        = Op' op (subst $# e1) (subst $# e2) (subst $# ref)
    -- Pairs
    subst $# (Pair' e1 e2 ref)
        = Pair' (subst $# e1) (subst $# e2) (subst $# ref)
    subst $# (Fst' e ref)
        = Fst' (subst $# e) (subst $# ref)
    subst $# (Snd' e ref)
        = Snd' (subst $# e) (subst $# ref)
    -- Lists
    subst $# (Nil' ref)
       = Nil' (subst $# ref)
    subst $# (Cons' e1 e2 ref)
        = Cons' (subst $# e1) (subst $# e2) (subst $# ref)
    subst $# (Case' lbl e0 e1 e2 ref)
        = Case' lbl (subst $# e0) (subst $# e1) (subst $# e2) (subst $# ref)
    
instance Substitute Name where
    -- NOTE: Only substitutes annotation variables.
    Subst _ ev $@ e | Just e' <- M.lookup e ev = e'
                    | otherwise                = e
    _ $# _ = error "supress warnings"

instance Substitute Ty where
    Subst tv _ $@ t@(TyVar a)
        | Just t' <- M.lookup a tv = t'
        | otherwise                = t
    _          $@ t@(TyCon _) 
        = t
    subst $@ (TyFun t1 e1 t2 e2)
        = TyFun (subst $@ t1) (subst $@ e1) (subst $@ t2) (subst $@ e2)
    -- Pairs
    subst $@ (TyPair t1 e1 t2 e2)
        = TyPair (subst $@ t1) (subst $@ e1) (subst $@ t2) (subst $@ e2)
    -- Lists
    subst $@ (TyList t ref)
        = TyList (subst $@ t) (subst $@ ref)
        
    subst $# t@(TyVar _)
        = t
    subst $# t@(TyCon _)
        = t
    subst $# TyFun t1 e1 t2 e2
        = TyFun (subst $# t1) (subst $# e1) (subst $# t2) (subst $# e2)
    -- Pairs
    subst $# TyPair t1 e1 t2 e2
        = TyPair (subst $# t1) (subst $# e1) (subst $# t2) (subst $# e2)
    -- Lists
    subst $# TyList t ref
        = TyList (subst $# t) (subst $# ref)
        
instance Substitute Ty' where
    subst $! t@(TyVar' a)
        | Just t' <- M.lookup a subst = t'
        | otherwise                   = t
    _     $! t@(TyCon' _) 
        = t
    subst $! (TyFun' t1 t2)
        = TyFun' (subst $! t1) (subst $! t2)
    -- Pairs
    subst $! (TyPair' t1 t2)
        = TyPair' (subst $! t1) (subst $! t2)
    -- Lists
    subst $! (TyList' t)
        = TyList' (subst $! t)

instance Substitute Ref where
    subst $@ Unif e  = Unif (subst $@  e )
    subst $@ Conc es = Conc (S.map (subst $@) es)
    
    (subst, _, _)   $# r@(Unif e) = M.findWithDefault r e subst
        -- FIXME: this should (but doesn't) always succeed, need to make sure the
        -- solver instantiates solutions with bottom...
    s@(subst, _, _) $#    Conc es = Conc (S.unionMap f es)
        where f def@(RefVar e) =
                let Conc r = M.findWithDefault (Conc $ S.singleton def) e subst in r
                -- FIXME: needed to changes this from M.!, in case we're
                -- substituting constraints where one ove the sides is unbound
              f r          = S.singleton (s $# r)

instance Substitute Ref' where
    subst $@    RefVar  e  = RefVar (subst $@ e)
    subst $@ r@(RefBool _) = r
    subst $@ r@(RefInt  _) = r
    -- Lists
    subst $@ r@(RefList _) = r
    
    subst $#    RefVar  e  = error "I should be handled by Ref"
    subst $# r@(RefBool _) = r
    subst $# r@(RefInt  _) = r
    -- Lists
    subst $# r@(RefList _) = r
    
instance Substitute Exn where
    subst $@ Unif e  = Unif (subst $@  e )
    subst $@ Conc es = Conc (S.map (subst $@) es)

    (_, subst, _) $# r@(Unif u) = M.findWithDefault r u subst
        -- FIXME: this should (but doesn't) always succeed, need to make sure the
        -- solver instantiates solutions with bottom...
    s@(_, subst, _) $# Conc es = Conc (S.unionMap f es)
        where f def@(ExnVar e) =
                let Conc e' = M.findWithDefault (Conc $ S.singleton def) e subst in e'
                -- FIXME: needed to changes this from M.!, in case we're
                -- substituting constraints where one ove the sides is unbound
              f e          = S.singleton (s $# e)

instance Substitute Exn' where
    subst $@ ExnVar   e   = ExnVar (subst $@ e)
    subst $@ ExnCrash lbl = ExnCrash lbl

    subst $# ExnVar   e   = error "I should be handled by Exn"
    subst $# ExnCrash lbl = ExnCrash lbl

instance Substitute Vrf where
    subst $@ Unif e  = Unif (subst $@  e )
    subst $@ Conc es = Conc (S.map (subst $@) es)

    (_, _, subst) $# r@(Unif u) = M.findWithDefault r u subst
        -- FIXME: this should (but doesn't) always succeed, need to make sure the
        -- solver instantiates solutions with bottom...
    s@(_, _, subst) $# Conc es = Conc (S.unionMap f es)
        where f def@(VrfVar e) =
                let Conc e' = M.findWithDefault (Conc $ S.singleton def) e subst in e'
                    -- FIXME: needed to changes this from M.!, in case we're
                    -- substituting constraints where one ove the sides is unbound
              f e          = S.singleton (s $# e)

instance Substitute Vrf' where
    subst $@  VrfVar e
        = VrfVar (subst $@ e)
    subst $@ (VrfCon lbl ref xpm exn)
        = VrfCon lbl
                 (subst $@ ref)
                 (M.mapKeysAndValuesWith (error "Substitute Vrf' ($@)")
                                         (subst $@)
                                         (subst $@)
                                         xpm                            )
                 (subst $@ exn)

    subst $#    VrfVar e        = error "I should be handled by Vrf"
    subst $# v@(VrfCon lbl ref xpm exn) -- should only be called when subsituting
                                        -- constraint sets
        = VrfCon lbl
                 (subst $# ref)
                 (M.mapKeysAndValuesWith (error "Substitute Vrf' ($#)")
                     (subst $#)
                     (subst $#)
                     xpm                                                )
                 (subst $# exn)
    
instance Substitute Ann where
    subst $@ (ref, exn, vrf) = (subst $@ ref, subst $@ exn, subst $@ vrf)
    subst $# (ref, exn, vrf) = (subst $# ref, subst $# exn, subst $# vrf)
    
instance Substitute RefConstr where
    subst $@ c = S.map (subst $@) c
    subst $# c = S.map (subst $#) c
        
instance Substitute (Constr' Ref') where
    subst $@ (ref1 :<: ref2) = (subst $@ ref1) :<: (subst $@ ref2)
    subst $# (ref1 :<: ref2) = (subst $# ref1) :<: (subst $# ref2)

instance Substitute ExnConstr where
    subst $@ c = S.map (subst $@) c
    subst $# c = S.map (subst $#) c
        
instance Substitute ExnConstr' where
    subst $@ (exn1 :<: exn2) = (subst $@ exn1) :<: (subst $@ exn2)
    subst $# (exn1 :<: exn2) = (subst $# exn1) :<: (subst $# exn2)

instance Substitute VrfConstr where
    subst $@ c = S.map (subst $@) c
    subst $# c = S.map (subst $#) c
        
instance Substitute VrfConstr' where
    subst $@ (vrf1 :<: vrf2) = (subst $@ vrf1) :<: (subst $@ vrf2)
    subst $# (vrf1 :<: vrf2) = (subst $# vrf1) :<: (subst $# vrf2)

instance Substitute TyScheme where
    Subst tv bv $@ Forall as rq eq vq rc ec vc t ref exn vrf
        = let s' = Subst (tv `M.restrict` as) (bv `M.restrict` (rq ++ eq ++ vq))
           in Forall as rq eq vq (s' $@ rc) (s' $@ ec) (s' $@ vc)
                     (s' $@ t) (s' $@ ref) (s' $@ exn) (s' $@ vrf)
    (rs,es,vs) $# Forall as rq eq vq rc ec vc t ref exn vrf
        = let s' = (rs `M.restrict` rq, es `M.restrict` eq, vs `M.restrict` vq)
           in Forall as rq eq vq (s' $# rc) (s' $# ec) (s' $# vc)
                     (s' $# t) (s' $# ref) (s' $# exn) (s' $# vrf)

instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env
    subst $# env = M.map (subst $#) env
    
instance Substitute TyEnv' where
    subst $! env = M.map (subst $!) env
    
instance Substitute (String, Rule) where
    subst $@ (lbl, W' rc ec vc env e t ref exn vrf)
        = ( lbl, W' (subst $@ rc) (subst $@ ec) (subst $@ vc)
                    (subst $@ env) e (subst $@ t)
                    (subst $@ ref) (subst $@ exn) (subst $@ vrf) )
    subst $# (lbl, W' rc ec vc env e t ref exn vrf)
        = ( lbl, W' (subst $# rc) (subst $# ec) (subst $# vc)
                    (subst $# env) e (subst $# t)
                    (subst $# ref) (subst $# exn) (subst $# vrf) )
    
instance Substitute a => Substitute (T.Tree a) where
    subst $@ t = fmap (subst $@) t
    subst $# t = fmap (subst $#) t

-- Lists
instance Substitute (Maybe (Expr' Ty')) where
    subst $! me' = fmap (subst $!) me'

instance Substitute (Maybe (Name, Name, Expr' Ty')) where
    subst $! me' = fmap (\(x, xs, e') -> (x, xs, subst $! e')) me'

instance Substitute (Maybe (Expr' Ann)) where
    subst $@ me' = fmap (subst $@) me'
    _ $# _ = error "supress warnings"

instance Substitute (Maybe (Name, Name, Expr' Ann)) where
    subst $@ me' = fmap (\(x, xs, e') -> (x, xs, subst $@ e')) me'
    _ $# _ = error "supress warnings"

-- | Fresh Variables

type InferM r = State [Name] r

class Fresh a where
    fresh :: InferM a
    
instance (Fresh a, Fresh b) => Fresh (a, b) where
    fresh = do x <- fresh
               y <- fresh
               return (x, y)
               
instance (Fresh a, Fresh b, Fresh c) => Fresh (a, b, c) where
    fresh = do x <- fresh
               y <- fresh
               z <- fresh
               return (x, y, z)

instance (Fresh a, Fresh b, Fresh c, Fresh d) => Fresh (a, b, c, d) where
    fresh = do x <- fresh
               y <- fresh
               z <- fresh
               u <- fresh
               return (x, y, z, u)

instance (Fresh a, Fresh b, Fresh c, Fresh d, Fresh e) => Fresh (a, b, c, d, e) where
    fresh = do x <- fresh
               y <- fresh
               z <- fresh
               u <- fresh
               v <- fresh
               return (x, y, z, u, v)
               
instance (Fresh a, Fresh b, Fresh c, Fresh d, Fresh e, Fresh f) => Fresh (a, b, c, d, e, f) where
    fresh = do x <- fresh
               y <- fresh
               z <- fresh
               u <- fresh
               v <- fresh
               w <- fresh
               return (x, y, z, u, v, w)

instance Fresh Name where
    fresh = do (x:xs) <- get
               put xs
               return x
               
instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar (augment "\\alpha" a))

instance Fresh Ty' where
    fresh = do a <- fresh
               return (TyVar' (augment "\\alpha" a))

instance Fresh Ref where
    fresh = do b <- fresh
               return (Unif (augment "\\beta" b))

instance Fresh Exn where
    fresh = do b <- fresh
               return (Unif (augment "\\chi" b))

instance Fresh Vrf where
    fresh = do b <- fresh
               return (Unif (augment "\\nu" b))

-- | Pretty Printing

instance LaTeX TyEnv where
    latex env | M.null env = "\\epsilon "
              | otherwise  = ("\\left[\\begin{split}"++) . (++"\\end{split}\\right]") . L.intercalate newline . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v) . M.toList $ env

instance LaTeX (T.Tree (String, Rule)) where
    latex (T.Node (lbl, rule) cs)
        = "\\frac{" ++ {- "\\displaystyle " ++ -} concatMap latex cs
            ++ "}\n{" ++ {- "\\displaystyle " ++ -}          latex rule ++ "}"
            ++ "\\mbox{\\ [" ++ lbl ++ "]}" ++ "\\quad"

instance LaTeX a => LaTeX (Expr' a) where
    latex (Con' c ann)
        = "\\left(" ++
          latex c
          ++ " : " ++ latex ann ++ "\\right)"
    latex (Var' x ann) 
        = "\\left(" ++
          latex x
          ++ " : " ++ latex ann ++ "\\right)"
    latex (Abs' x e ann)
        = "\\left(\\lambda " ++ latex x ++ "." ++ space ++ latex e ++ "\\right)"
          ++ " : " ++ latex ann
    latex (App' e1 e2 ann) 
        = "\\left(" ++ latex e1 ++ space ++ latex e2 ++ "\\right)"
          ++ " : " ++ latex ann
    latex (Let' x e1 e2 ann) 
        =  "\\left("
        ++ mathbf "let" ++ space ++ latex x  ++ space
        ++ mathbf "="   ++ space ++ latex e1 ++ space
        ++ mathbf "in"  ++ space ++ latex e2
        ++ "\\right)"
        ++ " : " ++ latex ann
    latex (Fix' f e ann) 
        = "\\left(" ++ mathbf "fix" ++ space ++ latex f
          ++ "." ++ space ++ latex e ++ "\\right)"
          ++ " : " ++ latex ann
    latex (If' lbl e0 e1 e2 ann)
        = "\\left("
        ++ mathbf "if"   ++ "_{" ++ lbl ++ "}" ++ space ++ latex e0 ++ space
        ++ mathbf "then"                       ++ space ++ latex e1 ++ space
        ++ mathbf "else"                       ++ space ++ latex e2
        ++ "\\right)"
        ++ " : " ++ latex ann
    -- Operators
    latex (Op' op e1 e2 ann)
        = "\\left(" ++ latex e1 ++ latex op ++ latex e2 ++ "\\right)"
          ++ " : " ++ latex ann
    -- Pair
    latex (Pair' e1 e2 ann)
        = "\\left(" ++ latex e1 ++ ", " ++ latex e2 ++ "\\right)"
          ++ " : " ++ latex ann
    latex (Fst' e ann)
        = "\\left(" ++ mathbf "fst" ++ space ++ latex e ++ "\\right)"
          ++ " : " ++ latex ann
    latex (Snd' e ann)
        = "\\left(" ++ mathbf "snd" ++ space ++ latex e ++ "\\right)"
          ++ " : " ++ latex ann
    -- Lists
    latex (Nil' ann)
        = mathbf "[]" ++ " : " ++ latex ann
    latex (Cons' e1 e2 ann)
        = "\\left(" ++ latex e1 ++ space ++ mathbf "::" ++ space ++ latex e2 ++ "\\right)"
          ++ " : " ++ latex ann
    latex (Case' lbl e arm1 arm2 ann)
        = "\\left("
          ++ mathbf "case" ++ "_{" ++ lbl ++ "}" ++ space ++ latex e ++ space
          ++ mathbf "of" ++ space ++ "\\left\\{"
          ++ maybe "" (\e1 -> mathbf "[]" ++ "\\to " ++ latex e1) arm1
          ++ (if isJust arm1 && isJust arm2 then "; " else "")
          ++ maybe "" (\(x, xs, e2) -> "\\left(" ++ latex x ++ "::"
                                                 ++ latex xs ++ "\\right)"
                                                 ++ "\\to " ++ latex e2) arm2
          ++ "\\right\\}" ++ "\\right)"
          ++ " : " ++ latex ann

instance LaTeX Ty' where
    latex (TyVar' a)
        = latex a
    latex (TyCon' TyInt)
        = mathbf "Int"
    latex (TyCon' TyBool)
        = mathbf "Bool"
    latex (TyFun' t1 t2)
        = "\\left("  ++ latex t1 ++ "\\to " ++ latex t2 ++ "\\right)"
    -- Pairs
    latex (TyPair' t1 t2)
        = "\\left(" ++ latex t1 ++ "\\times " ++ latex t2 ++ "\\right)"
    -- Lists
    latex (TyList' t)
        = "\\left[" ++ latex t ++ "\\right]"

instance LaTeX Ty where
    latex (TyVar a)
        = latex a
    latex (TyCon TyInt)
        = mathbf "Int"
    latex (TyCon TyBool)
        = mathbf "Bool"
    latex (TyFun t1 ref1 t2 ref2)
        = "\\left("  ++ latex t1 ++ "@" ++ latex ref1
          ++ "\\to " ++ latex t2 ++ "@" ++ latex ref2 ++ "\\right)"
    -- Pairs
    latex (TyPair t1 ref1 t2 ref2)
        = "\\left("    ++ latex t1 ++ "@" ++ latex ref1
          ++ "\\times " ++ latex t2 ++ "@" ++ latex ref2 ++ "\\right)"
    -- Lists
    latex (TyList t ref)
        = "\\left[" ++ latex t ++ "@" ++ latex ref ++ "\\right]"
    
instance LaTeX TyScheme where
    latex (Forall as rq eq vq rc ec vc t ref exn vrf)
        = "\\forall " ++ concatMap latex (as ++ rq ++ eq ++ vq)
          ++ " . " ++ latex rc ++ latex ec ++ latex vc
          ++ " \\Rightarrow " ++ latex t
          ++ "@" ++ latex ref ++ "; " ++ latex exn ++ "; " ++ latex vrf

instance LaTeX Ref' where
    latex (RefVar  b) = latex b
    latex (RefTop   ) = "\\top "
    latex (RefBool b) = mathbf (show b)
    latex (RefInt  n) = latex n
    -- Lists
    latex (RefList l) = mathbf (show l)

instance LaTeX Ref where
    latex (Unif u ) = latex u
    latex (Conc bs) = latexSet bs
    
instance LaTeX Int' where
    latex Neg  = mathbf "-"
    latex Zero = mathbf "0"
    latex Pos  = mathbf "+"

instance LaTeX Exn' where
    latex (ExnVar   b  ) = latex b
    latex (ExnCrash lbl) = "\\lightning_{" ++ latex lbl ++ "}"

instance LaTeX Exn where
    latex (Unif u ) = latex u
    latex (Conc bs) = latexSet bs

instance LaTeX Vrf' where
    latex (VrfVar b)
        = latex b
    latex (VrfCon lbl ref1 xpm exn)
        = latex ref1 ++ "\\bowtie_{" ++ lbl ++ "}"
                     ++ latex xpm ++ "\\succ " ++ latex exn
                     
instance LaTeX (M.Map Ref' Exn) where
    latex m | M.null m  = "\\epsilon "
            | otherwise = ("\\left[\\begin{split}"++)
                          . (++"\\end{split}\\right]")
                          . L.intercalate newline 
                          . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v)
                          . M.toList
                          $ m

instance LaTeX Vrf where
    latex (Unif v ) = latex v
    latex (Conc vs) = latexSet vs

instance LaTeX Ann where
    latex (ref, exn, vrf)   
        = "\\left(" ++ latex ref ++ ", " ++ latex exn ++ ", " ++ latex vrf ++ "\\right)"

instance LaTeX (Constr' Ref') where
    latex (ref1 :<: ref2) = latex ref1 ++ "\\sqsubseteq " ++ latex ref2

instance LaTeX RefConstr where
    latex c = latexSet c

instance LaTeX ExnConstr' where
    latex (exn1 :<: exn2) = latex exn1 ++ "\\sqsubseteq " ++ latex exn2

instance LaTeX ExnConstr where
    latex c = latexSet c

instance LaTeX VrfConstr' where
    latex (vrf1 :<: vrf2) = latex vrf1 ++ "\\sqsubseteq " ++ latex vrf2

instance LaTeX VrfConstr where
    latex c = latexSet c

instance LaTeX Subst where
    latex (Subst a b) = "\\left[\\begin{split}" ++ latex' a ++ "; " ++ latex' b ++ "\\end{split}\\right]"
        where latex' m | M.null m  = "\\epsilon"
                       | otherwise = L.intercalate newline . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v) . M.toList $ m
    
instance LaTeX Rule where
    latex (W' rc ec vc env e t ref exn vrf)
        =  "\\begin{split}" -- {- ++ align -} ++                latex c   -- ++ newline
                            -- {- ++ align -} ++ ", "        ++ latex env -- ++ newline
                            {- ++ align -} ++ " \\vdash " ++ latex e   -- ++ newline
                            {- ++ align -} ++ " : "       ++ latex t   -- ++ newline
                            {- ++ align -} ++ "\\ \\&\\ " ++ latex ref
                                           ++ ";" ++ latex exn ++ ";" ++ latex vrf
        ++ "\\end{split}"
        
instance LaTeX RefSubst where
    latex subst = "\\left[\\begin{split}" ++ latexMap subst ++ "\\end{split}\\right]"
    
instance LaTeX ExnSubst where
    latex subst = "\\left[\\begin{split}" ++ latexMap subst ++ "\\end{split}\\right]"
    
instance LaTeX VrfSubst where
    latex subst = "\\left[\\begin{split}" ++ latexMap subst ++ "\\end{split}\\right]"
