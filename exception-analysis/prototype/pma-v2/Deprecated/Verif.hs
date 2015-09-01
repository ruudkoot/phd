{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Deprecated.Verif where

import Control.Monad
import Control.Monad.State

import qualified Data.Graph     as G
import qualified Data.List      as L
import qualified Data.Map       as M
import qualified Data.Map.Util  as M
import           Data.Maybe
import qualified Data.Set       as S
import qualified Data.Set.Util  as S
import qualified Data.Tree      as T

import           Common
import qualified Deprecated.Exn as Exn
import qualified Deprecated.DF  as DF

-- | Abstract Syntax

data Expr'
    = Var'  Name                    Exn.Exn DF.Ref
    | Con'  Con                     Exn.Exn DF.Ref
    | Abs'  Name  Expr'             Exn.Exn DF.Ref
    | Fix'  Name  Name  Expr'       Exn.Exn DF.Ref
    | App'  Expr' Expr'             Exn.Exn DF.Ref
    | Let'  Name  Expr' Expr'       Exn.Exn DF.Ref
    | If'   Lbl   Expr' Expr' Expr' Exn.Exn DF.Ref
    -- Operators
    | Op'   Op    Expr' Expr'       Exn.Exn DF.Ref
    -- Pairs
    | Pair' Expr' Expr'             Exn.Exn DF.Ref
    | Fst'  Expr'                   Exn.Exn DF.Ref
    | Snd'  Expr'                   Exn.Exn DF.Ref
    -- Lists
    | Nil'                          Exn.Exn DF.Ref
    | Cons' Expr' Expr'             Exn.Exn DF.Ref
    | Case' Lbl   Expr' (Maybe Expr') (Maybe (Name, Name, Expr')) Exn.Exn DF.Ref
    deriving (Eq, Ord, Show)
    
getExn :: Expr' -> Exn.Exn
getExn (Var'    _     exn _) = exn
getExn (Con'    _     exn _) = exn
getExn (Abs'    _ _   exn _) = exn
getExn (Fix'    _ _ _ exn _) = exn
getExn (App'    _ _   exn _) = exn
getExn (Let'    _ _ _ exn _) = exn
getExn (If'   _ _ _ _ exn _) = exn
-- Operators
getExn (Op'     _ _ _ exn _) = exn
-- Pairs
getExn (Pair'   _ _   exn _) = exn
getExn (Fst'    _     exn _) = exn
getExn (Snd'    _     exn _) = exn
-- Lists
getExn (Nil'          exn _) = exn
getExn (Cons'   _ _   exn _) = exn
getExn (Case' _ _ _ _ exn _) = exn

getRef :: Expr' -> DF.Ref
getRef (Var'    _     _ ref) = ref
getRef (Con'    _     _ ref) = ref
getRef (Abs'    _ _   _ ref) = ref
getRef (Fix'    _ _ _ _ ref) = ref
getRef (App'    _ _   _ ref) = ref
getRef (Let'    _ _ _ _ ref) = ref
getRef (If'   _ _ _ _ _ ref) = ref
-- Operators
getRef (Op'     _ _ _ _ ref) = ref
-- Pairs
getRef (Pair'   _ _   _ ref) = ref
getRef (Fst'    _     _ ref) = ref
getRef (Snd'    _     _ ref) = ref
-- Lists
getRef (Nil'          _ ref) = ref
getRef (Cons'   _ _   _ ref) = ref
getRef (Case' _ _ _ _ _ ref) = ref
    
mergeExprs :: Exn.Expr' -> DF.Expr' -> Expr'
mergeExprs (Exn.Var'     x        exn) (DF.Var'      x'          ref) | x == x'
    = Var' x exn ref
mergeExprs (Exn.Con'     c        exn) (DF.Con'      c'          ref) | c == c'
    = Con' c exn ref
mergeExprs (Exn.Abs'     x e      exn) (DF.Abs'      x' e'       ref) | x == x'
    = Abs' x (mergeExprs e e') exn ref
mergeExprs (Exn.Fix'     f x e    exn) (DF.Fix'      f' x' e'    ref) | f == f, x == x'
    = Fix' f x (mergeExprs e e') exn ref
mergeExprs (Exn.App'     e1 e2    exn) (DF.App'      e1' e2'     ref)
    = App' (mergeExprs e1 e1') (mergeExprs e2 e2') exn ref
mergeExprs (Exn.Let'     x  e1 e2 exn) (DF.Let'      x'  e1' e2' ref) | x == x'
    = Let' x (mergeExprs e1 e1') (mergeExprs e2 e2') exn ref
mergeExprs (Exn.If'  lbl e0 e1 e2 exn) (DF.If'  lbl' e0' e1' e2' ref) | lbl == lbl'
    = If' lbl (mergeExprs e0 e0') (mergeExprs e1 e1') (mergeExprs e2 e2') exn ref
-- Operators
mergeExprs (Exn.Op' op e1 e2 exn) (DF.Op' op' e1' e2' ref) | op == op'
    = Op' op (mergeExprs e1 e1') (mergeExprs e2 e2') exn ref
-- Pairs
mergeExprs (Exn.Pair' e1 e2 exn) (DF.Pair' e1' e2' ref)
    = Pair' (mergeExprs e1 e1') (mergeExprs e2 e2') exn ref
mergeExprs (Exn.Fst' e exn) (DF.Fst' e' ref)
    = Fst' (mergeExprs e e') exn ref
mergeExprs (Exn.Snd' e exn) (DF.Snd' e' ref)
    = Snd' (mergeExprs e e') exn ref
-- Lists
mergeExprs (Exn.Nil'                 exn) (DF.Nil'                     ref)
    = Nil' exn ref
mergeExprs (Exn.Cons'   e1 e2        exn) (DF.Cons'    e1' e2'         ref)
    = Cons' (mergeExprs e1 e1') (mergeExprs e2 e2') exn ref
mergeExprs (Exn.Case' l e0 arm1 arm2 exn) (DF.Case' l' e0' arm1' arm2' ref) | l == l'
    = let marm1 = case (arm1, arm1') of
                    (Nothing, Nothing ) -> Nothing
                    (Just e1, Just e1') -> Just (mergeExprs e1 e1')
          marm2 = case (arm2, arm2') of
                    (Nothing         , Nothing            ) -> Nothing
                    (Just (x, xs, e2), Just (x', xs', e2')) -- | x == x', xs == xs'
                                -- FIXME: had to disable this check because we generate
                                --        fresh names in case the pattern is missing...
                        -> Just (x, xs, mergeExprs e2 e2')
       in Case' l (mergeExprs e0 e0') marm1 marm2 exn ref
-- Otherwise
mergeExprs exn df
    = error $ "Verif.mergeExprs: exn = " ++ show exn ++ ", df = " ++ show df

data Expr''  -- verification condition annotated expression
    = Var''  Name                 Vrf
    | Con''  Con                  Vrf
    | Abs''  Name   Expr''        Vrf
    | Fix''  Name   Name   Expr'' Vrf
    | App''  Expr'' Expr''        Vrf
    | Let''  Name   Expr'' Expr'' Vrf
    | If''   Expr'' Expr'' Expr'' Vrf
    -- Operators
    | Op''   Op     Expr'' Expr'' Vrf
    -- Pairs
    | Pair'' Expr'' Expr''        Vrf
    | Fst''  Expr''               Vrf
    | Snd''  Expr''               Vrf
    -- Lists
    | Nil''                       Vrf
    | Cons'' Expr'' Expr''        Vrf
    | Case'' Expr'' (Maybe Expr'') (Maybe (Name, Name, Expr'')) Vrf
    deriving (Eq, Ord, Show)

-- | Static Semantics

data Ty
    = TyVar Name
    | TyCon TyCon
    | TyFun Ty Vrf Ty Vrf
    -- Pairs
    | TyPair Ty Vrf Ty Vrf
    -- Lists
    | TyList Ty Vrf
    deriving (Eq, Ord, Show)

data TyCon
    = TyBool
    | TyInt
    deriving (Eq, Ord, Show)
    
data Vrf
    = VrfUnif Name
    | Vrf (S.Set Vrf')
    deriving (Eq, Ord, Show)

data Vrf'
    = VrfVar Name
    | VrfCon Lbl DF.Ref (M.Map DF.Ref' Exn.Exn) Exn.Exn
        -- FIXME: reconsider the type of the map in light of Main.solve2a
        --        (RefUnif -> ExnUnif?)
    deriving (Eq, Ord, Show)

type Constr = S.Set Constr'

data Constr'
    = Vrf :<: Vrf
    deriving (Eq, Ord, Show)

data TyScheme = Forall [Name] [Name] Constr Ty Vrf deriving (Eq, Ord, Show)

type TyEnv = M.Map Name TyScheme
    
-- | Inference Algorithm: Verification Constraints

-- * Miscellanous injection and projection helpers

injTS :: Ty -> Vrf -> TyScheme
injTS a vrf = Forall [] [] S.empty a vrf

injVrf :: Vrf -> Vrf
injVrf (VrfUnif e) = Vrf (S.singleton (VrfVar e))

prjVrf :: Vrf' -> Vrf
prjVrf (VrfVar r) = VrfUnif r

extrVrf :: Vrf' -> Name
extrVrf (VrfVar r) = r

-- * Derivation trees

data Rule
    = W' Constr TyEnv Expr' Ty Vrf
    deriving (Eq, Ord, Show)

type Deriv = T.Tree (String, Rule)

extrEnv :: Deriv -> TyEnv
extrEnv = M.unionsWith mergeEnv . map extrEnv' . T.flatten where
    extrEnv' (_, W' _ env _ _ _) = env
    mergeEnv ts1 ts2 = if ts1 == ts2 then ts1 else error "incompatible environments"
    
-- * Algorithm W_VC

inferVrf :: TyEnv -> Expr' -> InferM (Subst, Ty, Vrf, Constr, Deriv, Expr'')
inferVrf env e
    = do (s1, t1, vrf1, c1, d1, e1'') <- inferVrf' env e
         -- FIXME: Constraint simplification (and sanity checks) go here
         let (c2, s2) = contractCycles . removeReflexive . decompose $ (s1 $@ c1)
         let c3 = removeReflexive (s2 $@ c2)
         return (s2 $. s1, s2 $@ t1, s2 $@ vrf1, c3, d1, e1'')

inferVrf' :: TyEnv -> Expr' -> InferM (Subst, Ty, Vrf, Constr, Deriv, Expr'')
inferVrf' env e@(Var' x exn ref)
    | Just ts <- M.lookup x env
        = do (t, vrf, c) <- inst ts
             return ( idSubst, t, vrf, c
                    , T.Node ("Vrf-Var", W' c env e t vrf) []
                    , Var'' x vrf                             )
    | otherwise
        = error $ "identifier '" ++ show x ++ "' not in scope " ++ show env
inferVrf' env e@(Con' con exn ref)
    = do (t, c) <- typeOf con   -- FIXME: also return a vrf instead of generating fresh
         b' <- fresh
         return ( idSubst, t, b', c
                , T.Node ("Vrf-Con", W' c env e t b') []
                , Con'' con b'                           )
inferVrf' env e@(Abs' x e0 exn ref)
    = do (a1, vrf1) <- fresh
         let env0 = M.insert x (injTS a1 vrf1) env
         (s0, t0, vrf0, c0, d0, e0'') <- inferVrf env0 e0
         vrf' <- fresh
         let t' = TyFun (s0 $@ a1) (s0 $@ vrf1) t0 vrf0
         return ( s0, t', vrf', c0
                , T.Node ("Vrf-Abs", W' c0 env e t' vrf') [d0]
                , Abs'' x e0'' vrf'                            )
inferVrf' env e@(Fix' f x e0 exn ref) -- FIXME: from DF/EXN, not checked thoroughly
    = do (ax, bx, a0, b0, bf) <- fresh
         let env0 = M.insert f (injTS (TyFun ax bx a0 b0) bf)
                        (M.insert x (injTS ax bx) env)
         (s0, t0, vrf0, c0, d0, e0'') <- inferVrf env0 e0
         let s1 = unify t0 (s0 $@ a0)
         let s2 = unify' (s1 $@ vrf0) (s1 $@ s0 $@ b0)
         let t' = TyFun (s2 $@ s1 $@ s0 $@ ax) (s2 $@ s1 $@ s0 $@ bx  )
                        (s2 $@ s1 $@       t0) (s2 $@ s1 $@       vrf0)
         let b' = s2 $@ s1 $@ s0 $@ bf
         let c' = s2 $@ s1 $@ c0
         return ( s2 $. s1 $. s0, t', b', c'
                , T.Node ("Vrf-Fix", W' c' env e t' b') [d0]
                , Fix'' f x e0'' b'                          )
inferVrf' env e@(App' e1 e2 exn ref)
    = do (s1, t1, vrf1, c1, d1, e1'') <- inferVrf        env  e1
         (s2, t2, vrf2, c2, d2, e2'') <- inferVrf (s1 $@ env) e2
         (a, b) <- fresh
         let s3 = unify (s2 $@ t1) (TyFun t2 vrf2 a b)
         b' <- fresh
         let t' = s3 $@ a
         let c' = S.singleton (effect [s3 $@ b, s3 $@ s2 $@ vrf1] :<: b')
                  `S.union` (s3 $@ c2) `S.union` (s3 $@ s2 $@ c1)
         return ( s3 $. s2 $. s1, t', b', c'
                , T.Node ("Vrf-App", W' c' env e t' b') [d1, d2]
                , App'' e1'' e2'' b'                             )
inferVrf' env e@(Let' x e1 e2 exn ref)
    = do (s1, t1, vrf1, c1, d1, e1'') <- inferVrf                        env   e1
         let ts1 = gen (s1 $@ env) c1 t1 vrf1
         (s2, t2, vrf2, c2, d2, e2'') <- inferVrf (M.insert x ts1 (s1 $@ env)) e2
         let c' = c2 `S.union` (s2 $@ c1)
         return ( s2 $. s1, t2, vrf2, c'
                , T.Node ("Vrf-Let", W' c' env e t2 vrf2) [d1, d2]
                , Let'' x e1'' e2'' vrf2                           )
inferVrf' env e@(If' lbl e0 e1 e2 exn ref)
    = do (s0, t0, vrf0, c0, d0, e0'') <- inferVrf              env  e0
         (s1, t1, vrf1, c1, d1, e1'') <- inferVrf (      s0 $@ env) e1
         (s2, t2, vrf2, c2, d2, e2'') <- inferVrf (s1 $@ s0 $@ env) e2
         let s3 = unify (s2 $@ s1 $@ t0) (TyCon TyBool)
         let s4 = unify (s3 $@ s2 $@ t1) (s3 $@ t2)
         let t' = s4 $@ s3 $@ t2
         let vc = VrfCon lbl
                         (getRef e0)
                         (M.fromList [ (DF.RefBool True , getExn e1)
                                     , (DF.RefBool False, getExn e2) ])
                         exn
         b' <- fresh
         let c' = S.singleton (Vrf (S.singleton vc) :<: b')
                  `S.union` S.fromList [ s4 $@ s3 $@ s2 $@ s1 $@ vrf0 :<: b'
                                       , s4 $@ s3 $@ s2       $@ vrf1 :<: b'
                                       , s4 $@ s3             $@ vrf2 :<: b' ]
                  `S.union` (s4 $@ s3 $@ s2 $@ s1 $@ c0)
                  `S.union` (s4 $@ s3 $@ s2 $@ c1)
                  `S.union` (s4 $@ s3 $@ c2)
         return ( s4 $. s3 $. s2 $. s1 $. s0, t', b', c'
                , T.Node ("Vrf-If", W' c' env e t' b') [d0, d1, d2]
                , If'' e0'' e1'' e2'' b'                            )
-- Operators
inferVrf' env e@(Op' op@LEQ e1 e2 exn ref)
    = do (s1, t1, vrf1, c1, d1, e1'') <- inferVrf        env  e1
         (s2, t2, vrf2, c2, d2, e2'') <- inferVrf (s1 $@ env) e2
         let s3 = unify (s2 $@ t1) (TyCon TyInt)
         let s4 = unify (s3 $@ t2) (TyCon TyInt)
         let t' = TyCon TyBool
         b' <- fresh
         let c' = (s4 $@ s3 $@ s2 $@ c1) `S.union` (s4 $@ s3 $@ c2)
         return ( s4 $. s3 $. s2 $. s1, t', b', c'
                , T.Node ("Vrf-Op", W' c' env e t' b') [d1, d2]
                , Op'' op e1'' e2'' b'                          )
inferVrf' env e@(Op' op@ADD e1 e2 exn ref)
    = do (s1, t1, vrf1, c1, d1, e1'') <- inferVrf        env  e1
         (s2, t2, vrf2, c2, d2, e2'') <- inferVrf (s1 $@ env) e2
         let s3 = unify (s2 $@ t1) (TyCon TyInt)
         let s4 = unify (s3 $@ t2) (TyCon TyInt)
         let t' = TyCon TyInt
         b' <- fresh
         let c' = (s4 $@ s3 $@ s2 $@ c1) `S.union` (s4 $@ s3 $@ c2)
         return ( s4 $. s3 $. s2 $. s1, t', b', c'
                , T.Node ("Vrf-Op", W' c' env e t' b') [d1, d2]
                , Op'' op e1'' e2'' b'                          )
-- Pairs
inferVrf' env e@(Pair' e1 e2 exn ref)
    = do (s1, t1, vrf1, c1, d1, e1'') <- inferVrf        env  e1
         (s2, t2, vrf2, c2, d2, e2'') <- inferVrf (s1 $@ env) e2
         let t' = TyPair (s2 $@ t1) (s2 $@ vrf1) t2 vrf2
         b' <- fresh
         let c' = (s2 $@ c1) `S.union` c2
         return ( s2 $. s1, t', b', c'
                , T.Node ("Vrf-Pair", W' c' env e t' b') [d1, d2]
                , Pair'' e1'' e2'' b'                             )
inferVrf' env e@(Fst' e0 exn ref)
    = do (s0, t0, vrf0, c0, d0, e0'') <- inferVrf env e0
         (a1, b1, a2, b2) <- fresh
         let s1 = unify t0 (TyPair a1 b1 a2 b2)
         let t' = s1 $@ a1
         b' <- fresh
         let c' = s1 $@ c0 `S.union` S.fromList [vrf0 :<: b', b1 :<: b'] --FIXME: okay?
         return ( s1 $. s0, t', b', c'
                , T.Node ("Vrf-Fst", W' c' env e t' b') [d0]
                , Fst'' e0'' b'                              )
inferVrf' env e@(Snd' e0 exn ref)
    = do (s0, t0, vrf0, c0, d0, e0'') <- inferVrf env e0
         (a1, b1, a2, b2) <- fresh
         let s1 = unify t0 (TyPair a1 b1 a2 b2)
         let t' = s1 $@ a2
         b' <- fresh
         let c' = s1 $@ c0 `S.union` S.fromList [vrf0 :<: b', b2 :<: b'] --FIXME: okay?
         return ( s1 $. s0, t', b', c'
                , T.Node ("Vrf-Fst", W' c' env e t' b') [d0]
                , Snd'' e0'' b'                              )
-- Lists
inferVrf' env e@(Nil' exn ref)
    = do (a, b1, b2) <- fresh
         let t' = TyList a b1
         let c' = S.empty
         return ( idSubst, t', b2, c'
                , T.Node ("Vrf-Nil", W' c' env e t' b2) []
                , Nil'' b2                                 )
inferVrf' env e@(Cons' e1 e2 exn ref)
    = do (s1, t1, vrf1, c1, d1, e1'') <- inferVrf        env  e1
         (s2, t2, vrf2, c2, d2, e2'') <- inferVrf (s1 $@ env) e2
         q <- fresh
         let s3 = unify t2 (TyList (s2 $@ t1) q)
         b1q <- fresh
         let t = TyList (s3 $@ s2 $@ t1) b1q
         let b2 = vrf2         -- FIXME: or should b2 be fresh?
         let c = S.fromList [ s3 $@ s2 $@ vrf1 :<: b1q
                            , s3 $@ q          :<: b1q
                         -- , s3 $@ exn2       :<: b2
                            ]
                 `S.union` (s3 $@ s2 $@ c1) `S.union` (s3 $@ c2)
         return ( s3 $. s2 $. s1, t, b2, c
                , T.Node ("Vrf-Cons", W' c env e t b2) [d1, d2]
                , Cons'' e1'' e2'' b2                             )
inferVrf' env e@(Case' lbl e0 arm1@(Just e1) arm2@(Just (x', xs', e2)) exn ref)
    = do -- Scrutinee
         (s0, t0, vrf0, c0, d0, e0'') <- inferVrf env e0
         (a0, b0) <- fresh
         let s0' = unify t0 (TyList a0 b0)

         -- Nil arm (FIXME: old-style, as arms cannot be missing here anymore)
         (s1, t1, vrf1, c1, d1, e1'')
            <- maybe (error "pattern missing: nil")
                     (inferVrf (s0' $@ s0 $@ env))
                     arm1

         -- Cons arm (FIXME: old-style, as arms cannot be missing here anymore)
         (s2, t2, vrf2, c2, d2, e2'')
            <- maybe (error "pattern missing: cons")
                     (\(x, xs, e2) -> inferVrf
                        (M.insert x  (injTS (s1 $@ s0' $@ a0)
                                            (s1 $@ s0' $@ b0))
                        (M.insert xs (injTS (TyList (s1 $@ s0' $@ a0)
                                                    (s1 $@ s0' $@ b0))
                                            (s1 $@ s0' $@ vrf0))
                        (s1 $@ s0' $@ s0 $@ env))) e2)
                     arm2

         -- Return type
         let s3 = unify (s2 $@ t1) t2

         let t' = s3 $@ t2
         let vc = VrfCon lbl
                         (getRef e0)
                         (M.fromList [ (DF.RefList DF.E , getExn e1)
                                     , (DF.RefList DF.NE, getExn e2) ])
                         exn
         b' <- fresh
         let c' = S.singleton (Vrf (S.singleton vc) :<: b')
                  `S.union` S.fromList [ s3 $@ s2 $@ s1 $@ s0' $@ vrf0 :<: b'
                                       , s3 $@ s2              $@ vrf1 :<: b'
                                       , s3                    $@ vrf2 :<: b' ]
                  `S.union` (s3 $@ s2 $@ s1 $@ s0' $@ c0)
                  `S.union` (s3 $@ s2 $@ c1)
                  `S.union` (s3 $@ c2)
         return ( s3 $. s2 $. s1 $. s0' $. s0, t', b', c'
                , T.Node ("Vrf-Case", W' c' env e t' b') [d0, d1, d2]
                , Case'' e0'' (Just e1'') (Just (x', xs', e2'')) b'   )
-- Fallback
inferVrf' env e
    = error $ "Verif.inferVrf': e = " ++ show e
    
effect = Vrf . S.fromList . map (\(VrfUnif u) -> VrfVar u)

-- * Instantiation

inst :: TyScheme -> InferM (Ty, Vrf, Constr)
inst (Forall as bs c t vrf)
    = do as' <- replicateM (length as) fresh
         bs' <- replicateM (length bs) fresh'
         let r = Subst (M.fromList (zip as as')) (M.fromList (zip bs bs'))
         return (r $@ t, r $@ vrf, r $@ c)

fresh' :: InferM Name
fresh' = do b <- fresh
            return (augment "\\nu" b)

-- * Generalization

-- TODO: let-bound polymorphism and polyvariance
gen :: TyEnv -> Constr -> Ty -> Vrf -> TyScheme
gen env c t b = injTS t b

-- * Unification

unify :: Ty -> Ty -> Subst
unify (TyVar a1) t2@(TyVar a2)
    | a1 == a2  = Subst M.empty M.empty
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
unify (TyFun t1 b1 t2 b2) (TyFun t1' b1' t2' b2')
    = let s1 = unify'                    b1                     b1'
          s2 = unify' (            s1 $@ b2) (            s1 $@ b2')
          s3 = unify  (      s2 $@ s1 $@ t1) (      s2 $@ s1 $@ t1')
          s4 = unify  (s3 $@ s2 $@ s1 $@ t2) (s3 $@ s2 $@ s1 $@ t2')
       in s4 $. s3 $. s2 $. s1
-- Pairs
unify (TyPair t1 b1 t2 b2) (TyPair t1' b1' t2' b2')
    = let s1 = unify'                    b1                     b1'
          s2 = unify' (            s1 $@ b2) (            s1 $@ b2')
          s3 = unify  (      s2 $@ s1 $@ t1) (      s2 $@ s1 $@ t1')
          s4 = unify  (s3 $@ s2 $@ s1 $@ t2) (s3 $@ s2 $@ s1 $@ t2')
       in s4 $. s3 $. s2 $. s1
-- Lists
unify (TyList t b) (TyList t' b')
    = let s1 = unify'        b         b'
          s2 = unify  (s1 $@ t) (s1 $@ t')
       in s2 $. s1
unify _ _
    = error "constructor clash"

unify' :: Vrf -> Vrf -> Subst
unify' (VrfUnif u1) (VrfUnif u2)
    | u1 == u2  = Subst M.empty M.empty
    | otherwise = Subst M.empty (M.singleton u1 u2)
unify' vrf1 vrf2
    = error $ "not a simple type: vrf1 = " ++ show vrf1 ++ ", vrf2 = " ++ show vrf2

-- * Typing of constants

typeOf :: Con -> InferM (Ty, Constr)
typeOf (Bool x)
    = return (TyCon TyBool, S.empty)
typeOf (Int n)
    = return (TyCon TyInt , S.empty)
typeOf (ExnC _ _)
    = do a <- fresh
         return (a, S.empty)

-- | Constraint simplification

-- * Decomposition into singleton (atomic?) constraints

decompose :: Constr -> Constr
decompose c
    = S.foldr (\c' r -> r `S.union` decompose' c') S.empty c

decompose' :: Constr' -> Constr
decompose' (Vrf vrfs :<: b@(VrfUnif _))
    = S.unionMap (\vrf' -> S.singleton (Vrf (S.singleton vrf') :<: b)) vrfs
decompose' (VrfUnif b1 :<: b2@(VrfUnif _)) -- FIXME: we should't (but do) generate these
    = S.singleton (Vrf (S.singleton (VrfVar b1)) :<: b2)

-- * Remove reflexive constraints

removeReflexive :: Constr -> Constr
removeReflexive
    = S.foldr (\c'@(l :<: r) cr -> if l == injVrf r then cr else S.insert c' cr)
              S.empty
              
-- * Constract cyclic constraints (strongly connected components)

-- FIXME: extremely dubious code

contractCycles :: Constr -> (Constr, Subst)
contractCycles c
    = let sccs = G.stronglyConnCompR (toGraph c)
          (c', s') = foldr pc (S.empty, M.empty) sccs
       in (c', Subst M.empty s')

pc :: G.SCC ((), Vrf', [Vrf']) -> (Constr, M.Map Name Name) -> (Constr, M.Map Name Name)
pc (G.AcyclicSCC ((), r, vs)) (cr, sr)
    = ( foldr (\v -> S.insert (Vrf (S.singleton r) :<: prjVrf v)) cr vs
      , sr                                                                           )
pc (G.CyclicSCC scc@(((), r', _):scc')) (cr, sr)
    = ( foldr (\((), r, vs) cr' ->
            foldr (\v -> S.insert (Vrf (S.singleton r) :<: prjVrf v)) cr' vs
        ) cr scc
      , foldr (\((), r'', _) sr' -> M.insert (extrVrf r'') (extrVrf r') sr') sr scc' )

-- | Constraint solving (assumes constraints have been decomposed)

type VrfSubst = M.Map Name Vrf

solve :: Constr -> VrfSubst -> VrfSubst
solve c subst0
    = let sccs = G.stronglyConnCompR (toGraph c)
       in foldr processComponent subst0 sccs

processComponent :: G.SCC ((), Vrf', [Vrf']) -> VrfSubst -> VrfSubst
processComponent (G.AcyclicSCC ((), VrfVar b, vs)) subst
    = foldr (\(VrfVar v) -> M.insertWith vrfJoin v (subst M.!! b)) subst vs
processComponent (G.AcyclicSCC ((), vrfcon, vs)) subst
    = foldr (\(VrfVar v) -> M.insertWith vrfJoin v (Vrf (S.singleton vrfcon))) subst vs
processComponent scc@(G.CyclicSCC _) _
    = error $ "Vrf.processComponent: CyclicSCC: scc = " ++ show scc
                    
toGraph :: Constr -> [((), Vrf', [Vrf'])]
toGraph = map (\(k, v) -> ((), k, S.toList v)) . M.toList . toMap

toMap :: Constr -> M.Map Vrf' (S.Set Vrf')
toMap = S.foldr f M.empty
    where f (Vrf vrf1' :<: VrfUnif vrf2) | Just (vrf1, _) <- S.minView vrf1'
            = M.insertWith S.union vrf1 (S.singleton (VrfVar vrf2))
          f c' = error $ "Vrf.toMap.f: c' = " ++ show c'

vrfJoin :: Vrf -> Vrf -> Vrf
vrfJoin (Vrf vrfs1) (Vrf vrfs2) = Vrf (vrfs1 `S.union` vrfs2)

initSubst :: Ty -> Constr -> Expr'' -> VrfSubst
initSubst t c e' = S.foldr (\k -> M.insert k (Vrf S.empty)) M.empty (fev t `S.union` fev c `S.union` fev e')

-- | Free variables

class FreeVars a where
    ftv :: a -> S.Set Name
    fev :: a -> S.Set Name
    
instance FreeVars Expr'' where
    ftv = error "Verif.ftv_Expr''"
    
    fev (Var''  _        vrf) = fev vrf
    fev (Con''  _        vrf) = fev vrf
    fev (Abs''  _  e     vrf) = fev vrf `S.union` fev e
    fev (Fix''  _  _  e  vrf) = fev vrf `S.union` fev e
    fev (App''  e1 e2    vrf) = fev vrf `S.union` fev e1 `S.union` fev e2
    fev (Let''  _  e1 e2 vrf) = fev vrf `S.union` fev e1 `S.union` fev e2
    fev (If''   e0 e1 e2 vrf) = fev vrf `S.union` fev e0 `S.union` fev e1 `S.union` fev e2
    -- Operators
    fev (Op''   op e1 e2 vrf) = fev vrf `S.union` fev e1 `S.union` fev e2
    -- Pairs
    fev (Pair'' e1 e2    vrf) = fev vrf `S.union` fev e1 `S.union` fev e2
    fev (Fst''  e        vrf) = fev vrf `S.union` fev e
    fev (Snd''  e        vrf) = fev vrf `S.union` fev e
    -- Lists
    fev (Nil''           vrf) = fev vrf
    fev (Cons'' e1 e2    vrf) = fev vrf `S.union` fev e1 `S.union` fev e2
    fev (Case'' e0 e1 e2 vrf) = fev vrf `S.union` fev e0 `S.union` fev e1 `S.union` fev e2
    
instance FreeVars Ty where
    ftv (TyVar a)
        = S.singleton a
    ftv (TyCon _)
        = S.empty
    ftv (TyFun t1 _ t2 _)
        = ftv t1 `S.union` ftv t2
    -- Pairs
    ftv (TyPair t1 _ t2 _)
        = ftv t1 `S.union` ftv t2
    -- Lists
    ftv (TyList t _)
        = ftv t

    fev (TyVar a)
        = S.empty
    fev (TyCon _)
        = S.empty
    fev (TyFun t1 b1 t2 b2)
        = fev t1 `S.union` fev b1 `S.union` fev t2 `S.union` fev b2
    -- Pairs
    fev (TyPair t1 b1 t2 b2)
        = fev t1 `S.union` fev b1 `S.union` fev t2 `S.union` fev b2
    -- Lists
    fev (TyList t b)
        = fev t `S.union` fev b

instance FreeVars Vrf where
    ftv = error "supress waring"
    
    fev (VrfUnif e ) = S.singleton e
    fev (Vrf     es) = S.unionMap fev es

instance FreeVars Vrf' where
    ftv = error "supress waring"

    fev (VrfVar z)       = S.singleton z
    fev (VrfCon _ _ _ _) = S.empty

instance FreeVars Constr' where
    ftv = error "supress warnings"
    fev (vrf1 :<: vrf2) = fev vrf1 `S.union` fev vrf2

instance FreeVars Constr where
    ftv = error "supress warnings"
    fev c = S.unionMap fev c
    
-- Lists
instance FreeVars (Maybe Expr'') where
    ftv = error "supress warnings"
    
    fev Nothing   = S.empty
    fev (Just e'') = fev e''

instance FreeVars (Maybe (Name, Name, Expr''))  where
    ftv = error "supress warnings"

    fev Nothing           = S.empty
    fev (Just (_, _, e'')) = fev e''

-- | Substitutions

infixr 0 $@
infixr 9 $.

data Subst = Subst (M.Map Name Ty) (M.Map Name Name) deriving Show

idSubst :: Subst
idSubst = Subst M.empty M.empty

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $$ s1) $+ s2
    where ($$), ($+) :: Subst -> Subst -> Subst
          subst $$ Subst tv ev
            = Subst (M.map (subst $@) tv) (M.map (subst $@) ev)
          Subst tv1 ev1 $+ Subst tv2 ev2
            = Subst (M.unionWith overlapError tv1 tv2)
                    (M.unionWith overlapError ev1 ev2)
                where overlapError a b = error $ "Verif.$+: overlapping substitutions: a = " ++ show a ++ ", b = " ++ show b ++ ", tv1 = " ++ show tv1 ++ ", tv2 = " ++ show tv2 ++ ", ev1 = " ++ show ev1 ++ ", ev2 = " ++ show ev2

class Substitute t where
    ($@) :: Subst -> t -> t
    ($#) :: VrfSubst -> t -> t
    
instance Substitute Name where
    -- NOTE: Only substitutes annotation variables.
    Subst _ ev $@ e | Just e' <- M.lookup e ev = e'
                    | otherwise                = e
    _ $# _ = error "supress warnings"

instance Substitute Ty where
    Subst tv _ $@ t@(TyVar a)
        | Just t' <- M.lookup a tv = t'
        | otherwise                = t
    _     $@ t@(TyCon _) 
        = t
    subst $@ (TyFun t1 b1 t2 b2)
        = TyFun (subst $@ t1) (subst $@ b1) (subst $@ t2) (subst $@ b2)
    -- Pairs
    subst $@ (TyPair t1 b1 t2 b2)
        = TyPair (subst $@ t1) (subst $@ b1) (subst $@ t2) (subst $@ b2)
    -- Lists
    subst $@ (TyList t b)
        = TyList (subst $@ t) (subst $@ b)
        
    _ $# t@(TyVar _) 
        = t
    _ $# t@(TyCon _) 
        = t
    subst $# (TyFun t1 b1 t2 b2)
        = TyFun (subst $# t1) (subst $# b1) (subst $# t2) (subst $# b2)
    -- Pairs
    subst $# (TyPair t1 b1 t2 b2)
        = TyPair (subst $# t1) (subst $# b1) (subst $# t2) (subst $# b2)
    -- Lists
    subst $# (TyList t b)
        = TyList (subst $# t) (subst $# b)
        
instance Substitute Vrf where
    subst $@ VrfUnif e  = VrfUnif    (subst $@  e )
    subst $@ Vrf     es = Vrf (S.map (subst $@) es)

    subst $# r@(VrfUnif u) = M.findWithDefault r u subst -- FIXME: this should (but doesn't) always succeed, need to make sure the solver instantiates solutions with bottom...
    subst $# Vrf        es = Vrf (S.unionMap f es)
        where f (VrfVar e) = let Vrf e' = subst M.! e in e'
              f e          = S.singleton (subst $# e)
    
instance Substitute Vrf' where
    subst $@    VrfVar e        = VrfVar (subst $@ e)
    subst $@ v@(VrfCon _ _ _ _) = v

    subst $#    VrfVar e        = error "I should be handled by Vrf"
    subst $# v@(VrfCon _ _ _ _) = v

instance Substitute Constr where
    subst $@ c = S.map (subst $@) c
    subst $# c = S.map (subst $#) c
    
instance Substitute Constr' where
    subst $@ (vrf1 :<: vrf2) = (subst $@ vrf1) :<: (subst $@ vrf2)
    subst $# (vrf1 :<: vrf2) = (subst $# vrf1) :<: (subst $# vrf2)

instance Substitute TyScheme where
    Subst tv bv $@ Forall as bs c t b
        = let s' = Subst (tv `M.restrict` as) (bv `M.restrict` bs)
           in Forall as bs (s' $@ c) (s' $@ t) (s' $@ b)
    bv $# Forall as bs c t vrf
        = let s' = bv `M.restrict` bs
           in Forall as bs (s' $# c) (s' $# t) (s' $# vrf)

instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env
    subst $# env = M.map (subst $#) env
    
instance Substitute (String, Rule) where
    subst $@ (lbl, W' c env e t b)
        = (lbl, W' (subst $@ c) (subst $@ env) e (subst $@ t) (subst $@ b))
    subst $# (lbl, W' c env e t b)
        = (lbl, W' (subst $# c) (subst $# env) e (subst $# t) (subst $# b))
    
instance Substitute a => Substitute (T.Tree a) where
    subst $@ t = fmap (subst $@) t
    subst $# t = fmap (subst $#) t

instance Substitute Expr'' where
    subst $@ (Var'' x vrf)
        = Var'' x (subst $@ vrf)
    subst $@ (Con'' c vrf)
        = Con'' c (subst $@ vrf)
    subst $@ (Abs'' x e vrf)
        = Abs'' x (subst $@ e) (subst $@ vrf)
    subst $@ (Fix'' f x e vrf)
        = Fix'' f x (subst $@ e) (subst $@ vrf)
    subst $@ (App'' e1 e2 vrf)
        = App'' (subst $@ e1) (subst $@ e2) (subst $@ vrf)
    subst $@ (Let'' x e1 e2 vrf)
        = Let'' x (subst $@ e1) (subst $@ e2) (subst $@ vrf)
    subst $@ (If'' e0 e1 e2 vrf)
        = If'' (subst $@ e0) (subst $@ e1) (subst $@ e2) (subst $@ vrf)
    -- Operators
    subst $@ (Op'' op e1 e2 vrf)
        = Op'' op (subst $@ e1) (subst $@ e2) (subst $@ vrf)
    -- Pairs
    subst $@ (Pair'' e1 e2 vrf)
        = Pair'' (subst $@ e1) (subst $@ e2) (subst $@ vrf)
    subst $@ (Fst'' e vrf)
        = Fst'' (subst $@ e) (subst $@ vrf)
    subst $@ (Snd'' e vrf)
        = Snd'' (subst $@ e) (subst $@ vrf)
    -- Lists
    subst $@ (Nil'' vrf)
        = Nil'' (subst $@ vrf)
    subst $@ (Cons'' e1 e2 vrf)
        = Cons'' (subst $@ e1) (subst $@ e2) (subst $@ vrf)
    subst $@ (Case'' e0 e1 e2 vrf)
        = Case'' (subst $@ e0) (subst $@ e1) (subst $@ e2) (subst $@ vrf)
        
    subst $# (Var'' x vrf)
        = Var'' x (subst $# vrf)
    subst $# (Con'' c vrf)
        = Con'' c (subst $# vrf)
    subst $# (Abs'' x e vrf)
        = Abs'' x (subst $# e) (subst $# vrf)
    subst $# (Fix'' f x e vrf)
        = Fix'' f x (subst $# e) (subst $# vrf)
    subst $# (App'' e1 e2 vrf)
        = App'' (subst $# e1) (subst $# e2) (subst $# vrf)
    subst $# (Let'' x e1 e2 vrf)
        = Let'' x (subst $# e1) (subst $# e2) (subst $# vrf)
    subst $# (If'' e0 e1 e2 vrf)
        = If'' (subst $# e0) (subst $# e1) (subst $# e2) (subst $# vrf)
    -- Operators
    subst $# (Op'' op e1 e2 vrf)
        = Op'' op (subst $# e1) (subst $# e2) (subst $# vrf)
    -- Pairs
    subst $# (Pair'' e1 e2 vrf)
        = Pair'' (subst $# e1) (subst $# e2) (subst $# vrf)
    subst $# (Fst'' e vrf)
        = Fst'' (subst $# e) (subst $# vrf)
    subst $# (Snd'' e vrf)
        = Snd'' (subst $# e) (subst $# vrf)
    -- Lists
    subst $# (Nil'' vrf)
        = Nil'' (subst $# vrf)
    subst $# (Cons'' e1 e2 vrf)
        = Cons'' (subst $# e1) (subst $# e2) (subst $# vrf)
    subst $# (Case'' e0 e1 e2 vrf)
        = Case'' (subst $# e0) (subst $# e1) (subst $# e2) (subst $# vrf)

-- Lists    
instance Substitute (Maybe Expr'') where
    subst $@ me'' = fmap (subst $@) me''
    _ $# _ = error "supress warnings"

instance Substitute (Maybe (Name, Name, Expr'')) where
    subst $@ me'' = fmap (\(x, xs, e'') -> (x, xs, subst $@ e'')) me''
    _ $# _ = error "supress warnings"

-- * Substitutions for debugging purposes only

solSubst :: DF.RefSubst -> Exn.ExnSubst -> VrfSubst -> VrfSubst
solSubst refSubst exnSubst
    = M.map solSubst1 where
        solSubst1 (Vrf vrfs)
            = Vrf (S.map solSubst2 vrfs)
        solSubst2 (VrfCon lbl ref xpm exn)
            = VrfCon lbl
                     (refSubst DF.$# ref)
                     (M.map solSubst3 xpm) 
                     (exnSubst Exn.$# exn)
        solSubst3 exn
            = exnSubst Exn.$# exn
            
solSubst2 :: DF.RefSubst -> Exn.ExnSubst -> Exn.Subst -> VrfSubst -> VrfSubst
solSubst2 refSubst exnSubst exnSubst2   -- FIXME: awkward naming
    = M.map solSubst1 where
        solSubst1 (Vrf vrfs)
            = Vrf (S.map solSubst2 vrfs)
        solSubst2 (VrfCon lbl ref xpm exn)
            = VrfCon lbl
                     (refSubst DF.$# ref)
                     (M.map solSubst3 xpm) 
                     (exnSubst Exn.$# (exnSubst2 Exn.$@ exn))
        solSubst3 exn
            = exnSubst Exn.$# (exnSubst2 Exn.$@ exn)

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

instance Fresh Name where
    fresh = do (x:xs) <- get
               put xs
               return x

instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar (augment "\\alpha" a))
               
instance Fresh Vrf where
    fresh = do b <- fresh
               return (VrfUnif (augment "\\nu" b))

-- | Pretty Printing

instance LaTeX Expr' where
    latex (Con' c       exn ref)
        = latex c ++ "@" ++ latex ref ++ "\\& " ++ latex exn
    latex (Var' x       exn ref) 
        = latex x ++ "@" ++ latex ref ++ "\\& " ++ latex exn
    latex (Abs' x e     exn ref)
        = "\\left(\\lambda " ++ latex x ++ "." ++ space ++ latex e ++ "\\right)"  ++ "@" ++ latex ref  ++ "\\& " ++ latex exn
    latex (Fix' f x e exn ref) 
        = "\\left(" ++ mathbf "fix" ++ space ++ latex f ++ space ++ latex x
          ++ "." ++ space ++ latex e ++ "\\right)"
          ++ "@"    ++ latex ref
          ++ "\\& " ++ latex exn
    latex (App' e1 e2   exn ref) 
        = "\\left(" ++ latex e1 ++ space ++ latex e2 ++ "\\right)"  ++ "@" ++ latex ref ++ "\\& " ++ latex exn
    latex (Let' x e1 e2 exn ref) 
        =  mathbf "let" ++ space ++ latex x  ++ space
        ++ mathbf "="   ++ space ++ latex e1 ++ space
        ++ mathbf "in"  ++ space ++ latex e2
        ++ "@"                   ++ latex ref
        ++ "\\& "                ++ latex exn
    latex (If' lbl e0 e1 e2 exn ref)
        =  "\\left("
        ++ mathbf "if" ++ "_{" ++ lbl ++ "}" ++ space ++ latex e0 ++ space
        ++ mathbf "then" ++ space ++ latex e1 ++ space
        ++ mathbf "else" ++ space ++ latex e2
        ++ "\\right)"
        ++ "@"                    ++ latex ref
        ++ "\\& "                 ++ latex exn
    -- Operators
    latex (Op' op e1 e2 exn ref)
        = "\\left(" ++ latex e1 ++ latex op ++ latex e2 ++ "\\right)"
    -- Pairs
    latex (Pair' e1 e2 exn ref)
        = "\\left(" ++ latex e1 ++ ", " ++ latex e2 ++ "\\right)"
          ++ "@" ++ latex ref ++ "\\& " ++ latex exn
    latex (Fst' e exn ref)
        = "\\left(" ++ mathbf "fst" ++ space ++ latex e ++ "\\right)"
          ++ "@" ++ latex ref ++ "\\& " ++ latex exn
    latex (Snd' e exn ref)
        = "\\left(" ++ mathbf "snd" ++ space ++ latex e ++ "\\right)"
          ++ "@" ++ latex ref ++ "\\& " ++ latex exn
    -- Lists
    latex (Nil' exn ref)
        = mathbf "[]" ++ "@" ++ latex ref ++ "\\& " ++ latex exn
    latex (Cons' e1 e2 exn ref)
        = "\\left(" ++ latex e1 ++ space ++ "::" ++ space ++ latex e2 ++ "\\right)" ++ "@" ++ latex ref ++ "\\& " ++ latex exn
    latex (Case' lbl e arm1 arm2 exn ref)
        =    "\\left("
          ++ mathbf "case" ++ "_{" ++ lbl ++ "}" ++ space ++ latex e ++ space
          ++ mathbf "of" ++ space ++ "\\left\\{"
          ++ maybe "" (\e1 -> mathbf "[]" ++ "\\to " ++ latex e1) arm1
          ++ (if isJust arm1 && isJust arm2 then "; " else "")
          ++ maybe "" (\(x, xs, e2) -> "\\left(" ++ latex x ++ "::"
                                                ++ latex xs ++ "\\right)"
                                                ++ "\\to " ++ latex e2) arm2
          ++ "\\right\\}" ++ "\\right)"
          ++ "@"    ++ latex ref
          ++ "\\& " ++ latex exn

instance LaTeX TyEnv where
    latex env | M.null env = "\\epsilon "
              | otherwise  = ("\\left[\\begin{split}"++) . (++"\\end{split}\\right]") . L.intercalate newline . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v) . M.toList $ env

instance LaTeX (T.Tree (String, Rule)) where
    latex (T.Node (lbl, rule) cs)
        = "\\frac{\\displaystyle " ++ concatMap latex cs
            ++ "}{\\displaystyle " ++           latex rule ++ "}"
            ++ "\\mbox{\\ [" ++ lbl ++ "]}" ++ "\\quad "

instance LaTeX Ty where
    latex (TyVar a)
        = latex a
    latex (TyCon TyInt)
        = mathbf "Int"
    latex (TyCon TyBool)
        = mathbf "Bool"
    latex (TyFun t1 b1 t2 b2)
        = "\\left("  ++ latex t1 ++ space  ++ "\\&" ++ space ++ latex b1
          ++ "\\to " ++ latex t2 ++ space  ++ "\\&" ++ space ++ latex b2 ++ "\\right)"
    -- Pairs
    latex (TyPair t1 b1 t2 b2)
        = "\\left("     ++ latex t1 ++ space ++ "\\&" ++ space ++ latex b1
          ++ "\\times " ++ latex t2 ++ space ++ "\\&" ++ space ++ latex b2 ++ "\\right)"
    -- Lists
    latex (TyList t b)
        = "\\left[" ++ latex t ++ space ++ "\\&" ++ space ++ latex b ++ "\\right]"
    
instance LaTeX TyScheme where
    latex (Forall as bs cs t b) 
        = "\\forall " ++ concatMap latex (as ++ bs)
          ++ " . " ++ latex cs
          ++ " \\Rightarrow " ++ latex t
          ++ "\\ \\& \\ " ++ latex b

instance LaTeX Vrf' where
    latex (VrfVar b)
        = latex b
    latex (VrfCon lbl ref1 xpm exn)
        = latex ref1 ++ "\\bowtie_{" ++ lbl ++ "}"
                     ++ latex xpm ++ "\\succ " ++ latex exn

instance LaTeX Vrf where
    latex (VrfUnif v)  = latex v
    latex (Vrf     vs) = latexSet vs

instance LaTeX Constr' where
    latex (vrf1 :<: vrf2) = latex vrf1 ++ "\\sqsubseteq " ++ latex vrf2

instance LaTeX Constr where
    latex c = latexSet c
    
instance LaTeX (M.Map DF.Ref' Exn.Exn) where
    latex m | M.null m  = "\\epsilon "
            | otherwise = ("\\left[\\begin{split}"++)
                          . (++"\\end{split}\\right]")
                          . L.intercalate newline 
                          . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v)
                          . M.toList
                          $ m
    
instance LaTeX Subst where
    latex (Subst a b) = "\\left[\\begin{split}" ++ latex' a ++ "; " ++ latex' b ++ "\\end{split}\\right]"
        where latex' m | M.null m  = "\\epsilon"
                       | otherwise = L.intercalate newline . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v) . M.toList $ m
    
instance LaTeX Rule where
    latex (W' c env e t b)
        =  "\\begin{split}" {- ++ align -} -- ++                latex c   -- ++ newline
                            {- ++ align -} -- ++ ", "        ++ latex env -- ++ newline
                            {- ++ align -} ++ " \\vdash " ++ latex e   -- ++ newline
                            {- ++ align -} ++ " : "       ++ latex t   -- ++ newline
                            {- ++ align -} ++ "\\ \\&\\ " ++ latex b   -- ++ newline
        ++ "\\end{split}"
        
instance LaTeX VrfSubst where
    latex subst = "\\left[\\begin{split}" ++ latexMap subst ++ "\\end{split}\\right]"
