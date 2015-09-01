{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Deprecated.Exn where

import Control.Monad
import Control.Monad.State

import qualified Data.Graph      as G
import qualified Data.Graph.Util as G
import qualified Data.List       as L
import qualified Data.Map        as M
import qualified Data.Map.Util   as M
import qualified Data.Set        as S
import qualified Data.Set.Util   as S
import qualified Data.Tree       as T

import Common

-- | Abstract Syntax

data Expr'  -- exception annotated expression
    = Var'        Name              Exn
    | Con'        Con               Exn
    | Abs'        Name  Expr'       Exn
    | Fix'        Name  Name  Expr' Exn
    | App'        Expr' Expr'       Exn
    | Let'        Name  Expr' Expr' Exn
    | If'   Lbl   Expr' Expr' Expr' Exn
    -- Operators
    | Op'         Op    Expr' Expr' Exn
    -- Pairs
    | Pair'       Expr' Expr'       Exn
    | Fst'        Expr'             Exn
    | Snd'        Expr'             Exn
    -- Lists
    | Nil'                          Exn
    | Cons'       Expr' Expr'       Exn
    | Case' Lbl   Expr' (Maybe Expr') (Maybe (Name, Name, Expr')) Exn
    deriving (Eq, Ord, Show)
    
-- | Static Semantics

data Ty
    = TyVar Name
    | TyCon TyCon
    | TyFun Ty Exn Ty Exn
    -- Pairs
    | TyPair Ty Exn Ty Exn
    -- Lists
    | TyList Ty Exn
    deriving (Eq, Ord, Show)

data TyCon
    = TyBool
    | TyInt
    deriving (Eq, Ord, Show)

data Exn
    = ExnUnif Name
    | Exn (S.Set Exn')
    deriving (Eq, Ord, Show)

data Exn'
    = ExnVar Name
    | ExnCrash Lbl
    deriving (Eq, Ord, Show)
    
type Constr = S.Set Constr'

data Constr'
    = Exn :<: Exn
    deriving (Eq, Ord, Show)

data TyScheme = Forall [Name] [Name] Constr Ty Exn deriving (Eq, Ord, Show)

type TyEnv = M.Map Name TyScheme
    
-- | Inference Algorithm: Exceptions

-- * Miscellanous injection and projection helpers

injTS :: Ty -> Exn -> TyScheme
injTS a exn = Forall [] [] S.empty a exn

injExn :: Exn -> Exn
injExn (ExnUnif e) = Exn (S.singleton (ExnVar e))

prjExn :: Exn' -> Exn
prjExn (ExnVar r) = ExnUnif r

extrExn :: Exn' -> Name
extrExn (ExnVar r) = r

-- * Derivation tree

data Rule
    = W' Constr TyEnv Expr Ty Exn
    deriving (Eq, Ord, Show)

type Deriv = T.Tree (String, Rule)

extrEnv :: Deriv -> TyEnv
extrEnv = M.unionsWith mergeEnv . map extrEnv' . T.flatten where
    extrEnv' (_, W' _ env _ _ _) = env
    mergeEnv ts1 ts2 = if ts1 == ts2 then ts1 else error "incompatible environments"

-- * Algorithm W_Exn

inferExn :: TyEnv -> Expr -> InferM (Subst, Ty, Exn, Constr, Deriv, Expr')
inferExn env e
    = do (s1, t1, exn1, c1, d1, e1') <- inferExn' env e
         -- FIXME: Constraint simplification (and sanity checks) go here
         let (c2, s2) = contractCycles . removeReflexive . decompose $ (s1 $@ c1)
         let c3 = removeReflexive (s2 $@ c2)
         return (s2 $. s1, s2 $@ t1, s2 $@ exn1, c3, d1, e1')

inferExn' :: TyEnv -> Expr -> InferM (Subst, Ty, Exn, Constr, Deriv, Expr')
inferExn' env e@(Var x)
    | Just ts <- M.lookup x env
        = do (t, exn, c) <- inst ts
             return ( idSubst, t, exn, c
                    , T.Node ("Exn-Var", W' c env e t exn) []
                    , Var' x exn                              )
    | otherwise
        = error $ "identifier '" ++ show x ++ "' not in scope " ++ show env
inferExn' env e@(Con con)
    = do (t, exn, c) <- typeOf con
         return ( idSubst, t, exn, c
                , T.Node ("Exn-Con", W' c env e t exn) []
                , Con' con exn                            )
inferExn' env e@(Abs x e0)
    = do (a1, exn1) <- fresh
         let env0 = M.insert x (injTS a1 exn1) env
         (s0, t0, exn0, c0, d0, e0') <- inferExn env0 e0
         exn' <- fresh
         let t' = TyFun (s0 $@ a1) (s0 $@ exn1) t0 exn0
         return ( s0, t', exn', c0
                , T.Node ("Exn-Abs", W' c0 env e t' exn') [d0]
                , Abs' x e0' exn'                              )
inferExn' env e@(Fix f x e0)
    = do (ax, bx, a0, b0, bf) <- fresh
         let env0 = M.insert f (injTS (TyFun ax bx a0 b0) bf)
                        (M.insert x (injTS ax bx) env)
         (s0, t0, exn0, c0, d0, e0') <- inferExn env0 e0
         let s1 = unify t0 (s0 $@ a0)
         let s2 = unify' (s1 $@ exn0) (s1 $@ s0 $@ b0)
         let t' = TyFun (s2 $@ s1 $@ s0 $@ ax) (s2 $@ s1 $@ s0 $@ bx  )
                        (s2 $@ s1 $@       t0) (s2 $@ s1 $@       exn0)
         let b' = s2 $@ s1 $@ s0 $@ bf
         let c' = s2 $@ s1 $@ c0
         return ( s2 $. s1 $. s0, t', b', c'
                , T.Node ("Exn-Fix", W' c' env e t' b') [d0]
                , Fix' f x e0' b'                            )
inferExn' env e@(App e1 e2)
    = do (s1, t1, exn1, c1, d1, e1') <- inferExn        env  e1
         (s2, t2, exn2, c2, d2, e2') <- inferExn (s1 $@ env) e2
         (a, b) <- fresh
         let s3 = unify (s2 $@ t1) (TyFun t2 exn2 a b)
         b' <- fresh
         let t' = s3 $@ a
         let c' = (Exn (effect [s3 $@ b, s3 $@ s2 $@ exn1]) :<: b')
                    `S.insert` (s3 $@ s2 $@ c1) `S.union` (s3 $@ c2)
         return ( s3 $. s2 $. s1, t', b', c'
                , T.Node ("Exn-App", W' c' env e t' b') [d1, d2]
                , App' e1' e2' b'                                )
inferExn' env e@(Let x e1 e2)
    = do (s1, t1, exn1, c1, d1, e1') <- inferExn                        env   e1
         let ts1 = gen (s1 $@ env) exn1 c1 t1
         (s2, t2, exn2, c2, d2, e2') <- inferExn (M.insert x ts1 (s1 $@ env)) e2
         let c' = c2 `S.union` (s2 $@ c1)
         return ( s2 $. s1, t2, exn2, c'
                , T.Node ("Exn-Let", W' c' env e t2 exn2) [d1, d2]
                , Let' x e1' e2' exn2                              )
inferExn' env e@(If lbl e0 e1 e2)
    = do (s0, t0, exn0, c0, d0, e0') <- inferExn              env  e0
         (s1, t1, exn1, c1, d1, e1') <- inferExn (      s0 $@ env) e1
         (s2, t2, exn2, c2, d2, e2') <- inferExn (s1 $@ s0 $@ env) e2
         let s3 = unify (s2 $@ s1 $@ t0) (TyCon TyBool)
         let s4 = unify (s3 $@ s2 $@ t1) (s3 $@ t2)
         let t' = s4 $@ s3 $@ t2
         b' <- fresh
         let c' = (s4 $@ s3 $@ s2 $@ s1 $@ c0)
                  `S.union` (s4 $@ s3 $@ s2 $@ c1) `S.union` (s4 $@ s3 $@ c2)
                  `S.union` S.fromList [ s4 $@ s3 $@ s2 $@ s1 $@ exn0 :<: b' ]
         return ( s4 $. s3 $. s2 $. s1 $. s0, t', b', c'
                , T.Node ("Exn-If", W' c' env e t' b') [d0, d1, d2]
                , If' lbl e0' e1' e2' b'                            )
-- Operators
inferExn' env e@(Op op@LEQ e1 e2)
    = do (s1, t1, exn1, c1, d1, e1') <- inferExn        env  e1
         (s2, t2, exn2, c2, d2, e2') <- inferExn (s1 $@ env) e2
         let s3 = unify (s2 $@ t1) (TyCon TyInt)
         let s4 = unify (s3 $@ t2) (TyCon TyInt)
         let t' = TyCon TyBool
         b' <- fresh
         let c' = (s4 $@ s3 $@ s2 $@ c1) `S.union` (s4 $@ s3 $@ c2) `S.union`
                    S.fromList [ s4 $@ s3 $@ s2 $@ exn1 :<: b'
                               , s4 $@ s3 $@       exn2 :<: b' ]
         return ( s4 $. s3 $. s2 $. s1, t', b', c'
                , T.Node ("Exn-Op", W' c' env e t' b') [d1, d2]
                , Op' op e1' e2' b'                             )
inferExn' env e@(Op op@ADD e1 e2)
    = do (s1, t1, exn1, c1, d1, e1') <- inferExn        env  e1
         (s2, t2, exn2, c2, d2, e2') <- inferExn (s1 $@ env) e2
         let s3 = unify (s2 $@ t1) (TyCon TyInt)
         let s4 = unify (s3 $@ t2) (TyCon TyInt)
         let t' = TyCon TyInt
         b' <- fresh
         let c' = (s4 $@ s3 $@ s2 $@ c1) `S.union` (s4 $@ s3 $@ c2) `S.union`
                    S.fromList [ s4 $@ s3 $@ s2 $@ exn1 :<: b'
                               , s4 $@ s3 $@       exn2 :<: b' ]
         return ( s4 $. s3 $. s2 $. s1, t', b', c'
                , T.Node ("Exn-Op", W' c' env e t' b') [d1, d2]
                , Op' op e1' e2' b'                             )
-- Pairs
inferExn' env e@(Pair e1 e2)
    = do (s1, t1, exn1, c1, d1, e1') <- inferExn        env  e1
         (s2, t2, exn2, c2, d2, e2') <- inferExn (s1 $@ env) e2
         let t' = TyPair (s2 $@ t1) (s2 $@ exn1) t2 exn2
         b' <- fresh
         let c' = s2 $@ c1 `S.union` c2
         return ( s2 $. s1, t', b', c'
                , T.Node ("Exn-Pair", W' c' env e t' b') [d1, d2]
                , Pair' e1' e2' b'                               )
inferExn' env e@(Fst e0)
    = do (s0, t0, exn0, c0, d0, e0') <- inferExn env e0
         (a1, b1, a2, b2) <- fresh
         let s1 = unify t0 (TyPair a1 b1 a2 b2)
         let t' = s1 $@ a1
         b' <- fresh
         let c' = s1 $@ c0 `S.union` S.fromList [exn0 :<: b', b1 :<: b'] --FIXME: okay?
         return ( s1 $. s0, t', b', c'
                , T.Node ("Exn-Fst", W' c' env e t' b') [d0]
                , Fst' e0' b'                                )
inferExn' env e@(Snd e0)
    = do (s0, t0, exn0, c0, d0, e0') <- inferExn env e0
         (a1, b1, a2, b2) <- fresh
         let s1 = unify (TyPair a1 b1 a2 b2) t0
         let t' = s1 $@ a2
         b' <- fresh
         let c' = s1 $@ c0 `S.union` S.fromList [exn0 :<: b', b2 :<: b'] --FIXME: okay?
         return ( s1 $. s0, t', b', c'
                , T.Node ("Exn-Snd", W' c' env e t' b') [d0]
                , Snd' e0' b'                                )
-- Lists
inferExn' env e@Nil
    = do (a, b1, b2) <- fresh
         let t = TyList a b1
         let c = S.empty
         return ( idSubst, t, b2, c
                , T.Node ("Exn-Nil", W' c env e t b2) []
                , Nil' b2                                )
inferExn' env e@(Cons e1 e2)
    = do (s1, t1, exn1, c1, d1, e1') <- inferExn        env  e1
         (s2, t2, exn2, c2, d2, e2') <- inferExn (s1 $@ env) e2
         q <- fresh
         let s3 = unify t2 (TyList (s2 $@ t1) q)
         b1q <- fresh
         let t = TyList (s3 $@ s2 $@ t1) b1q
         let b2 = exn2         -- FIXME: or should b2 be fresh?
         let c = S.fromList [ s3 $@ s2 $@ exn1 :<: b1q
                            , s3 $@ q          :<: b1q
                         -- , s3 $@ exn2       :<: b2 -- FIXME: or should b2 be fresh?
                            ]
                 `S.union` (s3 $@ s2 $@ c1) `S.union` (s3 $@ c2)
         return ( s3 $. s2 $. s1, t, b2, c
                , T.Node ("Exn-Cons", W' c env e t b2) [d1, d2]
                , Cons' e1' e2' b2                              )
inferExn' env e@(Case lbl e0 arm1 arm2)
    = do -- Scrutinee
         (s0, t0, exn0, c0, d0, e0') <- inferExn env e0
         (a0, b0) <- fresh
         let s0' = unify t0 (TyList a0 b0)
         
         -- Nil arm
         (s1, t1, exn1, c1, d1, e1')
            <- case arm1 of
                Just e1 ->
                    inferExn (s0' $@ s0 $@ env) e1
                Nothing ->
                    do (a, b) <- fresh
                       let c' = S.singleton (Exn (S.singleton (ExnCrash lbl)) :<: b)
                       let e = ExnC lbl PatternMatchFail
                       return ( idSubst, a, b, c'
                              , T.Node ("Exn-Case-Nil"
                                       , W' S.empty env
                                            (Con e)
                                            a b                           )
                                       []
                              , Con' e b                                    )

         -- Cons arm
         (x', xs') <- maybe (do {(q,w) <- fresh; return (augment "Q" q, augment "W" w)}) (\(x, xs, _) -> return (x, xs)) arm2   -- FIXME: fresh not nicely named

         (s2, t2, exn2, c2, d2, e2')
            <- case arm2 of
                Just (x, xs, e2) ->
                    inferExn (M.insert x  (injTS (s1 $@ s0' $@ a0)
                                                 (s1 $@ s0' $@ b0))
                             (M.insert xs (injTS (TyList (s1 $@ s0' $@ a0)
                                                         (s1 $@ s0' $@ b0))
                                                 (s1 $@ s0' $@ exn0))
                             (s1 $@ s0' $@ s0 $@ env)))
                             e2
                Nothing ->
                    do (a, b) <- fresh
                       let c' = S.singleton (Exn (S.singleton (ExnCrash lbl)) :<: b)
                       let e = ExnC lbl PatternMatchFail
                       return ( idSubst, a, b, c'
                              , T.Node ( "Exn-Case-Cons"
                                       , W' S.empty env
                                            (Con e)
                                            a b                           )
                                       []
                              , Con' e b                                    )
                              
         -- Return type
         let s3 = unify (s2 $@ t1) t2
         
         let t' = s3 $@ t2
         b' <- fresh
         let c' = (s3 $@ s2 $@ s1 $@ s0' $@ c0)
                  `S.union` (s3 $@ s2 $@ c1) `S.union` (s3 $@ c2)
                  `S.union` S.fromList [ s3 $@ s2 $@ s1 $@ s0' $@ exn0 :<: b' ]
         return ( s3 $. s2 $. s1 $. s0' $. s0, t', b', c'
                , T.Node ("Exn-Case", W' c' env e t' b') [d0, d1, d2]
                , Case' lbl e0' (Just e1') (Just (x', xs', e2')) b'   )

effect = S.fromList . map (\(ExnUnif u) -> ExnVar u)

-- * Instantiation

inst :: TyScheme -> InferM (Ty, Exn, Constr)
inst (Forall as bs c t exn)
    = do as' <- replicateM (length as) fresh
         bs' <- replicateM (length bs) fresh'
         let r = Subst (M.fromList (zip as as')) (M.fromList (zip bs bs'))
         return (r $@ t, r $@ exn, r $@ c)
         
fresh' :: InferM Name
fresh' = do b <- fresh
            return (augment "\\chi" b)

-- * Generalization

-- TODO: let-bound polymorphism and polyvariance
gen :: TyEnv -> Exn -> Constr -> Ty -> TyScheme
gen env exn c t = injTS t exn

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
unify (TyFun t1 exn1 t2 exn2) (TyFun t1' exn1' t2' exn2')
    = let s1 = unify' (                  exn1) (                  exn1')
          s2 = unify' (            s1 $@ exn2) (            s1 $@ exn2')
          s3 = unify  (      s2 $@ s1 $@ t1  ) (      s2 $@ s1 $@ t1'  )
          s4 = unify  (s3 $@ s2 $@ s1 $@ t2  ) (s3 $@ s2 $@ s1 $@ t2'  )
       in s4 $. s3 $. s2 $. s1
-- Pairs
unify (TyPair t1 exn1 t2 exn2) (TyPair t1' exn1' t2' exn2')
    = let s1 = unify' (                  exn1) (                  exn1')
          s2 = unify' (            s1 $@ exn2) (            s1 $@ exn2')
          s3 = unify  (      s2 $@ s1 $@ t1  ) (      s2 $@ s1 $@ t1'  )
          s4 = unify  (s3 $@ s2 $@ s1 $@ t2  ) (s3 $@ s2 $@ s1 $@ t2'  )
       in s4 $. s3 $. s2 $. s1
-- Lists
unify (TyList t1 exn1) (TyList t2 exn2)
    = let s1 = unify'        exn1         exn2
          s2 = unify  (s1 $@ t1  ) (s1 $@ t2  )
       in s2 $. s1
unify _ _
    = error "constructor clash"

unify' :: Exn -> Exn -> Subst
unify' (ExnUnif u1) (ExnUnif u2)
    | u1 == u2  = Subst M.empty M.empty
    | otherwise = Subst M.empty (M.singleton u1 u2)
unify' exn1 exn2
    = error $ "not a simple type: exn1 = " ++ show exn1 ++ ", exn2 = " ++ show exn2

-- * Typing of constants

typeOf :: Con -> InferM (Ty, Exn, Constr)
typeOf (Bool x)
    = do b <- fresh
         return (TyCon TyBool, b, S.empty)
typeOf (Int n)
    = do b <- fresh
         return (TyCon TyInt , b, S.empty)
typeOf exnc@(ExnC lbl _)
    = do (a, b) <- fresh
         return (a, b, S.singleton (Exn (S.singleton (ExnCrash lbl)) :<: b))

-- | Constraint simplification

-- * Decomposition into singleton (atomic?) constraints

decompose :: Constr -> Constr
decompose c
    = S.foldr (\c' r -> r `S.union` decompose' c') S.empty c

decompose' :: Constr' -> Constr
decompose' (Exn exns :<: b@(ExnUnif _))
    = S.unionMap (\exn' -> S.singleton (Exn (S.singleton exn') :<: b)) exns
decompose' (ExnUnif b1 :<: b2@(ExnUnif _)) -- FIXME: we should't (but do) generate these
    = S.singleton (Exn (S.singleton (ExnVar b1)) :<: b2)

-- * Remove reflexive constraints

removeReflexive :: Constr -> Constr
removeReflexive
    = S.foldr (\c'@(l :<: r) cr -> if l == injExn r then cr else S.insert c' cr)
              S.empty
              
-- * Constract cyclic constraints (strongly connected components)

-- FIXME: extremely dubious code

contractCycles :: Constr -> (Constr, Subst)
contractCycles c
    = let sccs = G.stronglyConnCompR (toGraph c)
          (c', s') = foldr pc (S.empty, M.empty) sccs
       in (c', Subst M.empty s')

pc :: G.SCC ((), Exn', [Exn']) -> (Constr, M.Map Name Name) -> (Constr, M.Map Name Name)
pc (G.AcyclicSCC ((), r, vs)) (cr, sr)
    = ( foldr (\v -> S.insert (Exn (S.singleton r) :<: prjExn v)) cr vs
      , sr                                                                           )
pc (G.CyclicSCC scc@(((), r', _):scc')) (cr, sr)
    = ( foldr (\((), r, vs) cr' ->
            foldr (\v -> S.insert (Exn (S.singleton r) :<: prjExn v)) cr' vs
        ) cr scc
      , foldr (\((), r'', _) sr' -> M.insert (extrExn r'') (extrExn r') sr') sr scc' )

-- | Constraint solving (assumes constraints have been decomposed and decycled!)
                   -- FIXME: solver should take care of prepocessing the constraint set

type ExnSubst = M.Map Name Exn

solve :: Constr -> ExnSubst -> ExnSubst
solve c subst0
    = let sccs = G.stronglyConnCompR (toGraph c)
       in foldr processComponent subst0 sccs

processComponent :: G.SCC ((), Exn', [Exn']) -> ExnSubst -> ExnSubst
processComponent (G.AcyclicSCC ((), ExnVar b, vs)) subst
    = foldr (\(ExnVar v) -> M.insertWith exnJoin v (subst M.!! b)) subst vs
processComponent (G.AcyclicSCC ((), exncrash, vs)) subst
    = foldr (\(ExnVar v) -> M.insertWith exnJoin v (Exn (S.singleton exncrash))) subst vs
processComponent scc@(G.CyclicSCC _) _
    = error $ "Exn.processComponent: CyclicSCC (did you forget to decompose the constraint set?): scc = " ++ show scc
                    
toGraph :: Constr -> [((), Exn', [Exn'])]
toGraph = map (\(k, v) -> ((), k, S.toList v)) . M.toList . toMap

toMap :: Constr -> M.Map Exn' (S.Set Exn')
toMap = S.foldr f M.empty
    where f (Exn exn1' :<: ExnUnif exn2) | Just (exn1, _) <- S.minView exn1'
            = M.insertWith S.union exn1 (S.singleton (ExnVar exn2))
          f c' = error $ "Exn.toMap.f: c' = " ++ show c'

exnJoin :: Exn -> Exn -> Exn
exnJoin (Exn exns1) (Exn exns2) = Exn (exns1 `S.union` exns2)

initSubst :: Ty -> Constr -> Expr' -> ExnSubst
initSubst t c e' = S.foldr (\k -> M.insert k (Exn S.empty)) M.empty (fev t `S.union` fev c `S.union` fev e')

-- | Free variables

class FreeVars a where
    ftv :: a -> S.Set Name
    fev :: a -> S.Set Name
    
instance FreeVars Expr' where
    ftv = error "Exn.ftv_Expr'"
    
    fev (Var'    _        exn) 
        = fev exn
    fev (Con'    _        exn)
        = fev exn
    fev (Abs'    _  e     exn)
        = fev exn `S.union` fev e
    fev (Fix'    _  _  e  exn)
        = fev exn `S.union` fev e
    fev (App'    e1 e2    exn)
        = fev exn `S.union` fev e1 `S.union` fev e2
    fev (Let'    _  e1 e2 exn)
        = fev exn `S.union` fev e1 `S.union` fev e2
    fev (If'   _ e0 e1 e2 exn)
        = fev exn `S.union` fev e0 `S.union` fev e1 `S.union` fev e2
    -- Operators
    fev (Op'     op e1 e2 exn)
        = fev exn `S.union` fev e1 `S.union` fev e2
    -- Pairs
    fev (Pair'   e1 e2    exn)
        = fev exn `S.union` fev e1 `S.union` fev e2
    fev (Fst'    e        exn)  
        = fev exn `S.union` fev e
    fev (Snd'    e        exn)
        = fev exn `S.union` fev e
    -- Lists
    fev (Nil'             exn)
        = fev exn
    fev (Cons'   e1 e2    exn)
        = fev exn `S.union` fev e1 `S.union` fev e2
    fev (Case' _ e0 e1 e2 exn)
        = fev exn `S.union` fev e0 `S.union` fev e1 `S.union` fev e2

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
        = ftv t `S.union` ftv e
    
    fev (TyVar _)
        = S.empty
    fev (TyCon _)
        = S.empty
    fev (TyFun t1 e1 t2 e2)
        = fev t1 `S.union` fev e1 `S.union` fev t2 `S.union` fev e2
    -- Pairs
    fev (TyPair t1 e1 t2 e2)
        = fev t1 `S.union` fev e1 `S.union` fev t2 `S.union` fev e2
    -- Lists
    fev (TyList t e)
        = fev t `S.union` fev e

instance FreeVars Exn where
    ftv (ExnUnif e ) = S.empty
    ftv (Exn     es) = S.unionMap ftv es
    
    fev (ExnUnif e ) = S.singleton e
    fev (Exn     es) = S.unionMap fev es

instance FreeVars Exn' where
    ftv _          = S.empty

    fev (ExnVar z) = S.singleton z
    fev (ExnCrash _) = S.empty

instance FreeVars Constr' where
    ftv = error "supress warnings"
    fev (exn1 :<: exn2) = fev exn1 `S.union` fev exn2

instance FreeVars Constr where
    ftv = error "supress warnings"
    fev c = S.unionMap fev c

-- Lists
instance FreeVars (Maybe Expr') where
    ftv = error "supress warnings"
    
    fev Nothing   = S.empty
    fev (Just e') = fev e'

instance FreeVars (Maybe (Name, Name, Expr'))  where
    ftv = error "supress warnings"

    fev Nothing           = S.empty
    fev (Just (_, _, e')) = fev e'

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
                where overlapError a b = error $ "Exn.$+: overlapping substitutions: a = " ++ show a ++ ", b = " ++ show b ++ ", tv1 = " ++ show tv1 ++ ", tv2 = " ++ show tv2 ++ ", ev1 = " ++ show ev1 ++ ", ev2 = " ++ show ev2

class Substitute t where
    ($@) :: Subst -> t -> t
    ($#) :: ExnSubst -> t -> t
    
instance Substitute Expr' where
    subst $@ (Var' x exn)
        = Var' x (subst $@ exn)
    subst $@ (Con' c exn)
        = Con' c (subst $@ exn)
    subst $@ (Abs' x e exn)
        = Abs' x (subst $@ e) (subst $@ exn)
    subst $@ (Fix' f x e exn)
        = Fix' f x (subst $@ e) (subst $@ exn)
    subst $@ (App' e1 e2 exn)
        = App' (subst $@ e1) (subst $@ e2) (subst $@ exn)
    subst $@ (Let' x e1 e2 exn)
        = Let' x (subst $@ e1) (subst $@ e2) (subst $@ exn)
    subst $@ (If' lbl e0 e1 e2 exn)
        = If' lbl (subst $@ e0) (subst $@ e1) (subst $@ e2) (subst $@ exn)
    -- Operators
    subst $@ (Op' op e1 e2 exn)
        = Op' op (subst $@ e1) (subst $@ e2) (subst $@ exn)
    -- Pairs
    subst $@ (Pair' e1 e2 exn)
        = Pair' (subst $@ e1) (subst $@ e2) (subst $@ exn)
    subst $@ (Fst' e exn)
        = Fst' (subst $@ e) (subst $@ exn)
    subst $@ (Snd' e exn)
        = Snd' (subst $@ e) (subst $@ exn)
    -- Lists
    subst $@ (Nil' exn)
        = Nil' (subst $@ exn)
    subst $@ (Cons' e1 e2 exn)
        = Cons' (subst $@ e1) (subst $@ e2) (subst $@ exn)
    subst $@ (Case' lbl e0 e1 e2 exn)
        = Case' lbl (subst $@ e0) (subst $@ e1) (subst $@ e2) (subst $@ exn)
        
    subst $# (Var' x exn)
        = Var' x (subst $# exn)
    subst $# (Con' c exn)
        = Con' c (subst $# exn)
    subst $# (Abs' x e exn)
        = Abs' x (subst $# e) (subst $# exn)
    subst $# (Fix' f x e exn)
        = Fix' f x (subst $# e) (subst $# exn)
    subst $# (App' e1 e2 exn)
        = App' (subst $# e1) (subst $# e2) (subst $# exn)
    subst $# (Let' x e1 e2 exn)
        = Let' x (subst $# e1) (subst $# e2) (subst $# exn)
    subst $# (If' lbl e0 e1 e2 exn)
        = If' lbl (subst $# e0) (subst $# e1) (subst $# e2) (subst $# exn)
    -- Operators
    subst $# (Op' op e1 e2 exn)
        = Op' op (subst $# e1) (subst $# e2) (subst $# exn)
    -- Pairs
    subst $# (Pair' e1 e2 exn)
        = Pair' (subst $# e1) (subst $# e2) (subst $# exn)
    subst $# (Fst' e exn)
        = Fst' (subst $# e) (subst $# exn)
    subst $# (Snd' e exn)
        = Snd' (subst $# e) (subst $# exn)
    -- Lists
    subst $# (Nil' exn)
        = Nil' (subst $# exn)
    subst $# (Cons' e1 e2 exn)
        = Cons' (subst $# e1) (subst $# e2) (subst $# exn)
    subst $# (Case' lbl e0 e1 e2 exn)
        = Case' lbl (subst $# e0) (subst $# e1) (subst $# e2) (subst $# exn)


instance Substitute Name where
    -- NOTE: Only substitutes annotation variables.
    Subst _ ev $@ e | Just e' <- M.lookup e ev = e'
                    | otherwise                = e
    _ $# _ = error "supress warnings"

instance Substitute Ty where
    Subst tv _ $@ t@(TyVar a)
        | Just t' <- M.lookup a tv = t'
        | otherwise                = t
    _ $@ t@(TyCon _) 
        = t
    subst $@ (TyFun t1 e1 t2 e2)
        = TyFun (subst $@ t1) (subst $@ e1) (subst $@ t2) (subst $@ e2)
    -- Pairs
    subst $@ (TyPair t1 e1 t2 e2)
        = TyPair (subst $@ t1) (subst $@ e1) (subst $@ t2) (subst $@ e2)
    -- Lists
    subst $@ (TyList t exn)
        = TyList (subst $@ t) (subst $@ exn)
        
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
    subst $# TyList t exn
        = TyList (subst $# t) (subst $# exn)

instance Substitute Exn where
    subst $@ ExnUnif e  = ExnUnif    (subst $@  e )
    subst $@ Exn     es = Exn (S.map (subst $@) es)
    
    subst $# r@(ExnUnif u) = M.findWithDefault r u subst -- FIXME: this should (but doesn't) always succeed, need to make sure the solver instantiates solutions with bottom...
    subst $# Exn        es = Exn (S.unionMap f es)
        where f (ExnVar e) = let Exn e' = subst M.! e in e'
              f e          = S.singleton (subst $# e)

instance Substitute Exn' where
    subst $@ ExnVar   e   = ExnVar (subst $@ e)
    subst $@ ExnCrash lbl = ExnCrash lbl

    subst $# ExnVar   e   = error "I should be handled by Exn"
    subst $# ExnCrash lbl = ExnCrash lbl
    
instance Substitute Constr where
    subst $@ c = S.map (subst $@) c
    subst $# c = S.map (subst $#) c
    
instance Substitute Constr' where
    subst $@ (exn1 :<: exn2) = (subst $@ exn1) :<: (subst $@ exn2)
    subst $# (exn1 :<: exn2) = (subst $# exn1) :<: (subst $# exn2)

instance Substitute TyScheme where
    Subst tv bv $@ Forall as bs c t exn
        = let s' = Subst (tv `M.restrict` as) (bv `M.restrict` bs)
           in Forall as bs (s' $@ c) (s' $@ t) (s' $@ exn)
    bv $# Forall as bs c t exn
        = let s' = bv `M.restrict` bs
           in Forall as bs (s' $# c) (s' $# t) (s' $# exn)

instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env
    subst $# env = M.map (subst $#) env
    
instance Substitute (String, Rule) where
    subst $@ (lbl, W' c env e t exn)
        = (lbl, W' (subst $@ c) (subst $@ env) e (subst $@ t) (subst $@ exn))
    subst $# (lbl, W' c env e t exn)
        = (lbl, W' (subst $# c) (subst $# env) e (subst $# t) (subst $# exn))
    
instance Substitute a => Substitute (T.Tree a) where
    subst $@ t = fmap (subst $@) t
    subst $# t = fmap (subst $#) t
    
-- Lists    
instance Substitute (Maybe Expr') where
    subst $@ me' = fmap (subst $@) me'
    _ $# _ = error "supress warnings"

instance Substitute (Maybe (Name, Name, Expr')) where
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

instance Fresh Name where
    fresh = do (x:xs) <- get
               put xs
               return x
               
instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar (augment "\\alpha" a))

instance Fresh Exn where
    fresh = do b <- fresh
               return (ExnUnif (augment "\\chi" b))

-- | Pretty Printing
    
instance LaTeX TyEnv where
    latex env | M.null env = "\\epsilon "
              | otherwise  = ("\\left[\\begin{split}"++) . (++"\\end{split}\\right]") . L.intercalate newline . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v) . M.toList $ env

instance LaTeX (T.Tree (String, Rule)) where
    latex (T.Node (lbl, rule) cs)
        = "\\frac{\\displaystyle " ++ concatMap latex cs
            ++ "}\n{\\displaystyle " ++           latex rule ++ "}"
            ++ "\\mbox{\\ [" ++ lbl ++ "]}" ++ "\\quad "

-- FIXME: superfluous?
instance LaTeX Expr' where
    latex (Con' c       exn)
        = latex c ++ " \\& " ++ latex exn
    latex (Var' x       exn) 
        = latex x ++ " \\& " ++ latex exn
    latex (Abs' x e     exn)
        = "\\left(\\lambda " ++ latex x ++ "." ++ space ++ latex e ++ "\\right)"  ++ " \\& " ++ latex exn
    latex (App' e1 e2   exn) 
        = "\\left(" ++ latex e1 ++ space ++ latex e2 ++ "\\right)"  ++ " \\& " ++ latex exn
    latex (Let' x e1 e2 exn) 
        =  mathbf "let" ++ space ++ latex x  ++ space
        ++ mathbf "="   ++ space ++ latex e1 ++ space
        ++ mathbf "in"  ++ space ++ latex e2
        ++ " \\& " ++ latex exn
{-  latex (Fix' f x e exn) 
        = "\\left(" ++ mathbf "fix" ++ space ++ latex f ++ space ++ latex x
          ++ "." ++ space ++ latex e ++ "\\right)" -}
    latex (If' lbl e0 e1 e2 exn)
        =  mathbf "if_{" ++ lbl ++ "}" ++ space ++ latex e0 ++ space
        ++ mathbf "then" ++ space ++ latex e1 ++ space
        ++ mathbf "else" ++ space ++ latex e2
        ++ " \\& " ++ latex exn

instance LaTeX Ty where
    latex (TyVar a)
        = latex a
    latex (TyCon TyInt)
        = mathbf "Int"
    latex (TyCon TyBool)
        = mathbf "Bool"
    latex (TyFun t1 exn1 t2 exn2)
        = "\\left("  ++ latex t1 ++ "\\ \\&\\ " ++ latex exn1
          ++ "\\to " ++ latex t2 ++ "\\ \\&\\ " ++ latex exn2 ++ "\\right)"
    -- Pairs
    latex (TyPair t1 exn1 t2 exn2)
        = "\\left("  ++ latex t1 ++ "\\ \\&\\ " ++ latex exn1 ++
          "\\times " ++ latex t2 ++ "\\ \\&\\ " ++ latex exn2 ++ "\\right)"
    -- Lists
    latex (TyList t exn)
        = "\\left[" ++ latex t ++ "\\ \\&\\ " ++ latex exn ++ "\\right]"
    
instance LaTeX TyScheme where
    latex (Forall as bs cs t exn) 
        = "\\forall " ++ concatMap latex (as ++ bs)
          ++ " . " ++ latex cs
          ++ " \\Rightarrow " ++ latex t
          ++ " \\ \\&\\ " ++ latex exn

instance LaTeX Exn' where
    latex (ExnVar   b  ) = latex b
    latex (ExnCrash lbl) = "\\lightning_{" ++ latex lbl ++ "}"

instance LaTeX Exn where
    latex (ExnUnif u ) = latex u
    latex (Exn     bs) = latexSet bs

instance LaTeX Constr' where
    latex (exn1 :<: exn2) = latex exn1 ++ "\\sqsubseteq " ++ latex exn2

instance LaTeX Constr where
    latex c = latexSet c
    
instance LaTeX Subst where
    latex (Subst a b) = "\\left[\\begin{split}" ++ latexMap a ++ "; " ++ latexMap b ++ "\\end{split}\\right]"
    
instance LaTeX Rule where
    latex (W' c env e t exn)
        =  "\\begin{split}" -- ++ align
                         ++ latex c   -- ++ newline ++ align
--          ++ ", "        ++ latex env -- ++ newline ++ align
          ++ " \\vdash " ++ latex e   -- ++ newline ++ align
          ++ " : "       ++ latex t   -- ++ newline ++ align
          ++ "\\ \\&\\ " ++ latex exn ++ "\\end{split}"
        
instance LaTeX ExnSubst where
    latex subst = "\\left[\\begin{split}" ++ latexMap subst ++ "\\end{split}\\right]"
