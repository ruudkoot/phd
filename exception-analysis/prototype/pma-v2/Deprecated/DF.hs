{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Deprecated.DF where

import Control.Monad
import Control.Monad.State

import qualified Data.Graph    as G
import qualified Data.List     as L
import qualified Data.Map      as M
import qualified Data.Map.Util as M
import qualified Data.Set      as S
import qualified Data.Set.Util as S
import qualified Data.Tree     as T

import Common

-- | Abstract Syntax

data Expr'  -- refinement annotated expression
    = Var'        Name              Ref
    | Con'        Con               Ref
    | Abs'        Name  Expr'       Ref
    | Fix'        Name  Name  Expr' Ref
    | App'        Expr' Expr'       Ref
    | Let'        Name  Expr' Expr' Ref
    | If'   Lbl   Expr' Expr' Expr' Ref
    -- Operators
    | Op'         Op    Expr' Expr' Ref
    -- Pairs
    | Pair'       Expr' Expr'       Ref
    | Fst'        Expr'             Ref
    | Snd'        Expr'             Ref
    -- Lists
    | Nil'                          Ref
    | Cons'       Expr' Expr'       Ref
    | Case' Lbl   Expr' (Maybe Expr') (Maybe (Name, Name, Expr')) Ref
    deriving (Eq, Ord, Show)
    
-- | Static Semantics

data Ty
    = TyVar Name
    | TyCon TyCon
    | TyFun Ty Ref Ty Ref
    -- Pairs
    | TyPair Ty Ref Ty Ref
    -- Lists
    | TyList Ty Ref
    deriving (Eq, Ord, Show)

data TyCon
    = TyBool
    | TyInt
    deriving (Eq, Ord, Show)

data Ref
    = RefUnif Name
    | Ref (S.Set Ref')
    deriving (Eq, Ord, Show)

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
    
type Constr = S.Set Constr'

data Constr'
    = Ref :<: Ref
    deriving (Eq, Ord, Show)

data TyScheme = Forall [Name] [Name] Constr Ty Ref deriving (Eq, Ord, Show)

type TyEnv = M.Map Name TyScheme
    
-- | Inference Algorithm: Data Flow

-- * Miscellaneous injection and projection helpers

injTS :: Ty -> Ref -> TyScheme
injTS a ref = Forall [] [] S.empty a ref

injRef :: Ref -> Ref
injRef (RefUnif r) = Ref (S.singleton (RefVar r))

prjRef :: Ref' -> Ref
prjRef (RefVar r) = RefUnif r

extrRef :: Ref' -> Name
extrRef (RefVar r) = r

-- * Derivation trees

data Rule
    = W' Constr TyEnv Expr Ty Ref
    deriving (Eq, Ord, Show)

type Deriv = T.Tree (String, Rule)

extrEnv :: Deriv -> TyEnv
extrEnv = M.unionsWith mergeEnv . map extrEnv' . T.flatten where
    extrEnv' (_, W' _ env _ _ _) = env
    mergeEnv ts1 ts2 = if ts1 == ts2 then ts1 else error "incompatible environments"
    
-- *  Algorithm W_DF

inferDF :: TyEnv -> Expr -> InferM (Subst, Ty, Ref, Constr, Deriv, Expr')
inferDF env e
    = do (s1, t1, ref1, c1, d1, e1') <- inferDF' env e
         -- FIXME: Constraint simplification (and sanity checks) go here
         let (c2, s2) = contractCycles . removeReflexive . decompose $ (s1 $@ c1)
         let c3 = removeReflexive (s2 $@ c2)
         return (s2 $. s1, s2 $@ t1, s2 $@ ref1, c3, d1, e1')

inferDF' :: TyEnv -> Expr -> InferM (Subst, Ty, Ref, Constr, Deriv, Expr')
inferDF' env e@(Var x)
    | Just ts <- M.lookup x env
        = do (t, ref, c) <- inst ts
             return ( idSubst, t, ref, c
                    , T.Node ("DF-Var", W' c env e t ref) []
                    , Var' x ref                             )
    | otherwise
        = error $ "identifier '" ++ show x ++ "' not in scope " ++ show env
inferDF' env e@(Con con)
    = do (t, ref, c) <- typeOf con
         return ( idSubst, t, ref, c
                , T.Node ("DF-Con", W' c env e t ref) []
                , Con' con ref                           )
inferDF' env e@(Abs x e0)
    = do (a1, ref1) <- fresh
         let env0 = M.insert x (injTS a1 ref1) env
         (s0, t0, ref0, c0, d0, e0') <- inferDF env0 e0
         ref' <- fresh -- FIXME: ref' is completely unconstrained? ({lambda} :<: ref')
         let t' = TyFun (s0 $@ a1) (s0 $@ ref1) t0 ref0
         return ( s0, t', ref', c0   
                , T.Node ("DF-Abs", W' c0 env e t' ref') [d0]
                , Abs' x e0' ref'                             )
inferDF' env e@(Fix f x e0)
    = do (ax, bx, a0, b0, bf) <- fresh
         let env0 = M.insert f (injTS (TyFun ax bx a0 b0) bf)
                        (M.insert x (injTS ax bx) env)
         (s0, t0, ref0, c0, d0, e0') <- inferDF env0 e0
         let s1 = unify t0 (s0 $@ a0)
         let s2 = unify' (s1 $@ ref0) (s1 $@ s0 $@ b0)
         let t' = TyFun (s2 $@ s1 $@ s0 $@ ax) (s2 $@ s1 $@ s0 $@ bx  )
                        (s2 $@ s1 $@       t0) (s2 $@ s1 $@       ref0)
         let b' = s2 $@ s1 $@ s0 $@ bf
         let c' = s2 $@ s1 $@ c0
         return ( s2 $. s1 $. s0, t', b', c'
                , T.Node ("DF-Fix", W' c' env e t' b') [d0]
                , Fix' f x e0' b'                           )
inferDF' env e@(App e1 e2)
    = do (s1, t1, ref1, c1, d1, e1') <- inferDF        env  e1
         (s2, t2, ref2, c2, d2, e2') <- inferDF (s1 $@ env) e2
         (a, b) <- fresh
         let s3 = unify (s2 $@ t1) (TyFun t2 ref2 a b)
         b' <- fresh
         let t' = s3 $@ a
         let c' = (Ref (effect [s3 $@ b, s3 $@ s2 $@ ref1]) :<: b')
                    `S.insert` (s3 $@ s2 $@ c1) `S.union` (s3 $@ c2)
         return ( s3 $. s2 $. s1, t', b', c'
                , T.Node ("DF-App", W' c' env e t' b') [d1, d2]
                , App' e1' e2' b'                               )
inferDF' env e@(Let x e1 e2)
    = do (s1, t1, ref1, c1, d1, e1') <- inferDF                        env   e1
         let ts1 = gen (s1 $@ env) ref1 c1 t1
         (s2, t2, ref2, c2, d2, e2') <- inferDF (M.insert x ts1 (s1 $@ env)) e2
         let c' = c2 `S.union` (s2 $@ c1)
         return ( s2 $. s1, t2, ref2, c'
                , T.Node ("DF-Let", W' c' env e t2 ref2) [d1, d2]
                , Let' x e1' e2' ref2                             )
inferDF' env e@(If lbl e0 e1 e2)  -- FIXME: ref0 not used (not context-sensitive)
    = do (s0, t0, ref0, c0, d0, e0') <- inferDF              env  e0
         (s1, t1, ref1, c1, d1, e1') <- inferDF (      s0 $@ env) e1
         (s2, t2, ref2, c2, d2, e2') <- inferDF (s1 $@ s0 $@ env) e2
         let s3 = unify (s2 $@ s1 $@ t0) (TyCon TyBool)
         let s4 = unify (s3 $@ s2 $@ t1) (s3 $@ t2)
         let t' = s4 $@ s3 $@ t2
         b' <- fresh
         let c' = (s4 $@ s3 $@ s2 $@ s1 $@ c0)
                  `S.union` (s4 $@ s3 $@ s2 $@ c1) `S.union` (s4 $@ s3 $@ c2)
                  `S.union` S.fromList [ s4 $@ s3 $@ s2 $@ ref1 :<: b'
                                       , s4 $@ s3 $@ ref2       :<: b' ]
         return ( s4 $. s3 $. s2 $. s1 $. s0, t', b', c'
                , T.Node ("DF-If", W' c' env e t' b') [d0, d1, d2]
                , If' lbl e0' e1' e2' b'                           )
-- Operators
inferDF' env e@(Op op@LEQ e1 e2) -- FIXME: ref1 and ref2 not used
    = do (s1, t1, ref1, c1, d1, e1') <- inferDF        env  e1
         (s2, t2, ref2, c2, d2, e2') <- inferDF (s1 $@ env) e2
         let s3 = unify (s2 $@ t1) (TyCon TyInt)
         let s4 = unify (s3 $@ t2) (TyCon TyInt)
         let t' = TyCon TyBool
         b' <- fresh
         let c' = (s4 $@ s3 $@ s2 $@ c1) `S.union` (s4 $@ s3 $@ c2) `S.union`
                     S.singleton (Ref (S.fromList [RefBool True, RefBool False]) :<: b')
         return ( s4 $. s3 $. s2 $. s1, t', b', c'
                , T.Node ("DF-Op", W' c' env e t' b') [d1, d2]
                , Op' op e1' e2' b'                            )
inferDF' env e@(Op op@ADD e1 e2) -- FIXME: ref1 and ref2 not used
    = do (s1, t1, ref1, c1, d1, e1') <- inferDF        env  e1
         (s2, t2, ref2, c2, d2, e2') <- inferDF (s1 $@ env) e2
         let s3 = unify (s2 $@ t1) (TyCon TyInt)
         let s4 = unify (s3 $@ t2) (TyCon TyInt)
         let t' = TyCon TyInt
         b' <- fresh
         let c' = (s4 $@ s3 $@ s2 $@ c1) `S.union` (s4 $@ s3 $@ c2) `S.union`
                     S.singleton (Ref (S.fromList [RefInt Neg, RefInt Zero, RefInt Pos]) :<: b')
         return ( s4 $. s3 $. s2 $. s1, t', b', c'
                , T.Node ("DF-Op", W' c' env e t' b') [d1, d2]
                , Op' op e1' e2' b'                            )
-- Pairs
inferDF' env e@(Pair e1 e2)
    = do (s1, t1, ref1, c1, d1, e1') <- inferDF        env  e1
         (s2, t2, ref2, c2, d2, e2') <- inferDF (s1 $@ env) e2
         let t' = TyPair (s2 $@ t1) (s2 $@ ref1) t2 ref2
         b' <- fresh
         let c' = s2 $@ c1 `S.union` c2
         return ( s2 $. s1, t', b', c'
                , T.Node ("DF-Pair", W' c' env e t' b') [d1, d2]
                , Pair' e1' e2' b'                               )
inferDF' env e@(Fst e0)
    = do (s0, t0, ref0, c0, d0, e0') <- inferDF env e0
         (a1, b1, a2, b2) <- fresh
         let s1 = unify t0 (TyPair a1 b1 a2 b2)
         let t' = s1 $@ a1
         let b' = s1 $@ b1
         let c' = s1 $@ c0
         return ( s1 $. s0, t', b', c'
                , T.Node ("DF-Fst", W' c' env e t' b') [d0]
                , Fst' e0' b'                               )
inferDF' env e@(Snd e0)
    = do (s0, t0, ref0, c0, d0, e0') <- inferDF env e0
         (a1, b1, a2, b2) <- fresh
         let s1 = unify t0 (TyPair a1 b1 a2 b2)
         let t' = s1 $@ a2
         let b' = s1 $@ b2
         let c' = s1 $@ c0
         return ( s1 $. s0, t', b', c'
                , T.Node ("DF-Snd", W' c' env e t' b') [d0]
                , Snd' e0' b'                               )
-- Lists
inferDF' env e@Nil
    = do (a, b1, b2) <- fresh
         let t = TyList a b1
         let c = S.singleton (Ref (S.singleton (RefList E)) :<: b2)
         return ( idSubst, t, b2, c
                , T.Node ("DF-Nil", W' c env e t b2) []
                , Nil' b2                               )
inferDF' env e@(Cons e1 e2)
    = do (s1, t1, ref1, c1, d1, e1') <- inferDF        env  e1
         (s2, t2, ref2, c2, d2, e2') <- inferDF (s1 $@ env) e2
         q <- fresh
         let s3 = unify t2 (TyList (s2 $@ t1) q)
         b1q <- fresh
         let t = TyList (s3 $@ s2 $@ t1) b1q
         b2 <- fresh
         let c = S.fromList [ Ref (S.singleton (RefList NE)) :<: b2
                            , s3 $@ s2 $@ ref1               :<: b1q
                            , s3 $@ q                        :<: b1q ]
                 `S.union` (s3 $@ s2 $@ c1) `S.union` (s3 $@ c2)
         return ( s3 $. s2 $. s1, t, b2, c
                , T.Node ("DF-Cons", W' c env e t b2) [d1, d2]
                , Cons' e1' e2' b2                             )
inferDF' env e@(Case lbl e0 arm1 arm2)
    = do -- Scrutinee
         (s0, t0, ref0, c0, d0, e0') <- inferDF env e0
         (a0, b0) <- fresh
         let s0' = unify t0 (TyList a0 b0)
         
         -- Nil arm
         (s1, t1, ref1, c1, d1, e1')
            <- case arm1 of
                Just e1 ->
                    inferDF (s0' $@ s0 $@ env) e1
                Nothing ->
                    do (a, b) <- fresh
                       let e = ExnC lbl PatternMatchFail
                       return ( idSubst, a, b, S.empty
                              , T.Node ( "DF-Case-Nil", W' S.empty env (Con e) a b ) []
                              , Con' e b                                                )

         -- Cons arm
         (x', xs') <- maybe (do {(q,w) <- fresh; return (augment "Q" q, augment "W" w)})(\(x, xs, _) -> return (x, xs)) arm2    -- FIXME: fresh not nicely named
         
         refCONS <- fresh

         (s2, t2, ref2, c2, d2, e2')
            <- case arm2 of
                Just (x, xs, e2) ->
                    inferDF (M.insert x  (injTS (s1 $@ s0' $@ a0)
                                                (s1 $@ s0' $@ b0))
                            (M.insert xs (injTS (TyList (s1 $@ s0' $@ a0)
                                                        (s1 $@ s0' $@ b0))
                                                refCONS)    -- FIXME: test with ref0 to
                                                            -- see if we can detect the
                                                            -- unsoundness (yes we can)
                            (s1 $@ s0' $@ s0 $@ env)))
                            e2
                Nothing ->
                    do (a, b) <- fresh
                       let e = ExnC lbl PatternMatchFail
                       return ( idSubst, a, b, S.empty
                              , T.Node ("DF-Case-Cons", W' S.empty env (Con e) a b) []
                              , Con' e b                                               )

         -- Return type
         let s3 = unify (s2 $@ t1) t2

         let t' = s3 $@ t2
         b' <- fresh
         let c' = (s3 $@ s2 $@ s1 $@ s0' $@ c0)
                  `S.union` (s3 $@ s2 $@ c1) `S.union` (s3 $@ c2)
                  `S.union` S.fromList [ s3 $@ s2 $@ ref1                 :<: b'
                                       , s3 $@       ref2                 :<: b'
                                       , Ref (S.fromList [ RefList E
                                                         , RefList NE ] ) :<: refCONS ]

         return ( s3 $. s2 $. s1 $. s0' $. s0, t', b', c'
                , T.Node ("DF-Case", W' c' env e t' b') [d0, d1, d2]
                , Case' lbl e0' (Just e1') (Just (x', xs', e2')) b'  )

effect = S.fromList . map (\(RefUnif u) -> RefVar u)

-- * Instantiation

inst :: TyScheme -> InferM (Ty, Ref, Constr)
inst (Forall as bs c t ref)
    = do as' <- replicateM (length as) fresh
         bs' <- replicateM (length bs) fresh'
         let r = Subst (M.fromList (zip as as')) (M.fromList (zip bs bs'))
         return (r $@ t, r $@ ref, r $@ c)
         
fresh' :: InferM Name
fresh' = do b <- fresh
            return (augment "\\beta" b)

-- * Generalization

-- TODO: let-bound polymorphism and polyvariance
gen :: TyEnv -> Ref -> Constr -> Ty -> TyScheme
gen env ref c t = injTS t ref

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
unify (TyFun t1 ref1 t2 ref2) (TyFun t1' ref1' t2' ref2')
    = let s1 = unify' (                  ref1) (                  ref1')
          s2 = unify' (            s1 $@ ref2) (            s1 $@ ref2')
          s3 = unify  (      s2 $@ s1 $@ t1  ) (      s2 $@ s1 $@ t1'  )
          s4 = unify  (s3 $@ s2 $@ s1 $@ t2  ) (s3 $@ s2 $@ s1 $@ t2'  )
       in s4 $. s3 $. s2 $. s1
-- Pairs
unify (TyPair t1 ref1 t2 ref2) (TyPair t1' ref1' t2' ref2')
    = let s1 = unify' (                  ref1) (                  ref1')
          s2 = unify' (            s1 $@ ref2) (            s1 $@ ref2')
          s3 = unify  (      s2 $@ s1 $@ t1  ) (      s2 $@ s1 $@ t1'  )
          s4 = unify  (s3 $@ s2 $@ s1 $@ t2  ) (s3 $@ s2 $@ s1 $@ t2'  )
       in s4 $. s3 $. s2 $. s1
-- Lists
unify (TyList t1 ref1) (TyList t2 ref2)
    = let s1 = unify'        ref1         ref2
          s2 = unify  (s1 $@ t1  ) (s1 $@ t2  )
       in s2 $. s1
unify _ _
    = error "constructor clash"

unify' :: Ref -> Ref -> Subst
unify' (RefUnif u1) (RefUnif u2)
    | u1 == u2  = Subst M.empty M.empty
    | otherwise = Subst M.empty (M.singleton u1 u2)
unify' ref1 ref2
    = error $ "not a simple type: ref1 = " ++ show ref1 ++ ", ref2 = " ++ show ref2

-- * Typing of constants

typeOf :: Con -> InferM (Ty, Ref, Constr)
typeOf (Bool x)
    = do b <- fresh
         return ( TyCon TyBool, b
                , S.singleton (Ref (S.singleton (RefBool x        )) :<: b))
typeOf (Int n)
    = do b <- fresh
         return ( TyCon TyInt , b
                , S.singleton (Ref (S.singleton (RefInt (injInt n))) :<: b))
typeOf (ExnC _ _)
    = do (a, b) <- fresh
         return (a, b, S.empty)
{- constant-style (currenly using eliminator-style)
-- Pairs
typeOf Fst
    = do (a1, b1, a2, b2, b3, b4) <- fresh
         return ( TyFun (TyPair a1 b1 a2 b2) b3 a1 b1
                , b4
                , S.empty                             )
typeOf Snd
    = do (a1, b1, a2, b2, b3, b4) <- fresh
         return ( TyFun (TyPair a1 b1 a2 b2) b3 a1 b1
                , b4
                , S.empty                             )
-- Operators
typeOf Leq
    = do (b1, b2, b3, b4, b5) <- fresh
         return ( TyFun (TyCon TyInt) b1 (TyFun (TyCon TyInt) b2 (TyCon TyBool) b3) b4
                , b5
                , S.singleton (Ref (S.fromList [RefBool True, RefBool False]) :<: b3)  )
-}
-- | Constraint simplification

-- * Decomposition into singleton (atomic?) constraints

decompose :: Constr -> Constr
decompose c
    = S.foldr (\c' r -> r `S.union` decompose' c') S.empty c

decompose' :: Constr' -> Constr
decompose' (Ref refs :<: b@(RefUnif _))
    = S.unionMap (\ref' -> S.singleton (Ref (S.singleton ref') :<: b)) refs
decompose' (RefUnif b1 :<: b2@(RefUnif _)) -- FIXME: we shouldn't (but do) generate these
    = S.singleton (Ref (S.singleton (RefVar b1)) :<: b2)
    
-- * Remove reflexive constraints

removeReflexive :: Constr -> Constr
removeReflexive
    = S.foldr (\c'@(l :<: r) cr -> if l == injRef r then cr else S.insert c' cr)
              S.empty

-- * Constract cyclic constraints (strongly connected components)

-- FIXME: extremely dubious code

contractCycles :: Constr -> (Constr, Subst)
contractCycles c
    = let sccs = G.stronglyConnCompR (toGraph c)
          (c', s') = foldr pc (S.empty, M.empty) sccs
       in (c', Subst M.empty s')

pc :: G.SCC ((), Ref', [Ref']) -> (Constr, M.Map Name Name) -> (Constr, M.Map Name Name)
pc (G.AcyclicSCC ((), r, vs)) (cr, sr)
    = ( foldr (\v -> S.insert (Ref (S.singleton r) :<: prjRef v)) cr vs
      , sr                                                                           )
pc (G.CyclicSCC scc@(((), r', _):scc')) (cr, sr)
    = ( foldr (\((), r, vs) cr' ->
            foldr (\v -> S.insert (Ref (S.singleton r) :<: prjRef v)) cr' vs
        ) cr scc
      , foldr (\((), r'', _) sr' -> M.insert (extrRef r'') (extrRef r') sr') sr scc' )

-- | Constraint solving (assumes constraints have been decomposed and decycled!)

type RefSubst = M.Map Name Ref -- FIXME: newtype

solve :: Constr -> RefSubst -> RefSubst
solve c subst0
    = let sccs = G.stronglyConnCompR (toGraph c)
       in foldr processComponent subst0 sccs

processComponent :: G.SCC ((), Ref', [Ref']) -> RefSubst -> RefSubst
processComponent (G.AcyclicSCC ((), RefVar b, vs)) subst
    = foldr (\(RefVar v) -> M.insertWith refJoin v (subst M.!! b)) subst vs
processComponent (G.AcyclicSCC ((), refcon, vs)) subst
    = foldr (\(RefVar v) -> M.insertWith refJoin v (Ref (S.singleton refcon))) subst vs
processComponent (G.CyclicSCC _) _
    = error "DF.processComponent: CyclicSCC (did you forget to decompose the constraint set?)"

-- FIXME: Use a representation more suited for the none R version and already apply prj
toGraph :: Constr -> [((), Ref', [Ref'])]
toGraph = map (\(k, v) -> ((), k, S.toList v)) . M.toList . toMap

toMap :: Constr -> M.Map Ref' (S.Set Ref')
toMap = S.foldr f M.empty
    where f (Ref ref1' :<: RefUnif ref2) | Just (ref1, _) <- S.minView ref1'
            = M.insertWith S.union ref1 (S.singleton (RefVar ref2))

refJoin :: Ref -> Ref -> Ref
refJoin (Ref refs1) (Ref refs2) = Ref (refs1 `S.union` refs2)

initSubst :: Ty -> Constr -> Expr' -> RefSubst
initSubst t c e' = S.foldr (\k -> M.insert k (Ref S.empty)) M.empty (fev t `S.union` fev c `S.union` fev e')

-- | Free variables

class FreeVars a where
    ftv :: a -> S.Set Name
    fev :: a -> S.Set Name
    
instance FreeVars Expr' where
    ftv = error "DF.ftv_Expr'"

    fev (Var'    _        ref) 
        = fev ref
    fev (Con'    _        ref)
        = fev ref
    fev (Abs'    _  e     ref)
        = fev ref `S.union` fev e
    fev (Fix'    _  _  e  ref)
        = fev ref `S.union` fev e
    fev (App'    e1 e2    ref)  
        = fev ref `S.union` fev e1 `S.union` fev e2
    fev (Let'    _  e1 e2 ref)
        = fev ref `S.union` fev e1 `S.union` fev e2
    fev (If'   _ e0 e1 e2 ref)
        = fev ref `S.union` fev e0 `S.union` fev e1 `S.union` fev e2
    -- Operators
    fev (Op'     op e1 e2 ref)  
        = fev ref `S.union` fev e1 `S.union` fev e2
    -- Pairs
    fev (Pair'   e1 e2    ref)
        = fev ref `S.union` fev e1 `S.union` fev e2
    fev (Fst'    e        ref)
        = fev ref `S.union` fev e
    fev (Snd'    e        ref)  
        = fev ref `S.union` fev e
    -- Lists
    fev (Nil'             ref)  
        = fev ref
    fev (Cons'   e1 e2    ref)
        = fev ref `S.union` fev e1 `S.union` fev e2
    fev (Case' _ e0 e1 e2 ref)
        = fev ref `S.union` fev e0 `S.union` fev e1 `S.union` fev e2
    
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

instance FreeVars Ref where
    ftv (RefUnif e ) = S.empty
    ftv (Ref     es) = S.unionMap ftv es
    
    fev (RefUnif e ) = S.singleton e
    fev (Ref     es) = S.unionMap fev es

instance FreeVars Ref' where
    ftv _           = S.empty

    fev (RefVar  z) = S.singleton z
    fev (RefTop   ) = S.empty
    fev (RefBool _) = S.empty
    fev (RefInt  _) = S.empty
    fev (RefList _) = S.empty

instance FreeVars Constr' where
    ftv = error "supress warnings"
    fev (ref1 :<: ref2) = fev ref1 `S.union` fev ref2

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
                where overlapError a b = error $ "DF.$+: overlapping substitutions: a = " ++ show a ++ ", b = " ++ show b ++ ", tv1 = " ++ show tv1 ++ ", tv2 = " ++ show tv2 ++ ", ev1 = " ++ show ev1 ++ ", ev2 = " ++ show ev2

class Substitute t where
    ($@) :: Subst    -> t -> t
    ($#) :: RefSubst -> t -> t
    
instance Substitute Expr' where -- FIXME: instance Functor Expr'
    subst $@ (Var' x ref)
        = Var' x (subst $@ ref)
    subst $@ (Con' c ref)
        = Con' c (subst $@ ref)
    subst $@ (Abs' x e ref)
        = Abs' x (subst $@ e) (subst $@ ref)
    subst $@ (Fix' f x e ref)
        = Fix' f x (subst $@ e) (subst $@ ref)
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
    subst $# (Fix' f x e ref)
        = Fix' f x (subst $# e) (subst $# ref)
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

instance Substitute Ref where
    subst $@ RefUnif e  = RefUnif    (subst $@  e )
    subst $@ Ref     es = Ref (S.map (subst $@) es)
    
    subst $# r@(RefUnif e) = M.findWithDefault r e subst -- FIXME: this should (but doesn't) always succeed, need to make sure the solver instantiates solutions with bottom...
    subst $#    Ref     es = Ref (S.unionMap f es)
        where f (RefVar e) = let Ref r = subst M.! e in r
              f r          = S.singleton (subst $# r)

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
    
instance Substitute Constr where
    subst $@ c = S.map (subst $@) c
    subst $# c = S.map (subst $#) c
        
instance Substitute Constr' where
    subst $@ (ref1 :<: ref2) = (subst $@ ref1) :<: (subst $@ ref2)
    subst $# (ref1 :<: ref2) = (subst $# ref1) :<: (subst $# ref2)

instance Substitute TyScheme where
    Subst tv bv $@ Forall as bs c t ref
        = let s' = Subst (tv `M.restrict` as) (bv `M.restrict` bs)
           in Forall as bs (s' $@ c) (s' $@ t) (s' $@ ref)
    bv $# Forall as bs c t ref
        = let s' = bv `M.restrict` bs
           in Forall as bs (s' $# c) (s' $# t) (s' $# ref)

instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env
    subst $# env = M.map (subst $#) env
    
instance Substitute (String, Rule) where
    subst $@ (lbl, W' c env e t ref)
        = (lbl, W' (subst $@ c) (subst $@ env) e (subst $@ t) (subst $@ ref))
    subst $# (lbl, W' c env e t ref)
        = (lbl, W' (subst $# c) (subst $# env) e (subst $# t) (subst $# ref))
    
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

instance Fresh Ref where
    fresh = do b <- fresh
               return (RefUnif (augment "\\beta" b))

-- | Pretty Printing

instance LaTeX TyEnv where
    latex env | M.null env = "\\epsilon "
              | otherwise  = ("\\left[\\begin{split}"++) . (++"\\end{split}\\right]") . L.intercalate newline . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v) . M.toList $ env

instance LaTeX (T.Tree (String, Rule)) where
    latex (T.Node (lbl, rule) cs)
        = "\\frac{" ++ {- "\\displaystyle " ++ -} concatMap latex cs
            ++ "}\n{" ++ {- "\\displaystyle " ++ -}          latex rule ++ "}"
            ++ "\\mbox{\\ [" ++ lbl ++ "]}" ++ "\\quad"

instance LaTeX Expr' where
    latex (Con' c       ref)
        = latex c ++ "@" ++ latex ref
    latex (Var' x       ref) 
        = latex x ++ "@" ++ latex ref
    latex (Abs' x e     ref)
        = "\\left(\\lambda " ++ latex x ++ "." ++ space ++ latex e ++ "\\right)"  ++ "@" ++ latex ref
    latex (App' e1 e2   ref) 
        = "\\left(" ++ latex e1 ++ space ++ latex e2 ++ "\\right)"  ++ "@" ++ latex ref
    latex (Let' x e1 e2 ref) 
        =  mathbf "let" ++ space ++ latex x  ++ space
        ++ mathbf "="   ++ space ++ latex e1 ++ space
        ++ mathbf "in"  ++ space ++ latex e2
        ++ "@" ++ latex ref
{-  latex (Fix' f x e ref) 
        = "\\left(" ++ mathbf "fix" ++ space ++ latex f ++ space ++ latex x
          ++ "." ++ space ++ latex e ++ "\\right)" -}
    latex (If' lbl e0 e1 e2 ref)
        =  mathbf "if_{" ++ lbl ++ "}" ++ space ++ latex e0 ++ space
        ++ mathbf "then" ++ space ++ latex e1 ++ space
        ++ mathbf "else" ++ space ++ latex e2
        ++ "@" ++ latex ref

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
    latex (Forall as bs cs t ref) 
        = "\\forall " ++ concatMap latex (as ++ bs)
          ++ " . " ++ latex cs
          ++ " \\Rightarrow " ++ latex t
          ++ "@" ++ latex ref

instance LaTeX Ref' where
    latex (RefVar  b) = latex b
    latex (RefTop   ) = "\\top "
    latex (RefBool b) = mathbf (show b)
    latex (RefInt  n) = latex n
    -- Lists
    latex (RefList l) = mathbf (show l)

instance LaTeX Ref where
    latex (RefUnif u ) = latex u
    latex (Ref     bs) = latexSet bs
    
instance LaTeX Int' where
    latex Neg  = mathbf "-"
    latex Zero = mathbf "0"
    latex Pos  = mathbf "+"

instance LaTeX Constr' where
    latex (ref1 :<: ref2) = latex ref1 ++ "\\sqsubseteq " ++ latex ref2

instance LaTeX Constr where
    latex c = latexSet c
    
instance LaTeX Subst where
    latex (Subst a b) = "\\left[\\begin{split}" ++ latex' a ++ "; " ++ latex' b ++ "\\end{split}\\right]"
        where latex' m | M.null m  = "\\epsilon"
                       | otherwise = L.intercalate newline . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v) . M.toList $ m
    
instance LaTeX Rule where
    latex (W' c env e t ref)
        =  "\\begin{split}" -- {- ++ align -} ++                latex c   -- ++ newline
                            -- {- ++ align -} ++ ", "        ++ latex env -- ++ newline
                            {- ++ align -} ++ " \\vdash " ++ latex e   -- ++ newline
                            {- ++ align -} ++ " : "       ++ latex t   -- ++ newline
                            {- ++ align -} ++ "@"         ++ latex ref
        ++ "\\end{split}"
        
instance LaTeX RefSubst where
    latex subst = "\\left[\\begin{split}" ++ latexMap subst ++ "\\end{split}\\right]"
