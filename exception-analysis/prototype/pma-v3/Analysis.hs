{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Analysis where

import Debug.Trace               as Debug

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

import Subst
import Syntax
import Fresh
import FTV
import Types
import Shapes
import Constr
import Ref
import Exn

-- | Pattern-matching types and type schemes

-- * Types

type PmTy = (Sh, Constr Ref Ref, Constr Exn Ref)
    -- FIXME: should perhaps be a datatype, as we run into overlapping instances

instance FTV PmTy where
    ftv (sh, c1, c2) = ftv sh `S.union` ftv c1 `S.union` ftv c2

-- * Type schemes

data PmScheme
    = Forall (S.Set Name) {- (S.Set Name) -} PmTy
    deriving (Eq, Show) -- FIXME: dangerous, we often want eq modulo alpha-renaming
    
instance FTV PmScheme where
    ftv (Forall q pmty) = ftv pmty `S.difference` q
    
scheme :: PmTy -> PmScheme
scheme = Forall S.empty

-- | Instantiation

inst :: PmScheme -> InferM PmTy
inst (Forall q (sh, c1, c2))
    = do q' <- replicateM (S.size q) (fresh :: InferM Name)
         let s = M.fromList (zip (S.toList q) q')
         return (s $@ sh, s $@ c1, s $@ c2)

-- | Generalization

-- gen :: x -> PmTy -> PmScheme -- FIXME: needs env and constr
gen env pmty
    = let -- polyvariant
          q = ftv pmty `S.difference` ftv env
          -- monovariant
          -- q = S.empty
       in Forall q pmty

schemeFromShape :: Sh -> PmScheme
schemeFromShape sh = Forall S.empty (sh, S.empty, S.empty)

least :: Ty -> InferM PmScheme
least t = do (q, k) <- least' t
             return (Forall q (k, S.empty, S.empty))
  where
    least' :: Ty -> InferM (S.Set Name, Sh)
    least' (TyVar _) -- FIXME: can we handle polymorphism in the underlying system?
        = do d <- fresh
             return (S.singleton d, (ShBase d))
    least' (TyCon c)
        = do d <- fresh
             return (S.singleton d, (ShBase d))
    least' (TyFun t1 t2)
        = do (q1, sh1) <- least' t1
             (q2, sh2) <- least' t2
             d <- fresh
             return ( q1 `S.union` q2 `S.union` S.singleton d
                    , ShFun sh1 sh2 d                         )
    least' (TyPair t1 t2)
        = do (q1, sh1) <- least' t1
             (q2, sh2) <- least' t2
             d <- fresh
             return ( q1 `S.union` q2 `S.union` S.singleton d
                    , ShPair sh1 sh2 d                        )
    least' (TyList t)
        = do (q, sh) <- least' t
             d <- fresh
             return ( q `S.union` S.singleton d
                    , ShList sh d               )
                    
genericInstanceOf :: PmScheme -> PmScheme -> Bool
genericInstanceOf (Forall q1 (sh1, rc1, xc1)) (Forall q2 (sh2, rc2, xc2))
    = let subst = unifySh sh1 sh2
       in if S.size rc1 > 250 then True else False{-
       in (subst $@ q1) == (subst $@ q2)
            && (subst $@ rc1) == (subst $@ rc2)
            && (subst $@ xc1) == (subst $@ xc2)
-}
unifySh :: Sh -> Sh -> Subst Name
unifySh (ShBase d1) (ShBase d2)
    | d1 == d2  = idSubst
    | otherwise = M.singleton d1 d2
unifySh (ShFun sh1 sh2 d) (ShFun sh1' sh2' d')
    = let s1 = unifySh        sh1         sh1'
          s2 = unifySh (s1 $@ sh2) (s1 $@ sh2')
       in s2 $. s1
unifySh (ShPair sh1 sh2 d) (ShPair sh1' sh2' d')
    = let s1 = unifySh        sh1         sh1'
          s2 = unifySh (s1 $@ sh2) (s1 $@ sh2')
       in s2 $. s1
unifySh (ShList sh d) (ShList sh' d')
    = let s1 = unifySh        sh          sh'
       in s1
       
-- | Constraint elimination
{-
elim :: S.Set Name -> Constr -> BtEnv -> BtTy -> Constr
elim v c env' k
    = S.foldr f c (fbv c)
        where negativeOccurences =
                negativeVariables (M.foldr (\(Forall _ _ k') -> BtFun k' (BtCon S)) k env')
              f b c = if b `S.notMember` (negativeOccurences `S.union` v)
                      then g (BtVar b) c
                      else c
              g b c = let (r, l, n) = trisect b c
                          r' = S.map (\(b' :<: _) -> b') r
                          l' = S.unionMap (\(_ :<: b') -> S.map (\r -> r :<: b') r') l
                       in l' `S.union` n
              trisect b c = S.foldr h (S.empty, S.empty, S.empty) c
                where h c@(b1 :<: b2) (r, l, n)
                        | b1 == b2  = error "reflexive constraint encountered"
                        | b2 == b   = (c `S.insert` r, l, n)
                        | b1 == b   = (r, c `S.insert` l, n)
                        | otherwise = (r, l, c `S.insert` n)
-}
-- | Analysis

analyze :: Env PmScheme -> Expr Ty -> InferM (PmTy, Expr (Env PmScheme, PmTy))
analyze env e@(Var x ty)
    -- FIXME: fresh name + constraint here?
    | Just pmsch <- M.lookup x env
        = do pmty <- inst pmsch
             return (pmty, Var x (env, pmty))
    | otherwise
        = error $ "identifier '" ++ show x ++ "' not in scope " ++ show env
analyze env e@(Con con ty)
    = do pmty <- pmtyOf con ty
         return (pmty, Con con (env, pmty))
analyze env e@(Abs x e0 ty@(TyFun tx tr))
    = do k <- freshLinearShapeFrom tx
         let env' = M.insert x (schemeFromShape k) env
         ((sh0, cr0, cx0), e0') <- analyze env' e0
         ann <- fresh
         let sh' = ShFun k sh0 ann
         return ((sh', cr0, cx0), Abs x e0' (env, (sh', cr0, cx0)))
analyze env e@(Fix f e0 ty)
    -- FIXME: add flag to disable polyvariant recursion
    = do let elim _ _ (_, rc, xc) = (rc, xc)

         let kleeneMycroft envI ksI = do
                ((kJ, rcJ, xcJ), e'J) <- analyze envI e0
                let (rcJ', xcJ') = elim {-(ftv envI `S.union` ftv kJ)-}undefined envI (kJ, rcJ, xcJ)
                let ksJ = gen envI (kJ, rcJ', xcJ')
                if {-Debug.trace (show $ S.size rcJ')-} (ksJ `genericInstanceOf` ksI)
                    then return ((kJ, rcJ', xcJ'), Fix f e'J (env, (kJ, rcJ', xcJ')))
                    else let envJ = M.insert f ksJ envI
                          in kleeneMycroft envJ ksJ

         ks0 <- least ty
         let env0 = M.insert f ks0 env
         kleeneMycroft env0 ks0

{-  = do k <- least ty
         let env' = M.insert f k env
         ((sh0, cr0, cx0), e0') <- analyze env' e0
         let cr' = S.fromList [sh0 :<# k] `S.union` cr0 -- FIXME: no counter-example yet
         let cx' = S.fromList [sh0 :<# k] `S.union` cx0 --        (if returning sh0)
         return ((sh0, cr', cx'), Fix f e0' ( env, (sh0, cr', cx')))
            -- FIXME: sh0 or k? If we have sh0 <: k then this doesn't seem and
            --        probably does not matter. If we don't, k is definitely
            --        unsound, sh0 may or may not be.
-}

analyze env e@(App e1 e2 ty)
    = do ((sh1@(ShFun sh1x sh1r ann), cr1, cx1), e1') <- analyze env e1
         ((sh2                      , cr2, cx2), e2') <- analyze env e2
         let cr' = (sh2 :<# sh1x) `S.insert` cr1 `S.union` cr2
         let cx' = S.fromList [ C (S.singleton (ExnVar ann)) :<: topLevelAnnotation sh1r
                              , sh2 :<# sh1x                                         ]
                        `S.union` cx1 `S.union` cx2
                         -- FIXME: should we create an intermediate freshLinearShape
                         --        instead of flowing directly into sh1r?
         return ((sh1r, cr', cx'), App e1' e2' (env, (sh1r, cr', cx')))
analyze env e@(Let x e1 e2 ty)
    = do ((sh1, cr1, cx1), e1') <- analyze env  e1
         let env' = M.insert x (gen env (sh1, cr1, cx1)) env
         ((sh2, cr2, cx2), e2') <- analyze env' e2
         let cr' = cr1 `S.union` cr2
         let cx' = cx1 `S.union` cx2
         return ((sh2, cr', cx'), Let x e1' e2' (env, (sh2, cr', cx')))
analyze env e@(If lbl e0 e1 e2 ty)
    = do ((ShBase a0, cr0, cx0), e0') <- analyze env e0
         ((sh1, cr1, cx1), e1') <- analyze env e1
         ((sh2, cr2, cx2), e2') <- analyze env e2
         sh' <- freshLinearShapeFrom ty
         let cr' = S.fromList [ CC (S.singleton (RefBool True )) a0 sh1 sh'
                              , CC (S.singleton (RefBool False)) a0 sh2 sh'
                              ]
                    `S.union` cr0 `S.union` cr1 `S.union` cr2
         let cx' = S.fromList [ a0 `flowTopLevelAnnotation` sh'
                              , CC (S.singleton (RefBool True )) a0 sh1 sh'
                              , CC (S.singleton (RefBool False)) a0 sh2 sh'
                              ]
                    `S.union` cx0 `S.union` cx1 `S.union` cx2
         return ((sh', cr', cx'), If lbl e0' e1' e2' (env, (sh', cr', cx')))
-- Operators
analyze env e@(Op op e1 e2 ty)
    = do ((sh1@(ShBase _), cr1, cx1), e1') <- analyze env e1
         ((sh2@(ShBase _), cr2, cx2), e2') <- analyze env e2
         ref <- fresh
         let sh' = ShBase ref
         let cr' = S.singleton (C (S.fromList (outputs op)) :<: ref)
                    `S.union` cr1 `S.union` cr2
                    -- FIXME: it is interesting that if we would be trying to infer
                    --        types here, we might also want to constrain the types
                    --        of the inputs to the operator (upper-bounds?)
         let cx' = S.fromList [sh1 :<# sh', sh2 :<# sh'] `S.union` cx1 `S.union` cx2
         return ((sh', cr', cx'), Op LEQ e1' e2' (env, (sh', cr', cx')))
            where
                outputs :: Op -> [Ref]
                outputs LEQ = [RefBool True, RefBool False]
                outputs ADD = [RefInt Neg, RefInt Zero, RefInt Pos]
-- Pairs
analyze env e@(Pair e1 e2 ty)
    = do ((sh1, cr1, cx1), e1') <- analyze env e1
         ((sh2, cr2, cx2), e2') <- analyze env e2
         ann <- fresh
         let sh' = ShPair sh1 sh2 ann
         let cr' = cr1 `S.union` cr2
         let cx' = cx1 `S.union` cx2
         return ((sh', cr', cx'), Pair e1' e2' (env, (sh', cr', cx')))
analyze env e@(Fst e0 ty)
    = do ((ShPair sh1 sh2 ann, cr0, cx0), e0') <- analyze env e0
         -- FIXME: intermediate freshLinear here? (addition of Exn suggests yes!)
         -- FIXME: cleanup constraint set here?
         let cx' = constr (injName ann) (topLevelAnnotation sh1) `S.union` cx0
         return ((sh1, cr0, cx'), Fst e0' (env, (sh1, cr0, cx')))
analyze env e@(Snd e0 ty)
    = do ((ShPair sh1 sh2 ann, cr0, cx0), e0') <- analyze env e0
         -- FIXME: intermediate freshLinear here?
         -- FIXME: cleanup constraint set here?
         let cx' = constr (injName ann) (topLevelAnnotation sh2) `S.union` cx0
         return ((sh2, cr0, cx'), Snd e0' (env, (sh2, cr0, cx')))
-- Lists
analyze env e@(Nil ty@(TyList t1))
    = do sh1 <- freshLinearShapeFrom t1 -- FIXME: doesn't generate a top-level ann.?
         ref <- fresh
         let sh' = ShList sh1 ref
         let cr' = S.singleton (C (S.fromList [RefList E]) :<: ref)
         return ((sh', cr', S.empty), Nil (env, (sh', cr', S.empty)))
analyze env e@(Cons e1 e2 ty@(TyList t))
    = do ((sh1            , cr1, cx1), e1') <- analyze env e1
         ((ShList sh2 ref2, cr2, cx2), e2') <- analyze env e2
         shI <- freshLinearShapeFrom t
         ref <- fresh
         let sh' = ShList shI ref
         let cr' = S.fromList [ sh1 :<# shI
                              , sh2 :<# shI
                           -- , C (S.singleton (injName ref2)) :<: ref -- DON'T DO THIS!
                              , C (S.fromList [RefList NE]) :<: ref
                              ]
                    `S.union` cr1 `S.union` cr2
            {- NOTE THAT THE REFINEMENT CONSTRAINTS ONLY TELL USE SOMETHING ABOUT
               THE HEAD OF THE LIST. WE ARE OPTIMISTIC HERE, BUT HAVE TO BE PESSIMISTIC
               IN [T-CASE] (THE FIRST IS IMPORTANT THE SECOND DOESN'T HURT).
            -}
         let cx' = S.fromList [ sh1 :<# shI
                              , sh2 :<# shI
                              , C (S.singleton (injName ref2)) :<: ref -- BUT DO SO HERE
                              ]
            {- IN CONTRAST THE EXCEPTION CONSTRAINTS TELL US SOMETHING ABOUT THE WHOLE
               SPINE OF THE LIST. THIS ALLOWS US TO BE OPTIMISTIC IN THE [T-CASE]
               (THIS IS IMPORTANT, WHILE BEING PESSIMISTIC HERE RARELY HURTS).
            -}
                    `S.union` cx1 `S.union` cx2
         return ((sh', cr', cx'), Cons e1' e2' (env, (sh', cr', cx')))
analyze env e@(Case lbl e0 (Just e1) (Just (x, xs, e2)) ty) -- FIXME: pessimistic for Exn
    = do ((sh0@(ShList shl nl), cr0, cx0), e0') <- analyze env e0
         ((sh1,                 cr1, cx1), e1') <- analyze env e1
         fr <- fresh
         let fcr = S.fromList [C (S.fromList [RefList E, RefList NE]) :<: fr]
         let fcx = S.fromList [C (S.fromList [ExnVar nl            ]) :<: fr]
         let env' = M.insert x   (scheme (shl          , S.empty, S.empty))
                        -- FIXME: ^^^ we're only passing shapes here,
                        --        not constraints this looks problematic
                    (M.insert xs (scheme (ShList shl fr, fcr    , fcx    )) env)
                        -- scheme or something more elaborate?
         ((sh2, cr2, cx2), e2') <- analyze env' e2
         sh' <- freshLinearShapeFrom ty
         let cr' = S.fromList [ CC (S.singleton (RefList E )) nl sh1 sh'
                              , CC (S.singleton (RefList NE)) nl sh2 sh'
                              ]
                    `S.union` cr0 `S.union` cr1 `S.union` cr2 -- FIXME: what about fc??
         let cx' = S.fromList [ C (S.singleton (injName nl)) :<: topLevelAnnotation sh'
                              , CC (S.singleton (RefList E )) nl sh1 sh'
                              , CC (S.singleton (RefList NE)) nl sh2 sh'
                              ]
                    `S.union` cx0 `S.union` cx1 `S.union` cx2
         return ((sh', cr', cx'), Case lbl e0' (Just e1') (Just (x, xs, e2')) (env, (sh', cr', cx')))

-- FIXME: used only once (use either twice or not at all...)
flowTopLevelAnnotation :: ConstrElem a => Name -> Sh -> Constr' a b
flowTopLevelAnnotation n1 sh2
    = C (S.singleton (injName n1)) :<: topLevelAnnotation sh2
    -- FIXME: suggest adding a 3rd kind of
    --        constraint for convenience or
    --        revisiting (:<:)

-- * Constant Typings

pmtyOf :: Con -> Ty -> InferM PmTy
pmtyOf (Bool b) ty
    = do ShBase a <- freshLinearShapeFrom ty
         return ( ShBase a
                , constr (RefBool b) a
                , S.empty              )
pmtyOf (Int n) ty
    = do ShBase a <- freshLinearShapeFrom ty
         return ( ShBase a
                , constr (RefInt (injInt n)) a
                , S.empty                      )
pmtyOf (ExnC lbl _) ty
    = do sh <- freshLinearShapeFrom ty
         let a = topLevelAnnotation sh
         return ( sh
                , S.empty
                , constr (ExnCrash lbl) a )

constr c v
    = S.singleton (C (S.singleton c) :<: v)

-- | Collect environments

collectEnvs :: Eq a => Expr (Env a, b) -> Env a
collectEnvs (Var _ (env, _))
    = env
collectEnvs (Con _ (env, _))
    = env
collectEnvs (Abs _ e (env, _))
    = mergeEnvs env [e]
collectEnvs (Fix _ e (env, _))
    = mergeEnvs env [e]
collectEnvs (App e1 e2 (env, _))
    = mergeEnvs env [e1, e2]
collectEnvs (Let _ e1 e2 (env, _))
    = mergeEnvs env [e1, e2]
collectEnvs (If _ e0 e1 e2 (env, _))
    = mergeEnvs env [e0, e1, e2]
-- Operators
collectEnvs (Op _ e1 e2 (env, _))
    = mergeEnvs env [e1, e2]
-- Pairs
collectEnvs (Pair e1 e2 (env, _))
    = mergeEnvs env [e1, e2]
collectEnvs (Fst e (env, _))
    = mergeEnvs env [e]
collectEnvs (Snd e (env, _))
    = mergeEnvs env [e]
-- Lists
collectEnvs (Nil (env, _))
    = env
collectEnvs (Cons e1 e2 (env, _))
    = mergeEnvs env [e1, e2]
collectEnvs (Case _ e0 (Just e1) (Just (_, _, e2)) (env, _))
    = mergeEnvs env [e0, e1, e2]
    
mergeEnvs :: Eq a => Env a -> [Expr (Env a,b)] -> Env a
mergeEnvs env = foldr (M.unionWith matches) env . map collectEnvs
    where matches k1 k2
            | k1 == k2  = k1
            | otherwise = error "environments do not match"
            
-- | Show "solved" types

class ShowSolved a where
    showSolved :: Show b => Solution b -> a -> String
    
instance ShowSolved Sh where
    showSolved sol (ShBase         x)
        = S.showSet (M.findWithDefault S.empty x sol)
    showSolved sol (ShFun  sh1 sh2 x)
        = "(" ++ showSolved sol sh1 ++ " -> " ++ showSolved sol sh2 ++ ")"
            ++ "^(" ++ S.showSet (M.findWithDefault S.empty x sol) ++ ")"
    -- Pairs
    showSolved sol(ShPair sh1 sh2 x)
        = "(" ++ showSolved sol sh1 ++ ", "   ++ showSolved sol sh2 ++ ")"
            ++ "^(" ++ S.showSet (M.findWithDefault S.empty x sol) ++ ")"
    -- Lists
    showSolved sol(ShList sh      x)
        = "[" ++ showSolved sol sh ++ "]"
            ++ "^(" ++ S.showSet (M.findWithDefault S.empty x sol) ++ ")"

instance ShowSolved PmTy where
    showSolved sol (sh, c1, c2)
        = showSolved sol sh ++ " with " -- ++ S.showSet c1 ++ "; " ++ S.showSet c2
            
instance ShowSolved PmScheme where
    showSolved sol (Forall q pmty)
        = "forall " {- ++ S.showSet q -} ++ ". " ++ showSolved (sol `M.restrictBySet` q) pmty
            
instance ShowSolved a => ShowSolved (Env a) where
    showSolved sol env
        = concat (M.foldrWithKey (\x t -> (:) ("\n  " ++ show x ++ " :: " ++ showSolved sol t)) [] env)
