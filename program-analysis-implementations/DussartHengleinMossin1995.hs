{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module DussartHengleinMossin1995 where

-- TODO: more type classes (unify, isMonomorphic)
-- TODO: more parameterized types (Constr)
-- TODO: use light-weight generic programming (isMonomorphic, subst)
-- TODO: substitution monad
-- TODO: make unification and inference a Maybe

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

import qualified Debug.Trace as Debug

-- | Examples

test example
    = let (s1, t1, e1') = evalInferM (wTy M.empty example)
       in evalInferM (wBt M.empty e1')

-- * Henglein & Mossin: Ackermann

exAck = Fix a (Lam i (Lam j (If (COp (Var i) EQL (Con $ Int 0))
                                (AOp (Var j) ADD (Con $ Int 1))
                                (If (COp (Var j) EQL (Con $ Int 0))
                                    (App (App (Var a)
                                              (AOp (Var i) SUB (Con $ Int 1))
                                         )
                                         (Con $ Int 1)
                                    )
                                    (App (App (Var a)
                                              (AOp (Var i) SUB (Con $ Int 1))
                                         )
                                         (App (App (Var a) (Var i))
                                              (AOp (Var j) SUB (Con $ Int 1))
                                         )
                                    )
                                )
        )))
    where a = -1
          i = -2
          j = -3

-- * Dussart, Henglein & Mossin

ex2 = Fix f (Lam x (Lam y (If (COp (Var x) EQL (Con $ Int 0))
                              (Con $ Int 2)
                              ((Var f `App` Var y) `App` (AOp (Var x) SUB (Con $ Int 1)))
      )))
    where f = -1
          x = -2
          y = -3
          
ks2 = (S.fromList [BtVar 6 :<: BtVar 8,BtVar 6 :<: BtVar 14,BtVar 7 :<: BtVar 9,BtVar 8 :<: BtVar 15,BtVar 11 :<: BtVar 15,BtVar 14 :<: BtVar 10],BtFun (Bt (BtVar 6)) (BtCon S) (BtFun (Bt (BtVar 7)) (BtCon S) (Bt (BtVar 15))))

(c2, k2) = ks2

-- | Syntax

type Name = Int

-- * Untyped expressions

data Expr
    = Var Name
    | Lam Name Expr
    | App Expr Expr
    | Con Con
    | If  Expr Expr Expr
    | Fix Name Expr
    | Let Name Expr Expr
    | AOp Expr AOp  Expr
    | COp Expr COp  Expr
    deriving (Eq, Ord, Show)
    
data Con
    = Bool Bool
    | Int  Int
    deriving (Eq, Ord, Show)
    
data AOp = ADD | SUB
    deriving (Eq, Ord, Show)

data COp = EQL
    deriving (Eq, Ord, Show)

-- * Type-annotated expressions

data Expr'
    = Var' Name  Ty
    | Lam' Name  Ty Expr'       Ty
    | App' Expr'    Expr'       Ty
    | Con' Con   Ty
    | If'  Expr'    Expr' Expr' Ty
    | Fix' Name  Ty Expr'       Ty
    | Let' Name  Ty Expr' Expr' Ty
    | AOp' Expr'    AOp   Expr' Ty
    | COp' Expr'    COp   Expr' Ty
    deriving (Eq, Ord, Show)

-- | Static semantics

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

-- * Binding-time annotation

data Bt
    = BtVar Name
    | BtCon BtCon
    | BtLub Bt Bt       -- Least upper bound
    deriving (Eq, Ord)
    
instance Show Bt where
    show (BtVar d)     = "?" ++ show d
    show (BtCon c)     = show c
    show (BtLub b1 b2) = show b1 ++ " ∨ " ++ show b2

data BtCon
    = S     -- Static
    | D     -- Dynamic
    deriving (Eq, Ord, Show)    

-- * Binding-time assumptions

type Constr = S.Set Constr'

data Constr'
    = Bt :<: Bt
    deriving (Eq, Ord, Show)

-- * Binding-time types

data BtTy
    = Bt Bt
    | BtFun BtTy Bt BtTy
    deriving (Eq, Ord, Show)

-- * Qualified binding-time types

data BtScheme = Forall (S.Set Name) Constr BtTy
    deriving Show

-- * Type environment

type TyEnv = M.Map Name Ty
type BtEnv = M.Map Name BtScheme

-- * Substitutions

infixr 0 $@
infixr 9 $.

type Subst a = M.Map Name a

idSubst :: Subst a
idSubst = M.empty

($.) :: Substitute a a => Subst a -> Subst a -> Subst a
subst2 $. subst1 = (subst2 $$ subst1) $+ subst2
    where ($$), ($+) :: Substitute a a => Subst a -> Subst a -> Subst a
          subst1 $$ subst2
            = M.map (subst1 $@) subst2
          subst1 $+ subst2
            = M.unionWith (error "overlapping substitutions") subst1 subst2

class Substitute a t where
    ($@) :: Subst a -> t -> t
    
instance Substitute Ty Ty where
    subst $@ t@(TyVar a) = M.findWithDefault t a subst
    subst $@ t@(TyCon _) = t
    subst $@ TyFun t1 t2 = TyFun (subst $@ t1) (subst $@ t2)

instance Substitute Ty TyEnv where
    subst $@ env = M.map (subst $@) env
    
instance Substitute Ty Expr' where
    subst $@ (Var' x t)
        = Var' x (subst $@ t)
    subst $@ (Lam' x t1 e t2)   
        = Lam' x (subst $@ t1) (subst $@ e) (subst $@ t2)
    subst $@ (App' e1 e2 t)
        = App' (subst $@ e1) (subst $@ e2) (subst $@ t)
    subst $@ (Con' c t)
        = Con' c (subst $@ t)
    subst $@ (If' e0 e1 e2 t)
        = If' (subst $@ e0) (subst $@ e1) (subst $@ e2) (subst $@ t)
    subst $@ (Fix' f t1 e t2)
        = Fix' f (subst $@ t1) (subst $@ e) (subst $@ t2)
    subst $@ (Let' x t1 e1 e2 t2)
        = Let' x (subst $@ t1) (subst $@ e1) (subst $@ e2) (subst $@ t2)
    subst $@ (AOp' e1 op e2 t)
        = AOp' (subst $@ e1) op (subst $@ e2) (subst $@ t)
    subst $@ (COp' e1 op e2 t)
        = COp' (subst $@ e1) op (subst $@ e2) (subst $@ t)

instance Substitute Bt Bt where
    subst $@ b@(BtVar d) = M.findWithDefault b d subst
    subst $@ b@(BtCon _) = b
    subst $@ BtLub b1 b2 = BtLub (subst $@ b1) (subst $@ b2)
    
instance Substitute Bt BtTy where
    subst $@ Bt b          = Bt (subst $@ b)
    subst $@ BtFun k1 b k2 = BtFun (subst $@ k1) (subst $@ b) (subst $@ k2)

instance Substitute Bt Constr' where
    subst $@ (b1 :<: b2) = (subst $@ b1) :<: (subst $@ b2)

instance Substitute Bt Constr where
    subst $@ c = S.map (subst $@) c

instance Substitute Bt BtScheme where
    subst $@ Forall q c k
        = let subst' = subst `M.restrictBySet` q
           in Forall q (subst' $@ c) (subst' $@ k)

instance Substitute Bt BtEnv where
    subst $@ env = M.map (subst $@) env
    
instance Substitute Name Name where
    subst $@ name = M.findWithDefault name name subst

instance Substitute Name (S.Set Name) where
    subst $@ names = S.map (subst $@) names

instance Substitute Name Bt where
    subst $@   (BtVar d)     = BtVar (subst $@ d)
    subst $@ b@(BtCon _)     = b
    subst $@   (BtLub b1 b2) = BtLub (subst $@ b1) (subst $@ b2)

instance Substitute Name BtTy where
    subst $@ (Bt b)          = Bt (subst $@ b)
    subst $@ (BtFun k1 b k2) = BtFun (subst $@ k1) b (subst $@ k2)

instance Substitute Name Constr' where
    subst $@ (b1 :<: b2) = (subst $@ b1) :<: (subst $@ b2)
    
instance Substitute Name Constr where
    subst $@ c = S.map (subst $@) c

-- | Inference algorithm

-- * Inference monad

type InferM a = State [Name] a

evalInferM :: State [Name] a -> a
evalInferM m = evalState m [1..]

-- * Type inference (monomorphic)

wTy :: TyEnv -> Expr -> InferM (Subst Ty, Ty, Expr')
wTy env (Var x)
    = do let t = env M.! x
         return (idSubst, t, Var' x t)
wTy env (Lam x e)
    = do a <- fresh
         let env' = M.insert x a env
         (s1, t1, e') <- wTy env' e
         let t' = TyFun (s1 $@ a) t1
         return (s1, t', Lam' x (s1 $@ a) (s1 $@ e') t')
wTy env (App e1 e2)
    = do (s1, t1, e1') <- wTy        env  e1
         (s2, t2, e2') <- wTy (s1 $@ env) e2
         a <- fresh
         let s3 = unifyTy (s2 $@ t1) (TyFun t2 a)
         let t' = s3 $@ a
         return (s3 $. s2 $. s1, t', App' (s3 $. s2 $@ e1') (s3 $@ e2') t')
wTy env (Con c)
    = do let t = typeOf c
         return (idSubst, t, Con' c t)
wTy env (If e0 e1 e2)
    = do (s0, t0, e0') <- wTy              env  e0
         (s1, t1, e1') <- wTy (      s0 $@ env) e1
         (s2, t2, e2') <- wTy (s1 $. s0 $@ env) e2
         let s3 = unifyTy (s2 $. s1 $@ t0) (TyCon TyBool)
         let s4 = unifyTy (s3 $. s2 $@ t1) (s3 $@ t2)
         let t' = s4 $. s3 $@ t2
         return (s4 $. s3 $. s2 $. s1 $. s0, t', If' e0' e1' e2' t')
wTy env (Fix f e)
    = do a <- fresh
         let env' = M.insert f a env
         (s1, t1, e') <- wTy env' e
         let s2 = unifyTy t1 (s1 $@ a)
         let t' = s2 $@ t1
         return (s2 $. s1, t', Fix' f (s2 $@ s1 $@ a) (s2 $@ e') t')
wTy env (Let x e1 e2)
    = do (s1, t1, e1') <- wTy env e1
         let env' = M.insert x t1 (s1 $@ env)
         (s2, t2, e2') <- wTy env' e2 
         return (s2 $. s1, t2, Let' x (s2 $@ t1) (s2 $@ e1') e2' t2)
wTy env (AOp e1 op e2)
    = do (s1, t1, e1') <- wTy env         e1
         (s2, t2, e2') <- wTy (s1 $@ env) e2
         let s3 = unifyTy (s2 $@ t1) (TyCon TyInt)
         let s4 = unifyTy (s3 $@ t2) (TyCon TyInt)
         let t' = TyCon TyInt
         return (s4 $. s3 $. s2 $. s1, t', AOp' e1' op e2' t')
wTy env (COp e1 op e2)
    = do (s1, t1, e1') <- wTy env        e1
         (s2, t2, e2') <- wTy (s1 $@ env) e2
         let s3 = unifyTy (s2 $@ t1) (TyCon TyInt)
         let s4 = unifyTy (s3 $@ t2) (TyCon TyInt)
         let t' = TyCon TyBool
         return (s4 $. s3 $. s2 $. s1, t', COp' e1' op e2' t')

-- * Constant typing

typeOf :: Con -> Ty
typeOf (Bool _) = TyCon TyBool
typeOf (Int  _) = TyCon TyInt

-- * Unification

unifyTy :: Ty -> Ty -> Subst Ty
unifyTy (TyVar a1) t2@(TyVar a2)
    | a1 == a2  = idSubst
    | otherwise = M.singleton a1 t2
unifyTy (TyVar a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = M.singleton a t
unifyTy t (TyVar a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = M.singleton a t
unifyTy (TyCon c1) (TyCon c2)
    | c1 == c2 = idSubst
    | otherwise = error "constructor clash"
unifyTy (TyFun t1 t2) (TyFun t1' t2')
    = let s1 = unifyTy        t1         t1'
          s2 = unifyTy (s1 $@ t2) (s1 $@ t2')
       in s2 $. s1
unifyTy _ _
    = error "constructor clash"

-- * Binding-time inference (polymorphic)

wBt :: BtEnv -> Expr' -> InferM (Constr, BtTy)
wBt env (Var' x t)
    = do let bs = env M.! x
         (c, k) <- inst bs
         return (c, k)
wBt env (Lam' x t1 e' t2)
    = do k <- newLinearBt t1
         (c, k') <- wBt (M.insert x (btScheme k) env) e'
         return ( c `S.union` constraintsWft k
                , BtFun k (BtCon S) k'         )
wBt env e@(App' e' e'' t)
    = do (c' , BtFun k b k') <- wBt env e'
         (c'', k''         ) <- wBt env e''
         return ( c' `S.union` c'' `S.union` constraintsS k'' k
                , k'                                            )
wBt env (Con' _ _)
    = return (S.empty, Bt $ BtCon S)
wBt env (If' e' e'' e''' t)
    = do (c'  , Bt b) <- wBt env e'
         (c'' , k'' ) <- wBt env e''
         (c''', k''') <- wBt env e'''
         k <- newLinearBt t
         return ( c' `S.union` c'' `S.union` c'''
                    `S.union` constraintsWft k
                    `S.union` constraintsS   k''  k
                    `S.union` constraintsS   k''' k
                    `S.union` constraintsF   b    k
                , k                                  )
wBt env (Let' x t1 e' e'' t2)
    = do (c', k') <- wBt env e'
         let bs = close env c' k'
         let env' = M.insert x bs env
         (c'', k'') <- wBt env' e''
         return (c'', k'')
wBt env (Fix' f t1 e' t2)
    = do let kleeneMycroft envI ksI = do
                w@(cJ, kJ) <- wBt envI e'
                let cJ' = elim (fbv envI `S.union` fbv kJ) cJ envI kJ
                let ksJ = close envI cJ' kJ
                if ksJ `genericInstanceOf` ksI
                    then return (cJ', kJ)
                    else let envJ = M.insert f ksJ envI
                          in kleeneMycroft envJ ksJ
         ks0 <- least t1
         let env0 = M.insert f ks0 env
         polyResult@(cP, kP) <- kleeneMycroft env0 ks0
         --- try some monomorphic things...
         kP <- newLinearBt t1
         let envQ = M.insert f (btScheme kP) env
         (cQ, kQ) <- wBt envQ e'
         let sR = unifyBtTy kP kQ
         let kR = sR $@ kQ
         let cR = sR $@ (cP `S.union` cQ)
         let cR' = elim (fbv envQ `S.union` fbv kR) cR envQ kR
         let monoResult = (cR', kR)
         ---
         return (error $ show monoResult)
         --return polyResult
wBt env (AOp' e1 _op e2 t)
    = do (c1, Bt b1) <- wBt env e1
         (c2, Bt b2) <- wBt env e2
         k <- fresh
         return ( c1 `S.union` c2
                    `S.union` constraintsF b1 k `S.union` constraintsF b2 k
                , k                                                         )
wBt env (COp' e1 _op e2 t)
    = do (c1, Bt b1) <- wBt env e1
         (c2, Bt b2) <- wBt env e2
         k <- fresh
         return ( c1 `S.union` c2
                    `S.union` constraintsF b1 k `S.union` constraintsF b2 k
                , k                                                         )

btScheme :: BtTy -> BtScheme
btScheme = Forall S.empty S.empty

genericInstanceOf :: BtScheme -> BtScheme -> Bool
genericInstanceOf (Forall q1 c1 k1) (Forall q2 c2 k2)
    = let subst = unifyBtTy k1 k2
       in (subst $@ q1) == (subst $@ q2) && (subst $@ c1) == (subst $@ c2)

unifyBtTy :: BtTy -> BtTy -> Subst Name
unifyBtTy (Bt (BtVar d1)) (Bt (BtVar d2))
    | d1 == d2  = idSubst
    | otherwise = M.singleton d1 d2
unifyBtTy (BtFun b1 _ b2) (BtFun b1' _ b2')
    = let s1 = unifyBtTy        b1         b1'
          s2 = unifyBtTy (s1 $@ b2) (s1 $@ b2')
       in s2 $. s1

least :: Ty -> InferM BtScheme
least t = do (q, k) <- least' t
             return (Forall q S.empty k)
  where
    least' :: Ty -> InferM (S.Set Name, BtTy)
    least' (TyVar _)
        = error "monomorphic type expected"
    least' (TyCon c)
        = do d <- fresh
             return (S.singleton d, Bt (BtVar d))
    least' (TyFun t1 t2)
        = do (q1, k1) <- least' t1
             (q2, k2) <- least' t2
             d <- fresh
             return ( q1 `S.union` q2 `S.union` S.singleton d
                    , BtFun k1 (BtVar d) k2                   )

elim :: S.Set Name -> Constr -> BtEnv -> BtTy -> Constr
elim v c env' k
    = S.foldr f c (fbv c)
        where negativeOccurences =
                nbv (M.foldr (\(Forall _ _ k') -> BtFun k' (BtCon S)) k env')
              f b c = if b `S.notMember` (negativeOccurences `S.union` v)
                      then g (BtVar b) c
                      else c
              g b c = let (r, l, n) = trisect b c
                          r' = S.map (\(b' :<: _) -> b') r
                          l' = S.unionMap (\(_ :<: b') -> S.map (\r -> r :<: b') r') l
                       in l' `S.union` n
              trisect b c = S.foldr h (S.empty, S.empty, S.empty) c
                where h c@(b1 :<: b2) (r, l, n)
                        | b2 == b   = (c `S.insert` r, l, n)
                        | b1 == b   = (r, c `S.insert` l, n)
                        | otherwise = (r, l, c `S.insert` n)

data Polarity = Pos | Neg

inv :: Polarity -> Polarity
inv Pos = Neg
inv Neg = Pos

nbv :: BtTy -> S.Set Name
nbv = nbv' Pos
    where nbv' :: Polarity -> BtTy -> S.Set Name
          nbv' Pos (Bt _)          = S.empty
          nbv' Neg (Bt b)          = fbv b
          nbv' pol (BtFun b1 _ b2) = nbv' (inv pol) b1 `S.union` nbv' pol b2

-- * Linear

newLinearBt :: Ty -> InferM BtTy
newLinearBt (TyVar _)
    = fresh
newLinearBt (TyCon _)
    = fresh
newLinearBt (TyFun t1 t2)
    = do k1 <- newLinearBt t1
         b <- fresh
         k2 <- newLinearBt t2
         return (BtFun k1 b k2)

-- * Instantiation

inst :: BtScheme -> InferM (Constr, BtTy)
inst (Forall q c k)
    = do b <- replicateM (S.size q) (fresh >>= return . BtVar)
         let subst = M.fromList (zip (S.toList q) b)
         return (subst $@ c, subst $@ k)

-- * Generalization

close :: BtEnv -> Constr -> BtTy -> BtScheme
close env c k
    = let q = (fbv c `S.union` fbv k) `S.difference` fbv env
       in Forall q c k

-- * Well-formedness

constraintsWft :: BtTy -> Constr
constraintsWft (Bt _)
    = S.empty
constraintsWft (BtFun k b k')
    = S.unions [ constraintsWft k, constraintsWft k'
               , constraintsF b k, constraintsF b k' ]

constraintsF :: Bt -> BtTy -> Constr
constraintsF b (Bt b')
    = constraintsA b b'
constraintsF b (BtFun k b' k')
    = constraintsA b b'
    
constraintsS :: BtTy -> BtTy -> Constr
constraintsS (Bt b) (Bt b')
    = constraintsA b b'
constraintsS (BtFun k1 b k2) (BtFun k1' b' k2')
    = S.unions [constraintsS k1' k1, constraintsS k2 k2', constraintsA b b']

constraintsA :: Bt -> Bt -> Constr
constraintsA (BtCon S) _
    = S.empty
constraintsA _ (BtCon D)
    = S.empty
constraintsA b b' | b == b'
    = S.empty
constraintsA b (BtLub b' _) | b == b'
    = S.empty
constraintsA b (BtLub _ b') | b == b'
    = S.empty
constraintsA (BtLub b b') b''
    = constraintsA b b'' `S.union` constraintsA b' b''
constraintsA (BtVar b) (BtVar b')
    = S.singleton (BtVar b :<: BtVar b')
{- FIXME: We have not implemented the rule for transitivity. The interpretation
          should likely be that we can always remove/do not need to add a
          constraints if it is already transitively entailed by the other
          constraints; but elim effectively handles those cases by removing them
          from the constraint set.
-}

-- | Free variables

class FTV t where
    ftv :: t -> S.Set Name
    
instance FTV Ty where
    ftv (TyVar a)     = S.singleton a
    ftv (TyCon _)     = S.empty
    ftv (TyFun t1 t2) = ftv t1 `S.union` ftv t2

class FBV t where
    fbv :: t -> S.Set Name

instance FBV Bt where
    fbv (BtVar d)     = S.singleton d
    fbv (BtCon _)     = S.empty
    fbv (BtLub b1 b2) = fbv b1 `S.union` fbv b2

instance FBV Constr' where
    fbv (b1 :<: b2) = fbv b1 `S.union` fbv b2
    
instance FBV Constr where
    fbv c = S.unionMap fbv c

instance FBV BtTy where
    fbv (Bt b) = fbv b
    fbv (BtFun k1 b k2) = fbv k1 `S.union` fbv b `S.union` fbv k2

instance FBV BtScheme where
    fbv (Forall q c k) = (fbv c `S.union` fbv k) `S.difference` q

instance FBV BtEnv where
    fbv env = M.unionMap fbv env
    
-- | Fresh variables

class Fresh t where
    fresh :: InferM t
    
instance (Fresh a, Fresh b, Fresh c) => Fresh (a, b, c) where
    fresh = do a <- fresh
               b <- fresh
               c <- fresh
               return (a, b, c)

instance Fresh Name where
    fresh = do (x:xs) <- get
               put xs
               return x
               
instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar a)

instance Fresh Bt where
    fresh = do b <- fresh
               return (BtVar b)

instance Fresh BtTy where
    fresh = do b <- fresh
               return (Bt b)
