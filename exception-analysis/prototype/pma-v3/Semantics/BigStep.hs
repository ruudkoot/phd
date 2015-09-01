{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TupleSections        #-}

module Semantics.BigStep where

-- ||| Launchbury-style natural semantics (call-by-need)

import Control.Applicative
import Control.Monad.State

import Data.Traversable

import qualified Data.List     as L
import qualified Data.Map      as M
import qualified Data.Set      as S
import qualified Data.Set.Util as S

import Syntax
import Ref
import Exn

-- | Normalisation

-- * Check if bound variables are distinct

boundVariablesDistinct :: Expr () -> Bool
boundVariablesDistinct = maybe False (const True) . boundVariablesDistinct'
    where boundVariablesDistinct' :: Expr () -> Maybe (S.Set Name)
          boundVariablesDistinct' (Var x ())
            = return (S.singleton x)
          boundVariablesDistinct' (Con _ ())
            = return S.empty
          boundVariablesDistinct' (Abs x e ())
            = do xs <- boundVariablesDistinct' e
                 if x `S.member` xs then
                    notDistinct
                 else
                    return (x `S.insert` xs)
          boundVariablesDistinct' (Fix f e ())
            = do xs <- boundVariablesDistinct' e
                 if f `S.member` xs then
                    notDistinct
                 else
                    return (f `S.insert` xs)
          boundVariablesDistinct' (App e1 e2 ())
            = do xs1 <- boundVariablesDistinct' e1
                 xs2 <- boundVariablesDistinct' e2
                 if xs1 `S.overlap` xs2 then
                    notDistinct
                 else
                    return (xs1 `S.union` xs2)
          boundVariablesDistinct' (Let x e1 e2 ())
            = do xs1 <- boundVariablesDistinct' e1
                 xs2 <- boundVariablesDistinct' e2
                 if x `S.member` xs1 || x `S.member` xs2 || xs1 `S.overlap` xs2 then
                    notDistinct
                 else
                    return (x `S.insert` (xs1 `S.union` xs2))
          boundVariablesDistinct' (If _ e0 e1 e2 ())
            = do xs0 <- boundVariablesDistinct' e0
                 xs1 <- boundVariablesDistinct' e1
                 xs2 <- boundVariablesDistinct' e2
                 if S.overlaps [xs0, xs1, xs2] then
                    notDistinct
                 else
                    return (xs0 `S.union` xs1 `S.union` xs2)
          -- Operators
          boundVariablesDistinct' (Op _ e1 e2 ())
            = do xs1 <- boundVariablesDistinct' e1
                 xs2 <- boundVariablesDistinct' e2
                 if xs1 `S.overlap` xs2 then
                    notDistinct
                 else
                    return (xs1 `S.union` xs1)
          -- Pairs
          boundVariablesDistinct' (Pair e1 e2 ())
            = do xs1 <- boundVariablesDistinct' e1
                 xs2 <- boundVariablesDistinct' e2
                 if xs1 `S.overlap` xs2 then
                    notDistinct
                 else
                    return (xs1 `S.union` xs1)
          boundVariablesDistinct' (Fst e ())
            = boundVariablesDistinct' e
          boundVariablesDistinct' (Snd e ())
            = boundVariablesDistinct' e
          -- Lists
          boundVariablesDistinct' (Nil ())
            = return S.empty
          boundVariablesDistinct' (Cons e1 e2 ())
            = do xs1 <- boundVariablesDistinct' e1
                 xs2 <- boundVariablesDistinct' e2
                 if xs1 `S.overlap` xs2 then
                    notDistinct
                 else
                    return (xs1 `S.union` xs2)
          boundVariablesDistinct' (Case _ e0 arm1 arm2 ())
            = do xs0 <- boundVariablesDistinct' e0
                 xs1 <- maybe (return S.empty) boundVariablesDistinct'  arm1
                 xs2 <- maybe (return S.empty) boundVariablesDistinct'' arm2
                 if S.overlaps [xs0, xs1, xs1] then
                    notDistinct
                 else
                    return (S.unions [xs0, xs1, xs2])
            where boundVariablesDistinct'' (x1, x2, e')
                    = do xs' <- boundVariablesDistinct' e'
                         if x1 == x2 || x1 `S.member` xs' || x2 `S.member` xs' then
                            notDistinct
                         else
                            return (x1 `S.insert` (x2 `S.insert` xs'))

          notDistinct = fail "bound variables not distinct"

-- * Alpha renaming

alphaRename :: Expr () -> FreshM (Expr ())
alphaRename = alphaRename' M.empty

alphaRename' :: M.Map Name Name -> Expr () -> FreshM (Expr ())
alphaRename' subst (Var x ())
    -- FIXME: general brokenness...
    = -- return $ Var (subst M.!! x)
      -- return $ Var (M.findWithDefault (error $ "variable not bound: subst = " ++ show subst ++ ", x = " ++ show x) x subst)
      return $ Var (M.findWithDefault x x subst) ()
alphaRename' _subst e@(Con _ ())
    = return e
alphaRename' subst (Abs x e ())
    = do x' <- fresh
         e' <- alphaRename' (M.insert x x' subst) e
         return (Abs x' e' ())
alphaRename' subst (Fix f e ())
    = do f' <- fresh
         e' <- alphaRename' (M.insert f f' subst) e
         return (Fix f' e' ())
alphaRename' subst (App e1 e2 ())
    = do e1' <- alphaRename' subst e1
         e2' <- alphaRename' subst e2
         return (App e1' e2' ())
alphaRename' subst (Let x e1 e2 ())
    = do x' <- fresh
         let subst' = M.insert x x' subst
         e1' <- alphaRename' subst' e1
         e2' <- alphaRename' subst' e2
         return (Let x' e1' e2' ())
alphaRename' subst (If lbl e0 e1 e2 ())
    = do e0' <- alphaRename' subst e0
         e1' <- alphaRename' subst e1
         e2' <- alphaRename' subst e2
         return (If lbl e0' e1' e2' ())
-- Operators
alphaRename' subst (Op op e1 e2 ())
    = do e1' <- alphaRename' subst e1
         e2' <- alphaRename' subst e2
         return (Op op e1' e2' ())
-- Pairs
alphaRename' subst (Pair e1 e2 ())
    = do e1' <- alphaRename' subst e1
         e2' <- alphaRename' subst e2
         return (Pair e1' e2' ())
alphaRename' subst (Fst e ())
    = do e' <- alphaRename' subst e
         return (Fst e' ())
alphaRename' subst (Snd e ())
    = do e' <- alphaRename' subst e
         return (Snd e' ())
-- Lists
alphaRename' _subst (Nil ())
    = return (Nil ())
alphaRename' subst (Cons e1 e2 ())
    = do e1' <- alphaRename' subst e1
         e2' <- alphaRename' subst e2
         return (Cons e1' e2' ())
alphaRename' subst (Case lbl e0 arm1 arm2 ())
    = do e0' <- alphaRename' subst e0
         arm1' <- traverse (alphaRename' subst) arm1
         arm2' <- traverse  alphaRename''       arm2
         return (Case lbl e0' arm1' arm2' ())
    where alphaRename'' (x, xs, e)
            = do (x', xs') <- fresh
                 let subst' = M.insert x x' (M.insert xs xs' subst)
                 e' <- alphaRename' subst' e
                 return (x', xs', e')
          
-- * Transformation into normal form

transform :: Expr () -> FreshM (Expr ())
transform x@(Var _ ())
    = return x
transform c@(Con _ ())
    = return c
transform (Abs x e ())
    = do e' <- transform e
         return (Abs x e' ())
transform (Fix f e ())
    = do e' <- transform e
         return (Let f e' (Var f ()) ())
transform (App e1 x@(Var _ ()) ())
    = do e1' <- transform e1
         return (App e1' x ())
transform (App e1 e2 ())
    = do y   <- fresh
         e1' <- transform e1
         e2' <- transform e2
         return (Let y e2' (App e1' (Var y ()) ()) ())
transform (Let x e1 e2 ())
    = do e1' <- transform e1
         e2' <- transform e2
         return (Let x e1' e2' ())
transform (If lbl e0 e1 e2 ())
    = do e0' <- transform e0
         e1' <- transform e1
         e2' <- transform e2
         return (If lbl e0' e1' e2' ())
-- Operators
transform (Op op e1 e2 ())
    = do e1' <- transform e1
         e2' <- transform e2
         return (Op op e1' e2' ())
-- Pairs
transform (Pair e1 e2 ())
    = do (y1, y2) <- fresh
         e1' <- transform e1
         e2' <- transform e2
         return (Let y1 e1' (Let y2 e2' (Pair (Var y1 ()) (Var y2 ()) ()) ()) ())
transform (Fst e ())
    = do e' <- transform e
         return (Fst e' ())
transform (Snd e ())
    = do e' <- transform e
         return (Snd e' ())
-- Lists
transform (Nil ())
    = return (Nil ())
transform (Cons e1 e2 ())
    -- FIXME: not the most optimal transformation if argument is a Var
    = do (y1, y2) <- fresh
         e1' <- transform e1
         e2' <- transform e2
         return (Let y1 e1' (Let y2 e2' (Cons (Var y1 ()) (Var y2 ()) ()) ()) ())
transform (Case lbl e0 arm1 arm2 ())
    = do e0'   <- transform e0
         arm1' <- traverse                           transform    arm1
         arm2' <- traverse (\(x,xs,e) -> (x,xs,) <$> transform e) arm2
         return (Case lbl e0' arm1' arm2' ())

-- | Reduction

type Heap = M.Map Name (Expr ())

-- * Reduce (weak head normal form)

reduce :: Int -> Heap -> Expr () -> FreshM (Heap, Expr ())
-- FIXME: move heap into the state monad?
reduce 0 heap _
    = return (heap, Con (ExnC "reduce" Diverge) ())
reduce fuel heap (Var x ())
    | Just e' <- M.lookup x heap
        = do (heap', z) <- reduce (fuel - 1) (M.delete x heap) e'
             z' <- alphaRename z
             return (M.insert x z heap', z')
    | otherwise
        = error $ "Sem.reduce: unbound variable: x = "
                  ++ show x ++ ", heap = " ++ show heap
reduce _fuel heap e@(Con _ ())
    = return (heap, e)
reduce _fuel heap e@(Abs _ _ ())
    = return (heap, e)
reduce fuel heap (App e (Var x ()) ())
    = do (heap', e') <- reduce (fuel - 1) heap e
         case e' of
            Con (ExnC lbl exn) () -> return (heap', Con (ExnC lbl exn) ())
            Abs y e''          () -> reduce (fuel - 1) heap' (substitute e'' x y)
            _ -> error $ "Sem.reduce: " ++ show e'
reduce fuel heap (Let x e1 e2 ())
    = reduce (fuel - 1) (M.insert x e1 heap) e2
reduce fuel heap (If _ e0 e1 e2 ())
    = do (heap', e0') <- reduce (fuel - 1) heap e0
         case e0' of
            Con (ExnC _ _    ) () -> return (heap', e0')
            Con (Bool   True ) () -> reduce (fuel - 1) heap' e1
            Con (Bool   False) () -> reduce (fuel - 1) heap' e2
-- Operators
reduce fuel heap (Op op e1 e2 ())
    = do (heap1, e1') <- reduce (fuel - 1) heap e1
         case e1' of 
            Con (ExnC _ _ ) () -> return (heap1, e1')
            Con (Int    n1) () -> 
                do (heap2, e2') <- reduce (fuel - 1) heap1 e2
                   case e2' of
                        Con (ExnC _ _ ) () -> return (heap2, e2')
                        Con (Int    n2) () ->
                           case op of
                                LEQ -> return (heap2, Con (Bool (n1 <= n2)) ())
                                ADD -> return (heap2, Con (Int  (n1 +  n2)) ())

-- Pairs
reduce _fuel heap e@(Pair _ _ ())
    = return (heap, e)
reduce fuel heap (Fst e ())
    = do (heap', e') <- reduce (fuel - 1) heap e
         case e' of
            Con (ExnC _ _) () -> return (heap', e')
            Pair e1 _e2    () -> reduce (fuel - 1) heap' e1
reduce fuel heap (Snd e ())
    = do (heap', e') <- reduce (fuel - 1) heap e
         case e' of
            Con (ExnC _ _) () -> return (heap', e')
            Pair _e1 e2    () -> reduce (fuel - 1) heap' e2
-- Lists
reduce _fuel heap e@(Nil ())
    = return (heap, e)
reduce _fuel heap e@(Cons _ _ ())
    = return (heap, e)
reduce fuel heap (Case lbl e0 arm1 arm2 ())
    = do (heap', e0') <- reduce (fuel - 1) heap e0
         case e0' of
            Con (ExnC _ _) () -> return (heap', e0')
            Nil () ->
                do case arm1 of
                        Nothing -> return (heap, Con (ExnC lbl PatternMatchFail) ())
                        Just e1 -> reduce (fuel - 1) heap' e1
            Cons (Var a ()) (Var as ()) () ->
                do case arm2 of
                        Nothing -> return (heap', Con (ExnC lbl PatternMatchFail) ())
                        Just (x, xs, e2) -> reduce (fuel - 1) heap'
                                                   (substitute (substitute e2 a x) as xs)

-- * Reduce (under constructors, not under abstractions)

reduceFurther :: Int -> Heap -> Expr () -> FreshM (Heap, Expr ())
reduceFurther fuel heap e =
    do (heap', e') <- reduce (fuel - 1) heap e
       case e' of
            Pair (Var x1 ()) (Var x2 ()) () ->
                do (heap1, e1') <- reduceFurther (fuel - 1) heap' (heap' M.! x1)
                   (heap2, e2') <- reduceFurther (fuel - 1) heap1 (heap1 M.! x2)
                   return (heap2, Pair e1' e2' ())
            Pair _ _ () -> error $ "Sem.reduceFurther: e' = " ++ show e'
            Cons (Var x1 ()) (Var x2 ()) () ->
                do (heap1, e1') <- reduceFurther (fuel - 1) heap' (heap' M.! x1)
                   (heap2, e2') <- reduceFurther (fuel - 1) heap1 (heap1 M.! x2)
                   return (heap2, Cons e1' e2' ())
            Cons _ _ () -> error $ "Sem.reduceFurther: e' = " ++ show e'
            _ -> return (heap', e')

-- * Substitution

substitute :: Expr () -> Name -> Name -> Expr ()
substitute e@(Var z ()) x y
    | z == y    = Var x ()
    | otherwise = e
substitute e@(Con _ ()) _ _
    = e
substitute (Abs z e ()) x y
    | z == y    = error "shadowing unexpected"
    | otherwise = Abs z (substitute e x y) ()
substitute (Fix f e ()) x y
    | f == y    = error "shadowing unexpected"
    | otherwise = Fix f (substitute e x y) ()
substitute (App e1 e2 ()) x y
    = App (substitute e1 x y) (substitute e2 x y) ()
substitute (Let z e1 e2 ()) x y
    | z == y     = error "shadowing unexpected"
    | otherwise  = Let z (substitute e1 x y) (substitute e2 x y) ()
substitute (If lbl e0 e1 e2 ()) x y
    = If lbl (substitute e0 x y) (substitute e1 x y) (substitute e2 x y) ()
-- Operators
substitute (Op op e1 e2 ()) x y
    = Op op (substitute e1 x y) (substitute e2 x y) ()
-- Pairs
substitute (Pair e1 e2 ()) x y
    = Pair (substitute e1 x y) (substitute e2 x y) ()
substitute (Fst e ()) x y
    = Fst (substitute e x y) ()
substitute (Snd e ()) x y
    = Snd (substitute e x y) ()
-- Lists
substitute (Nil ()) _ _
    = Nil ()
substitute (Cons e1 e2 ()) x y
    = Cons (substitute e1 x y) (substitute e2 x y) ()
substitute (Case lbl e0 arm1 arm2 ()) x y
    = Case lbl
           (substitute e0 x y)
           (fmap (\e1 -> substitute e1 x y) arm1)
           (fmap (\(z,zs,e2) -> if z == y || zs == y
                                then error "shadowing unexpected"
                                else (z,zs,substitute e2 x y)     ) arm2)
           ()

-- | Postprocessing of the reduced expression

postProcessEval1 :: Expr () -> (S.Set Ref, S.Set Exn)
postProcessEval1 (Con (ExnC lbl Crash) ())
    = (S.empty, S.singleton (ExnCrash lbl))
postProcessEval1 (Con (ExnC _lbl Diverge) ())
    = (S.empty, S.empty)
postProcessEval1 (Con (ExnC lbl PatternMatchFail) ())
    = (S.empty, S.singleton (ExnCrash lbl)) -- FIXME: add separate exception
postProcessEval1 (Con (Bool b) ())
    = (S.singleton (RefBool b), S.empty)
postProcessEval1 (Con (Int n) ())
    = (S.singleton (RefInt (injInt n)), S.empty)
postProcessEval1 (Abs _ _ ())
    = (S.empty, S.empty)
-- Pairs
postProcessEval1 (Pair _ _ ())
    = (S.empty, S.empty)
-- Lists
postProcessEval1 (Nil ())
    = (S.singleton (RefList E), S.empty)
postProcessEval1 (Cons _ _ ())
    = (S.singleton (RefList NE), S.empty)
postProcessEval1 x
    = error $ "postProcessEval1: " ++ show x

-- * Dataflow and exceptions (further) of the evaluation result
--   Evaluates under constructors (not abstractions)

postProcessEval2 :: Expr () -> (S.Set Ref, S.Set Exn)
postProcessEval2 (Con (ExnC lbl Crash) ())
    = (S.empty, S.singleton (ExnCrash lbl))
postProcessEval2 (Con (ExnC _lbl Diverge) ())
    = (S.empty, S.empty)
postProcessEval2 (Con (ExnC lbl PatternMatchFail) ())
    = (S.empty, S.singleton (ExnCrash lbl)) -- FIXME: add separate exception
postProcessEval2 (Con (Bool b) ())
    = (S.singleton (RefBool b), S.empty)
postProcessEval2 (Con (Int  n) ())
    = (S.singleton (RefInt (injInt n)), S.empty)
postProcessEval2 (Abs _ _ ())
    = (S.empty, S.empty)
-- Pairs
postProcessEval2 (Pair e1 e2 ())
    = let (_, exn1) = postProcessEval2 e1
          (_, exn2) = postProcessEval2 e2
       in (S.empty, exn1 `S.union` exn2)
-- Lists
postProcessEval2 (Nil ())
    = (S.singleton (RefList E), S.empty)
postProcessEval2 (Cons e1 e2 ())
    = let (_, exn1) = postProcessEval2 e1
          (_, exn2) = postProcessEval2 e2
       in (S.singleton (RefList NE), exn1 `S.union` exn2)
postProcessEval2 x
    = error $ "postProcessEval2: " ++ show x

-- | Fresh names

type FreshM r = State [Name] r

class Fresh a where
    fresh :: FreshM a
    
instance (Fresh a, Fresh b) => Fresh (a, b) where
    fresh = do x <- fresh
               y <- fresh
               return (x, y)

instance Fresh Name where
    fresh = do (x:xs) <- get
               put xs
               return x
{- FIXME: DISABLED
-- | Pretty printing

instance LaTeX Heap where
    latex heap | M.null heap = "\\epsilon "
               | otherwise   = ("\\left[\\begin{split}"++) . (++"\\end{split}\\right]") . L.intercalate newline . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v) . M.toList $ heap
               
-}
