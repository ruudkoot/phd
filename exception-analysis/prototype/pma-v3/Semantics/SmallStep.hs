module Semantics.SmallStep where

-- ||| Stuctured operational semantics with environment
-- !!! Currenly call-by-value instead of name/need

import qualified Data.Map as M

import Syntax
import Ref
import Exn

-- | Values

isValue :: Expr a -> Bool
isValue (Con _ _)
    = True
isValue (Nil _)
    = True
isValue (Close _ _)
    = True
isValue _
    = False

-- | Environment

newtype Env = Env (M.Map Name (Expr Env)) deriving Show
    -- for CBV we assume that the values are values (no pun intended)

-- | One-step reduction relation

reduce :: Env -> Expr Env -> Expr Env
-- Var
reduce (Env env) (Var x _)
    = env M.! x
-- Abs
reduce env e@(Abs _ _ _)
    = Close e env 
-- Fix
reduce env e@(Fix _ _ _)
    = Close e env
-- App
reduce env (App e1 e2 z) | not (isValue e1)
    = let e1' = reduce env e1
       in App e1' e2 z
reduce env (App (Close (Abs x e1 _) (Env env1)) e2 _)
    = Bind (Env (M.insert x e2 env1)) e1
reduce env (App (Close e@(Fix f e1 z) (Env env1)) e2 _)
    = Bind (Env (M.insert f (Close e (Env env1)) env1)) e1
-- Let
reduce (Env env) (Let x e1 e2 _)
    = Bind (Env (M.insert x e1 env)) e2
-- If
reduce env (If l e1 e2 e3 z) | not (isValue e1)
    = let e1' = reduce env e1
       in If l e1' e2 e3 z
reduce env (If _l (Con (Bool True) _) e2 e3 _)
    = e2
reduce env (If _l (Con (Bool False) _) e2 e3 _)
    = e3
-- Op
reduce env (Op op e1 e2 z) | not (isValue e1)
    = let e1' = reduce env e1
       in Op op e1' e2 z
reduce env (Op op v1 e2 z) | not (isValue e2)
    = let e2' = reduce env e2
       in Op op v1 e2' z
reduce env (Op ADD v1@(Con (Int n1) _) v2@(Con (Int n2) _) z) | isValue v1 && isValue v2
    = Con (Int (n1 + n2)) z
reduce env (Op LEQ v1@(Con (Int n1) _) v2@(Con (Int n2) _) z) | isValue v1 && isValue v2
    = Con (Bool (n1 <= n2)) z
-- Pair
reduce env e@(Pair _ _ _)
    = Close e env
-- Fst
reduce env (Fst e z) | not (isValue e)
    = let e' = reduce env e
       in Fst e z
reduce env (Fst (Close (Pair e1 e2 _) env1) _)
    = Bind env1 e1
-- Snd
reduce env (Snd e z) | not (isValue e)
    = let e' = reduce env e
       in Snd e z
reduce env (Snd (Close (Pair e1 e2 _) env1) _)
    = Bind env1 e2
-- Cons
reduce env e@(Cons _ _ _)
    = Close e env
-- Case
reduce env (Case l e arm1 arm2 z) | not (isValue e)
    = let e' = reduce env e
       in Case l e' arm1 arm2 z
reduce env (Case l (Nil _) (Just e2) arm2 _)
    = e2
reduce (Env env) (Case l (Cons e1 e2 _) arm1 (Just (x1,x2,e3)) _)
    = Bind (Env (M.insert x1 e1 (M.insert x2 e2 env))) e3
-- Bind
reduce env (Bind env1 e1) | not (isValue e1)
    = let e1' = reduce env1 e1
       in Bind env1 e1'
reduce env (Bind env1 v1) | isValue v1
    = v1
-- <stuck> (including Con, Pair, Nil, Cons and Close)
reduce (Env env) e
    = error $ "stuck: e = " ++ show (eraseExpr e) ++ ", env = " ++ show (M.map eraseExpr env)

-- | Many-step reduction relation

emptyEnv = Env M.empty

eval :: Expr Env -> Expr Env {- isValue -}
eval = until isValue (reduce emptyEnv)

-- | Helper functions

noEnv = error "stop looking at me!"

castExpr :: Expr () -> Expr Env
castExpr (Var x ())
    = Var x noEnv
castExpr (Con c ())
    = Con c noEnv
castExpr (Abs x e ())
    = Abs x (castExpr e) noEnv
castExpr (Fix f e ())
    = Fix f (castExpr e) noEnv
castExpr (App e1 e2 ())
    = App (castExpr e1) (castExpr e2) noEnv
castExpr (Let x e1 e2 ())
    = Let x (castExpr e1) (castExpr e2) noEnv
castExpr (If l e1 e2 e3 ())
    = If l (castExpr e1) (castExpr e2) (castExpr e3) noEnv
castExpr (Op op e1 e2 ())
    = Op op (castExpr e1) (castExpr e2) noEnv
castExpr (Pair e1 e2 ())
    = Pair (castExpr e1) (castExpr e2) noEnv
castExpr (Fst e ())
    = Fst (castExpr e) noEnv
castExpr (Snd e ())
    = Snd (castExpr e) noEnv
castExpr (Nil ())
    = Nil noEnv
castExpr (Cons e1 e2 ())
    = Cons (castExpr e1) (castExpr e2) noEnv
castExpr (Case l e arm1 arm2 ())
    = Case l (castExpr e) (fmap castExpr arm1) (fmap (\(x1,x2,e2) -> (x1,x2,castExpr e2)) arm2) noEnv
castExpr (Bind _ _)
    = error "you don't belong!"
castExpr (Close _ _)
    = error "you dont' belong!"
    
eraseExpr :: Expr a -> Expr ()
eraseExpr (Var x _)
    = Var x ()
eraseExpr (Con c _)
    = Con c ()
eraseExpr (Abs x e _)
    = Abs x (eraseExpr e) ()
eraseExpr (Fix f e _)
    = Fix f (eraseExpr e) ()
eraseExpr (App e1 e2 _)
    = App (eraseExpr e1) (eraseExpr e2) ()
eraseExpr (Let x e1 e2 _)
    = Let x (eraseExpr e1) (eraseExpr e2) ()
eraseExpr (If l e1 e2 e3 _)
    = If l (eraseExpr e1) (eraseExpr e2) (eraseExpr e3) ()
eraseExpr (Op op e1 e2 _)
    = Op op (eraseExpr e1) (eraseExpr e2) ()
eraseExpr (Pair e1 e2 _)
    = Pair (eraseExpr e1) (eraseExpr e2) ()
eraseExpr (Fst e _)
    = Fst (eraseExpr e) ()
eraseExpr (Snd e _)
    = Snd (eraseExpr e) ()
eraseExpr (Nil _)
    = Nil ()
eraseExpr (Cons e1 e2 _)
    = Cons (eraseExpr e1) (eraseExpr e2) ()
eraseExpr (Case l e arm1 arm2 _)
    = Case l (eraseExpr e) (fmap eraseExpr arm1) (fmap (\(x1,x2,e3) -> (x1,x2,eraseExpr e3)) arm2) ()
eraseExpr  (Bind env e)
    = Bind () (eraseExpr e)
eraseExpr (Close e env)
    = Close (eraseExpr e) ()
