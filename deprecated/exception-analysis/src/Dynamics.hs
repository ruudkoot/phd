{-# LANGUAGE ViewPatterns #-}

module Dynamics where

import Data.Set as S

-- | Utility

iterateUntil :: (a -> Bool) -> (a -> a) -> a -> [a]
iterateUntil p f x = takeWhile (not . p) (iterate f x)

-- | Names

type Name = String

-- | Exception labels

data ExnLbl = DivByZero | PMF deriving (Eq, Ord, Show)

-- | Environments

data Env range = E
               | Env range :> (Name, range)
               deriving Show

type ExprEnv = Env Expr

(#) :: Name -> ExprEnv -> (ExprEnv, Expr)
y # (env :> (x, e))
    | x == y    = (env, e)
    | otherwise = let (env', e) = y # env in (env :> (x, e), e)
    
-- | Operators

data OP = ADD deriving (Eq, Ord, Show)

-- | Expressions

data Expr = Var Name
          | Bool Bool
          | Int Int
          | Exn (S.Set ExnLbl)
          | Nil
          | Close Expr ExprEnv
          | Abs Name Expr
          | Fix Name Expr
          | Expr :@: Expr
          | Let Name Expr Expr
          | If Expr Expr Expr
          | Op Expr OP Expr
          | Expr :*: Expr
          | Fst Expr
          | Snd Expr
          | Expr ::: Expr
          | Case Expr Expr (Name, Name, Expr)
          | Bind ExprEnv Expr
          deriving Show

-- | Values and normal forms

isValue :: Expr -> Bool
isValue (Bool  _  ) = True
isValue (Int   _  ) = True
isValue (Exn   _  ) = True
isValue  Nil        = True
isValue (Close _ _) = True
isValue _           = False

-- | Reduction relation

reduce :: ExprEnv -> Expr -> Expr
reduce env e = reduce' e env
    where
        reduce' :: Expr -> ExprEnv -> Expr
        reduce' (Var x) ((x#) -> (env, e))
            = Bind env e
        reduce' (Fix f e) env
            = Bind (env :> (f, Bind env $ Fix f e)) e
        reduce' e@(e1 ::: e2) env
            = Close e env
        reduce' (Bind env1 e) _
            = reduce env1 e

eval  env =        until isValue (reduce env)
eval_     =        until isValue (reduce E  )
eval'     = iterateUntil isValue (reduce E  )

-- | Normal forms

isHeadNormalForm :: Expr -> Bool
isHeadNormalForm (Bool  _  ) = True
isHeadNormalForm (Int   _  ) = True
isHeadNormalForm (Exn   _  ) = True
isHeadNormalForm  Nil        = True
isHeadNormalForm (Close e _) = isHeadNormalForm e
isHeadNormalForm (Abs   x e) = True
isHeadNormalForm _           = False

isBetaNormalForm :: Expr -> Bool
isBetaNormalForm (Bool  _  ) = True
isBetaNormalForm (Int   _  ) = True
isBetaNormalForm (Exn   _  ) = True
isBetaNormalForm  Nil        = True
isBetaNormalForm (Close e _) = isHeadNormalForm e
isBetaNormalForm _           = False

evalHNF = iterateUntil isHeadNormalForm (reduce E)
evalBNF = iterateUntil isBetaNormalForm (reduce E)

-- | Testing

fullyReduceList env e
    = case eval env e of
        Close (e1 ::: e2) env1 
            -> Close (eval env1 e1 ::: fullyReduceList env1 e2) env
        _   -> e

test1 = Fix "f" (Int 1 ::: Var "f")
