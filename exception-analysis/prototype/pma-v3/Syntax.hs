{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Syntax
    ( Name()
    , augment
    , freshIdents
    , Lbl
    , Expr(..)
    -- , topLevelAnn
    , Con(..)
    , ExnC(..)
    , Op(..)
    )
where

import Names
import Subst

-- | Labels

type Lbl = String   -- primarily used for debugging, but we will eventually
                    -- need something like this for error reporting
                    
-- | (Annotated) Expressions

data Expr ann
    = Var  Name                                  ann
    | Con  Con                                   ann
    | Abs  Name (Expr ann)                       ann
    | Fix  Name (Expr ann)                       ann
    | App       (Expr ann) (Expr ann)            ann
    | Let  Name (Expr ann) (Expr ann)            ann
    | If   Lbl  (Expr ann) (Expr ann) (Expr ann) ann
    -- Operators
    | Op   Op   (Expr ann) (Expr ann)            ann
    -- Pairs
    | Pair      (Expr ann) (Expr ann)            ann
    | Fst       (Expr ann)                       ann
    | Snd       (Expr ann)                       ann
    -- Lists
    | Nil                                        ann
    | Cons      (Expr ann) (Expr ann)            ann
    | Case Lbl  (Expr ann)
                (Maybe (            Expr ann))
                (Maybe (Name, Name, Expr ann))   ann
    deriving (Eq, Ord, Show)
    -- FIXME: moving ann to the front would give better
    --        partial application behaviour
    
instance Substitute s t => Substitute s (Expr t) where
    subst $@ (Var x ann)
        = Var x (subst $@ ann)
    subst $@ (Con c ann)
        = Con c (subst $@ ann)
    subst $@ (Abs x e ann)
        = Abs x (subst $@ e) (subst $@ ann)
    subst $@ (Fix f e ann)
        = Fix f (subst $@ e) (subst $@ ann)
    subst $@ (App e1 e2 ann)
        = App (subst $@ e1) (subst $@ e2) (subst $@ ann)
    subst $@ (Let x e1 e2 ann)
        = Let x (subst $@ e1) (subst $@ e2) (subst $@ ann)
    subst $@ (If lbl e0 e1 e2 ann)
        = If lbl (subst $@ e0) (subst $@ e1) (subst $@ e2) (subst $@ ann)
    -- Operators
    subst $@ (Op op e1 e2 ann)
        = Op op (subst $@ e1) (subst $@ e2) (subst $@ ann)
    -- Pairs
    subst $@ (Pair e1 e2 ann)
        = Pair (subst $@ e1) (subst $@ e2) (subst $@ ann)
    subst $@ (Fst e ann)
        = Fst (subst $@ e) (subst $@ ann)
    subst $@ (Snd e ann)
        = Snd (subst $@ e) (subst $@ ann)
    -- Lists
    subst $@ (Nil ann)
       = Nil (subst $@ ann)
    subst $@ (Cons e1 e2 ann)
        = Cons (subst $@ e1) (subst $@ e2) (subst $@ ann)
    subst $@ (Case lbl e0 arm1 arm2 ann)
        = Case lbl (subst $@ e0) (subst $@ arm1) (subst $@ arm2) (subst $@ ann)

-- * Top-level annotation
{- unused
topLevelAnn :: Expr ann -> ann
topLevelAnn (Var  _       ann) = ann
topLevelAnn (Con  _       ann) = ann
topLevelAnn (Abs  _ _     ann) = ann
topLevelAnn (Fix  _ _     ann) = ann
topLevelAnn (App  _ _     ann) = ann
topLevelAnn (Let  _ _ _   ann) = ann
topLevelAnn (If   _ _ _ _ ann) = ann
topLevelAnn (Op   _ _ _   ann) = ann
topLevelAnn (Pair _ _     ann) = ann
topLevelAnn (Fst  _       ann) = ann
topLevelAnn (Snd  _       ann) = ann
topLevelAnn (Nil          ann) = ann
topLevelAnn (Cons _ _     ann) = ann
topLevelAnn (Case _ _ _ _ ann) = ann
-}
-- | Constants

data Con
    = Unit
    | Bool      Bool
    | Int       Int
    | ExnC Lbl  ExnC
    deriving (Eq, Ord, Show)
    
data ExnC
    = Crash
    | Diverge
    | PatternMatchFail
    | DivisionByZero
    deriving (Eq, Ord, Show)

-- | Operators

data Op
    = LEQ
    | ADD
    deriving (Eq, Ord, Show)
