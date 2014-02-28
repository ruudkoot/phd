{-# LANGUAGE MultiParamTypeClasses #-}

module Shapes where

import qualified Data.Set as S

import Names
import Fresh
import FTV
import Subst
import Types

-- | Shapes

data Sh
    = ShBase       Name
    | ShFun  Sh Sh Name
    -- Pairs
    | ShPair Sh Sh Name
    -- Lists
    | ShList Sh    Name
    deriving (Eq, Ord)
    
instance Show Sh where
    show (ShBase         x)
        = show x
    show (ShFun  sh1 sh2 x)
        = "(" ++ show sh1 ++ " -> " ++ show sh2 ++ ")" ++ "^(" ++ show x ++ ")"
    -- Pairs
    show (ShPair sh1 sh2 x)
        = "(" ++ show sh1 ++ ", "   ++ show sh2 ++ ")" ++ "^(" ++ show x ++ ")"
    -- Lists
    show (ShList sh      x)
        = "[" ++ show sh ++ "]"                        ++ "^(" ++ show x ++ ")"
    
instance Fresh Sh where
    fresh = do a <- fresh
               return (ShBase a)

instance Substitute Name Sh where
    subst $@ ShBase         x
        = ShBase                               (subst $@ x)
    subst $@ ShFun  sh1 sh2 x
        = ShFun  (subst $@ sh1) (subst $@ sh2) (subst $@ x)
    -- Pairs
    subst $@ ShPair sh1 sh2 x
        = ShPair (subst $@ sh1) (subst $@ sh2) (subst $@ x)
    -- Lists
    subst $@ ShList sh      x
        = ShList (subst $@ sh)                 (subst $@ x)
        
-- | Free variables

instance FTV Sh where
    ftv (ShBase         x)
        = S.singleton x
    ftv (ShFun  sh1 sh2 x)
        = x `S.insert` ftv sh1 `S.union` ftv sh2
    ftv (ShPair sh1 sh2 x)
        = x `S.insert` ftv sh1 `S.union` ftv sh2
    ftv (ShList sh      x)
        = x `S.insert` ftv sh

positiveVariables :: Sh -> S.Set Name
positiveVariables (ShBase         x)
    = S.singleton x
positiveVariables (ShFun  sh1 sh2 x)
    = x `S.insert` negativeVariables sh1 `S.union` positiveVariables sh2
positiveVariables (ShPair sh1 sh2 x)
    = x `S.insert` positiveVariables sh1 `S.union` positiveVariables sh2
positiveVariables (ShList sh      x)
    = x `S.insert` positiveVariables sh

negativeVariables :: Sh -> S.Set Name
negativeVariables (ShBase         x)
    = S.empty
negativeVariables (ShFun  sh1 sh2 x)
    = positiveVariables sh1 `S.union` negativeVariables sh2
negativeVariables (ShPair sh1 sh2 x)
    = negativeVariables sh1 `S.union` negativeVariables sh2
negativeVariables (ShList sh      x)
    = negativeVariables sh

-- | Build fresh linear shapes from types

freshLinearShapeFrom :: Ty -> InferM Sh
freshLinearShapeFrom (TyVar _)
    = -- error "newLinearShape: polymorphism"
      do s <- fresh
         return s
freshLinearShapeFrom (TyCon _)
    = do x <- fresh
         return x
freshLinearShapeFrom (TyFun t1 t2)
    = do s1 <- freshLinearShapeFrom t1
         s2 <- freshLinearShapeFrom t2
         x  <- fresh
         return (ShFun s1 s2 x)
freshLinearShapeFrom (TyPair t1 t2)
    = do s1 <- freshLinearShapeFrom t1
         s2 <- freshLinearShapeFrom t2
         x  <- fresh
         return (ShPair s1 s2 x)
freshLinearShapeFrom (TyList t)
    = do s <- freshLinearShapeFrom t
         x <- fresh
         return (ShList s x)

-- | Top-level annotations (not to be confused with the one for Expr)

topLevelAnnotation :: Sh -> Name
topLevelAnnotation (ShBase     x) = x
topLevelAnnotation (ShFun  _ _ x) = x
topLevelAnnotation (ShPair _ _ x) = x
topLevelAnnotation (ShList _   x) = x
