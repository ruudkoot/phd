{-# LANGUAGE MultiParamTypeClasses #-}

module Ref where

import qualified Data.Set as S

import Subst
import FTV
import Syntax
import Constr

-- * Refinements

data Ref
    = RefVar  Name
    | RefTop
    | RefBool Bool
    | RefInt  Int'
    -- Lists
    | RefList List'
    deriving (Eq, Ord)
    
instance Show Ref where
    show (RefVar  x) = show x
    show (RefTop   ) = "T"
    show (RefBool b) = show b
    show (RefInt  n) = show n
    show (RefList l) = show l
    
instance FTV Ref where
    ftv (RefVar name) = S.singleton name
    ftv _             = S.empty

instance ConstrElem Ref where
    injName = RefVar

    prjName (RefVar n) = Just n
    prjName _          = Nothing
    
instance Substitute Name Ref where
    subst $@ RefVar a = RefVar (subst $@ a)
    _     $@ ref      = ref        
    
data Int'
    = Neg
    | Zero
    | Pos
    deriving (Eq, Ord)
    
instance Show Int' where
    show Neg  = "-"
    show Zero = "0"
    show Pos  = "+"

data List'
    = E
    | NE
    deriving (Eq, Ord, Show)

injInt :: Int -> Int'
injInt n | n < 0     = Neg
         | n > 0     = Pos
         | otherwise = Zero
