{-# LANGUAGE MultiParamTypeClasses #-}

module Exn where

import qualified Data.Set as S

import Subst
import FTV
import Syntax
import Constr
         
-- * Exceptions

data Exn
    = ExnVar   Name
    | ExnCrash Lbl
    deriving (Eq, Ord)
    
instance Show Exn where
    show (ExnVar name)  = show name
    show (ExnCrash lbl) = "CRASH_" ++ lbl
    
instance FTV Exn where
    ftv (ExnVar name) = S.singleton name
    ftv _             = S.empty
    
instance ConstrElem Exn where
    injName = ExnVar
    
    prjName (ExnVar n) = Just n
    prjName _          = Nothing
    
instance Substitute Name Exn where
    subst $@ ExnVar a = ExnVar (subst $@ a)
    _     $@ exn      = exn
