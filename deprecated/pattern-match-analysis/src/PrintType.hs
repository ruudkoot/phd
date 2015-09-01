module PrintType where

import Data.List (intersperse)

import Language.Haskell.Exts.Annotated

import Refinement

printType :: Type Phi -> String
printType (TyFun phi a b  )      = "(" ++ printType a ++ " -> " ++ printType b ++ ")@" ++ show phi
printType (TyTuple phi boxed ts) = "(" ++ concat (intersperse "," (map printType ts)) ++ ")@" ++ show phi
printType (TyList phi a   )      = "[" ++ printType a ++ "]@" ++ show phi
printType (TyVar phi name )      = prettyPrint name -- ++ "@" ++ show phi
printType (TyCon phi qname)      = prettyPrint qname ++ "@" ++ show phi
printType (TyForall (UC { uc = cs }) Nothing Nothing t) = "forall. " ++ show cs ++ " => " ++ printType t
printType x                      = error ("printType: " ++ show x)
