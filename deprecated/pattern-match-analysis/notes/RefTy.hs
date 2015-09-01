module RefTy where

import Data.List

type ConName   = String
type TyName    = String
type RefTyName = String
type TyVar     = String
type RefTyVar  = String

data DataCon  = DataCon ConName [TyName]
data DataType = DataType TyName [DataCon]

instance Show DataCon where
    show (DataCon conName tns) = conName ++ " " ++ concat (intersperse " " tns)
    
instance Show DataType where
    show (DataType tyName dcs) = "data " ++ tyName ++ " = " ++ concat (intersperse " | " (map show dcs))

data RefTy = RefTy :/\: RefTy   -- intersection type
           | RefTy :\/: RefTy   -- union type
           | RefTy :->: RefTy   -- function type
           | Bottom             -- bottom
           | A TyName [RefTy]
           | B RefTyName [RefTy]
           | RefTyVar ::: TyVar

instance Show RefTy where
    show (t1 :/\: t2)   = "(" ++ show t1 ++ " ∧ " ++ show t2 ++ ")"
    show (t1 :\/: t2)   = "(" ++ show t1 ++ " ∨ " ++ show t2 ++ ")"
    show (t1 :->: t2)   = "(" ++ show t1 ++ " → " ++ show t2 ++ ")"
    show (Bottom    )   = "⊥"
    show (A tyName rts) = tyName ++ " " ++ concat (intersperse " " (map show rts))
    show (B refTyName rts) = refTyName ++ " " ++ concat (intersperse " " (map show rts))
    show (rtv ::: tv)   = rtv ++ " :: " ++ tv
    
-- | Examples

dataBitstr = DataType "Bitstr" [DataCon "E" [], DataCon "Z" ["Bitstr"], DataCon "O" ["Bitstr"]]
