module Main where

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

type Name = String

-- | Dimensions

type DimVar = Name

data Dim = Dim { unDim :: Map DimVar Integer }
    deriving Show

-- | Types

data TyCon = TyBool
    deriving Show

data Ty = TyCon TyCon | TyReal Dim | Ty :-> Ty | Forall DimVar Ty
    deriving Show

-- | Free dimension variables

class FDV t where
    fdv :: t -> Set DimVar

instance FDV Dim where
    fdv = S.fromList . M.keys . unDim

instance FDV TyCon where
    fdv TyBool = S.empty

instance FDV Ty where
    fdv (TyCon tc)      = fdv tc
    fdv (TyReal dim)    = fdv dim
    fdv (t1 :-> t2)     = fdv t1 `S.union` fdv t2
    fdv (Forall dim ty) =  S.delete dim (fdv ty)

-- | Expressions

data Expr
    = Var Name
    | Con Rational
    | Zero Dim
    | Expr :@ Expr
    | Abs Name Ty Expr
    | 
    deriving Show
