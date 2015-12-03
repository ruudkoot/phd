module Main where

-- | Model

-- * Underlying types

data Ul1
    = UlReal
    | UlBool
  deriving (Eq, Show)

data UlN = UlN [UlN] Ul1
  deriving (Eq, Show)

-- * Dimension types

data Dim
    = F Int [Dim]
    | Prod Dim Dim
    | Inv Dim
    | DimVar Int
    | DimL
    | DimM
    | DimT
  deriving (Show)

data Constr
    = C Int [Dim]
    | EqDelta Dim Dim
  deriving (Eq, Show)

data Ty1
    = Real Int
    | Bool
  deriving (Eq, Show)

data TyRes
    = Real' Dim
    | Bool'
  deriving (Show)

data TyN = Ty1 Ty1
         | TyN Int [Constr] [TyN] TyRes
  deriving (Eq, Show)
  
ty1 :: Ty1 -> TyN
ty1 = TyN 0 [] []
  
type TyEnv = [TyN]

-- * Terms

data Tm
    = TmVar Int
  deriving (Eq, Show)

-- | Dimension reconstruction

reconstruct :: TyEnv -> Tm -> TyN
reconstruct env (TmVar x) = env !! x

-- | Examples

tyOp = TyN 2 [C 666 [0,1]] [ty1 (Real 0), ty1 (Real 1)] (Real' (Prod (DimVar 0) (DimVar 1))


