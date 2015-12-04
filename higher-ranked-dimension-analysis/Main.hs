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
  deriving (Show)

data Ty1
    = Real Int
    | Bool
  deriving (Eq, Show)

data TyRes
    = Real' Dim
    | Bool'
  deriving (Show)

data TyN
    = Ty1 Ty1
    | TyN Int [Constr] [TyN] TyRes
  deriving (Show)
  
type TyEnv = [TyN]

-- * Terms

data Tm
    = TmVar Int
    | TmApp Tm Tm
  deriving (Eq, Show)

-- | Dimension reconstruction

reconstruct :: TyEnv -> Tm -> TyN
reconstruct env (TmVar x)
    = env !! x
reconstruct env (TmApp t1 t2)
    = 

-- | Examples

tyOp = TyN 2 [C 666 [DimVar 0, DimVar 1]] [Ty1 $ Real 0, Ty1 $ Real 1] (Real' (Prod (DimVar 0) (DimVar 1)))

ex1 = reconstruct [tyOp] (TmVar 0)
