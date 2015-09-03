module Main where

type Idx = Int

data Name
    = Free  Idx
    | Bound Idx
    | Con   Idx
    deriving (Eq, Read)

data Ty = Arr [Ty] Idx

base :: Idx -> Ty
base = Arr []

data Tm = Tm [Ty] [(Either Name Tm, [Tm])]

data Nf = Nf [Ty] [(       Name,    [Nf])]
