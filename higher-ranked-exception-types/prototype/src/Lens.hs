module Lens (
    Lens(..)
) where

-- | Lenses

data Lens a b = Lens { get :: a -> b, set :: a -> b -> a }


