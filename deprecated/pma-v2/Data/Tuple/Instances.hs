{-# LANGUAGE TupleSections #-}

module Data.Tuple.Instances where

import Control.Applicative

import Data.Foldable
import Data.Traversable

import Data.Monoid

-- | 3-tuple

instance Functor ((,,) a b) where
    fmap f (x,y,z) = (x, y, f z)
    
instance Foldable ((,,) a b) where
    foldMap f (x, y, z) = f z `mappend` mempty

instance Traversable ((,,) a b) where
    traverse f (x, y, z) = (x, y,) <$> f z
