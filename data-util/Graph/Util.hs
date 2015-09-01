{-# LANGUAGE StandaloneDeriving #-}

module Data.Graph.Util where

import Data.Graph

deriving instance Show a => Show (SCC a)
