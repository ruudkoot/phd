module Fresh where

import Control.Monad
import Control.Monad.State

import Names

-- * Inference Monad

type InferM r = State [Name] r

-- * Fresh variables

class Fresh a where
    fresh :: InferM a

instance (Fresh a, Fresh b) => Fresh (a, b) where
    fresh = do x <- fresh
               y <- fresh
               return (x, y)

instance Fresh Name where
    fresh = do (x:xs) <- get
               put xs
               return x
