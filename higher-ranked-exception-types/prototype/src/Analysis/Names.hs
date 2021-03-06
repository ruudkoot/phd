{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Analysis.Names where

import Control.Monad
import Control.Monad.State
import Data.Monoid

-- | Names

type Name = Int

next :: Name -> Name
next name = name + 1

-- | Fresh names

class MonadFresh m where
    fresh :: m Name
    
type Fresh = State Name

instance MonadFresh Fresh where
    fresh = do
        name <- get
        modify next
        return name

evalFresh :: Fresh a -> Name -> a
evalFresh = evalState

-- | Miscellaneous

-- FIXME: this function is here to avoid a cyclic import

lookup' :: (Eq a, Show a, Show b) => String -> a -> [(a,b)] -> b
lookup' msg k xs = case lookup k xs of
                     Nothing -> error $ msg ++ ": could not find '" ++ show k
                                            ++ "' in "              ++ show xs
                     Just v  -> v
