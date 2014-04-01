module Names where

import Control.Monad
import Control.Monad.State

-- | Names

type Name = Int

-- | Fresh names

type Fresh a = State Name a

fresh :: Fresh Name
fresh = do
    name <- get
    modify (+1)
    return name

evalFresh = evalState

-- | Environment lookup

lookup' :: (Eq a, Show a, Show b) => String -> a -> [(a,b)] -> b
lookup' msg k xs = case lookup k xs of
                     Nothing -> error $ msg ++ ": could not find '" ++ show k
                                            ++ "' in "              ++ show xs
                     Just v  -> v
