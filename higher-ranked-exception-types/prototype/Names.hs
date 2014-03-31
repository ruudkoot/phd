module Names where

import Control.Monad
import Control.Monad.State

type Name = Int

type Fresh a = State Name a

fresh :: Fresh Name
fresh = do
    name <- get
    modify (+1)
    return name
    
evalFresh = evalState
