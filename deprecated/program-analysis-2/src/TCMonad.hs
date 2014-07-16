module TCMonad where

import Prelude hiding (log)

data State = State { freshVars :: [Int]
                   , log       :: [String]
                   }
    deriving Show
newtype TC a  = TC (State -> (a, State))

instance Monad TC where
    TC c1 >>= fc2 = TC (\s0 -> let (r, s1) = c1 s0
                                   TC c2   = fc2 r
                                in c2 s1
                       )
    return k      = TC (\s -> (k, s))
    
freshTC :: TC Int
freshTC = TC (\s -> let (fv:fvs) = freshVars s in (fv, State { freshVars = fvs, log = log s }))

logTC :: String -> TC ()
logTC msg = TC (\s -> ((), State { freshVars = freshVars s, log = msg : log s } ))

runTC :: TC a -> (a, State)
runTC (TC c) = c (State { freshVars = [0..], log = [] })
