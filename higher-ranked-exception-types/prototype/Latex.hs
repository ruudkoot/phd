module Latex where

import Data.List

class Latex a where
    latex   :: a -> String
    lhs2tex :: a -> String
    
instance Latex a => Latex [a] where
    lhs2tex env = "[" ++ intercalate "," (map lhs2tex env) ++ "]"
