module Util.Set where

import Data.List (intersperse)
import Data.Set

showSet :: Show a => Set a -> String
showSet = surround "{" "}" . concat . intersperse ", " . fmap show . toList
    where surround l r m = l ++ m ++ r
