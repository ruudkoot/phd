module Analysis.Latex where

import Data.List

class Latex a where
    latex :: a -> String

instance Latex () where
    latex () = "\\diamond"

instance Latex a => Latex [a] where
    latex env = "[" ++ intercalate "," (map latex env) ++ "]"
