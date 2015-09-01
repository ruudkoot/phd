module Abstract.Unit  where

import Data.Set
import Data.List (intersperse)

newtype AbsUnit
    = AbsUnit (Set ())
    deriving (Eq, Ord)
    
instance Show AbsUnit where
    show (AbsUnit s) = "{" ++ concat (intersperse "," (fmap show (toList s))) ++ "}"

injectUnit :: () -> AbsUnit
injectUnit = AbsUnit . singleton

mergeAbsUnit :: AbsUnit -> AbsUnit -> AbsUnit
mergeAbsUnit (AbsUnit a) (AbsUnit b) = AbsUnit (a `union` b)

subsetAbsUnit :: AbsUnit -> AbsUnit -> Bool
subsetAbsUnit (AbsUnit a) (AbsUnit b) = a `isSubsetOf` b

topAbsUnit :: AbsUnit
topAbsUnit = injectUnit ()
