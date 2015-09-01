module Abstract.Bool where

import Data.List (intersperse)
import Data.Set

newtype AbsBool
    = AbsBool (Set Bool)
    deriving (Eq, Ord)
    
instance Show AbsBool where
    show (AbsBool s) = "{" ++ concat (intersperse "," (fmap show (toList s))) ++ "}"

injectBool :: Bool -> AbsBool
injectBool = AbsBool . singleton

mergeAbsBool :: AbsBool -> AbsBool -> AbsBool
mergeAbsBool (AbsBool s) (AbsBool t) = AbsBool (s `union` t)

meetAbsBool :: AbsBool -> AbsBool -> AbsBool
meetAbsBool (AbsBool s) (AbsBool t) = AbsBool (s `intersection` t)

subsetAbsBool :: AbsBool -> AbsBool -> Bool
subsetAbsBool (AbsBool a) (AbsBool b) = a `isSubsetOf` b

topAbsBool :: AbsBool
topAbsBool = injectBool True `mergeAbsBool` injectBool False

botAbsBool :: AbsBool
botAbsBool = AbsBool empty

-- | "Primitive" operators

absBoolNot :: AbsBool -> AbsBool
absBoolNot (AbsBool xs) = AbsBool (fromList [not x | x <- toList xs])

absBoolAnd :: AbsBool -> AbsBool -> AbsBool
absBoolAnd (AbsBool xs) (AbsBool ys) = AbsBool (fromList [x && y | x <- toList xs, y <- toList ys])

absBoolOr :: AbsBool -> AbsBool -> AbsBool
absBoolOr (AbsBool xs) (AbsBool ys) = AbsBool (fromList [x || y | x <- toList xs, y <- toList ys])
