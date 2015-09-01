module Abstract.Either (AbsEither, mkAbsEither, joinAbsEither, absEitherContains) where

import Prelude
import Data.List (intersperse)
import Data.Set hiding (map)

import Abstract.Bool

newtype AbsEither = AbsEither (Set (Either AbsBool AbsBool))
    deriving (Eq, Ord)

mkAbsEither :: Either Bool Bool -> AbsEither
mkAbsEither (Left  b) = AbsEither (singleton (Left  (mkAbsBool b)))
mkAbsEither (Right b) = AbsEither (singleton (Right (mkAbsBool b)))

joinAbsEither :: AbsEither -> AbsEither -> AbsEither
joinAbsEither (AbsEither a) (AbsEither b) = AbsEither (a `union` b)

absEitherContains :: AbsEither -> AbsEither -> Bool
absEitherContains (AbsEither a) (AbsEither b) = a `isSubsetOf` b

instance Show AbsEither where
    show (AbsEither a) = "{" ++ concat (intersperse "," (map show (toList a))) ++ "}"
