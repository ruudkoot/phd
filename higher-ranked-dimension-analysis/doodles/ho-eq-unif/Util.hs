module Util (
    maximum',
    unionMap',
    _tests_
) where

import Data.Set (Set, toList, unions)

import qualified Data.Set as S (fromList)
import Test.Util

-- * Lists * --------------------------------------------------------------[ ]--

maximum' :: Ord a => a -> [a] -> a
maximum' x xs = maximum (x : xs)

-- * Sets * ---------------------------------------------------------------[X]--

-- UNUSED
unionMap :: Ord b => (a -> Set b) -> Set a -> Set b
unionMap f ss = unions (map f (toList ss))

unionMap' :: Ord b => (a -> Set b) -> [a] -> Set b
unionMap' f ss = unions (map f ss)

-- | TESTS | -------------------------------------------------------------------

_tests_ :: [(String, Bool)]
_tests_ =
    [("unionMap",                       _test_unionMap)
    ,("unionMap'",                      _test_unionMap')
    ]

_test_unionMap = unionMap f (S.fromList [1,2,3]) =?= S.fromList [1,2,3,4,5]
    where f 1 = S.fromList [1,2,3]
          f 2 = S.fromList [2,3,4]
          f 3 = S.fromList [3,4,5]

_test_unionMap' = unionMap' f [1,2,3] =?= S.fromList [1,2,3,4,5]
    where f 1 = S.fromList [1,2,3]
          f 2 = S.fromList [2,3,4]
          f 3 = S.fromList [3,4,5]
