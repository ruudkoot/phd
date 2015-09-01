module Data.Equiv
    ( Equiv(), empty, elems, insert, insert2, union, equivalent
    , equivalenceClass, representatives                         )
where

import qualified Data.List             as L
import qualified Data.Map              as M
import           Data.Maybe
import qualified Data.Set              as S

import qualified Data.UnionFind.IntMap as UF               -- == union-find-0.2

-- | Exported data types and functions

data Equiv a = Equiv { m :: M.Map a (UF.Point a), ps :: UF.PointSupply a }

-- * The empty equivalence relation
empty :: Equiv a
empty = Equiv { m = M.empty, ps = UF.newPointSupply }

-- * The elements of the relation
elems :: Ord a => Equiv a -> [(a,a)]
elems e@Equiv { m = m, ps = ps }
    = [(a,b) | a <- M.keys m, b <- equivalenceClass' e a ]

-- * Insert new element into equivalence relation; must be fresh (verified)
insert :: Ord a => a -> Equiv a -> Equiv a
insert x Equiv { m = m, ps = ps }
    = let (ps', p) = UF.fresh ps x
       in Equiv { m = M.insertWith (error "duplicate element") x p m, ps = ps' }
                                     
-- * Insert pair into equivalence relation; may be fresh or pre-existing
insert2 :: Ord a => a -> a -> Equiv a -> Equiv a
insert2 x y e0@Equiv { m = m0, ps = ps0 }
    = let e1@Equiv { m = m1, ps = ps1 }
            = case M.lookup x m0 of
                    Nothing -> insert x e0
                    Just _  ->          e0
          e2@Equiv { m = m2, ps = ps2 }
            = case M.lookup y m1 of 
                    Nothing -> insert y e1
                    Just _  ->          e1
       in union e2 x y

-- * Unions two equivalence classes in the relation
union :: Ord a => Equiv a -> a -> a -> Equiv a
union Equiv { m = m, ps = ps } x y
    = Equiv { m = m, ps = UF.union ps (m ?? x) (m ?? y) }

-- * Test if two elements are equivalent
equivalent :: Ord a => Equiv a -> a -> a -> Bool
equivalent Equiv { m = m, ps = ps } x y
    = UF.equivalent ps (m ?? x) (m ?? y)

-- * Enumerate all elements equivalent to the given (the equivalence class)
equivalenceClass :: Ord a => Equiv a -> a -> S.Set a
equivalenceClass Equiv { m = m, ps = ps } x
    = S.fromList [ y | y <- M.keys m, UF.equivalent ps (m ?? x) (m ?? y) ]
    
equivalenceClass' :: Ord a => Equiv a -> a -> [a]
equivalenceClass' Equiv { m = m, ps = ps } x
    = [ y | y <- M.keys m, UF.equivalent ps (m ?? x) (m ?? y) ]
    
-- * Enumerate all representatives of the equivalence classes in the relation
representatives :: Ord a => Equiv a -> S.Set a
representatives Equiv { m = m, ps = ps }
    = S.foldr (S.insert . UF.descriptor ps . UF.repr ps . (m ??)) S.empty (M.keysSet m)

-- | Helper functions

-- * Show

instance (Ord a, Show a) => Show (Equiv a) where
    show e@Equiv { m = m, ps = ps }
        = let r = representatives e
           in showSet $ S.foldr (\x -> (:) (showSet' x $ equivalenceClass e x)) [] r

showSet :: [String] -> String
showSet x = "{" ++ L.intercalate "," x ++ "}"

showSet' :: (Eq a, Show a) => a -> S.Set a -> String
showSet' r x = "{" ++ L.intercalate "," (map (\x' -> if x' == r then "[" ++ show x' ++ "]" else show x') (S.toList x)) ++ "}"

-- * Lookup value in map that is known to exist
(??) :: Ord a => M.Map a (UF.Point a) -> a -> UF.Point a
m ?? x = fromMaybe (error "Equiv.(??)") (M.lookup x m)

-- * Lookup value in map or insert if it does not exist yet
lookupInsert :: Ord k => k -> a -> M.Map k a -> (a, M.Map k a)
lookupInsert k v m
    = let (o, m') = M.insertLookupWithKey (\_ o _ -> o) k v m
       in (fromMaybe v o, m')
