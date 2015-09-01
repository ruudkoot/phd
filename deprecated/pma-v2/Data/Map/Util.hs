module Data.Map.Util ((!!), restrict, mapKeysAndValuesWith, unionMap) where

import           Prelude       hiding ((!!))

import qualified Data.Map as M
import qualified Data.Set as S

-- * Lookup with additional error reporting
(!!) :: (Ord k, Show k, Show a) => M.Map k a -> k -> a
m !! k | Just v <- M.lookup k m = v
       | otherwise              = error $ "Data.Map.Util.!!: key '" ++ show k ++ " not found in " ++ show m

restrict :: Ord k => M.Map k a -> [k] -> M.Map k a
restrict = foldr M.delete

mapKeysAndValues :: (Ord k1, Ord k2) =>
    (k1 -> k2) -> (a1 -> a2) -> M.Map k1 a1 -> M.Map k2 a2
mapKeysAndValues f g = M.mapKeys f . M.map g

mapKeysAndValuesWith :: (Ord k1, Ord k2) =>
    (a2 -> a2 -> a2) -> (k1 -> k2) -> (a1 -> a2) -> M.Map k1 a1 -> M.Map k2 a2
mapKeysAndValuesWith c f g = M.mapKeysWith c f . M.map g

-- | Map + Set

unionMap :: (Ord k, Ord b) => (a -> S.Set b) -> M.Map k a -> S.Set b
unionMap f = S.unions . M.elems . M.map f
