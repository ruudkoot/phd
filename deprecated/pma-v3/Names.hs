module Names where

-- | Names

newtype Name = Name String deriving (Eq, Ord)

instance Show Name where
    show (Name x) = x

augment :: String -> Name -> Name
augment prefix (Name name') = Name (prefix ++ name')

-- | Fresh Names

freshIdents :: [Name]
freshIdents = map (\n -> Name $ "?" ++ show n) [(1::Int)..]
