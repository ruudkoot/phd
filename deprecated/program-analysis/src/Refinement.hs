module Refinement where

import           Data.List
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Language.Haskell.Exts.Annotated hiding (Cons)

-- | Annotations

data Phi
    = Phi { phi :: Refinement }
    | NoPhi
    | UC { uc :: [RefConstr] } -- unsolved constraints
    deriving (Eq, Ord)
    
instance Show Phi where
    show (Phi r) = show r
    show (NoPhi) = "X"

-- | Refinements

data Refinement
    = RefVar (Name Phi)
    | RefCon
    deriving (Eq, Ord)

instance Show Refinement where
    show (RefVar    name   ) = prettyPrint name
    show (RefCon           ) = "RefCon"
  
-- | Constraints

data RefConstr
    = Refinement :<: Refinement
    deriving (Eq, Ord)

instance Show RefConstr where
    show (t1 :<: t2) = show t1 ++ " ⊆ " ++ show t2
    
-- * Unification variable renaming for instantiation

infixr 0 $@*^

($@*^) :: Map (Name Phi) (Name Phi) -> Refinement -> Refinement
sigma $@*^ (RefVar name)
    = RefVar (Map.findWithDefault name name sigma)
sigma $@*^ x
    = x
