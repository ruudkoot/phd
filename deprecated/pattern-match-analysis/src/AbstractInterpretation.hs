{-# LANGUAGE FunctionalDependencies #-}

module AbstractInterpretation where

import Data.List  as List
import Data.Map   as Map   hiding (singleton)
import Data.Maybe as Maybe
import Data.Set   as Set

import           Language.Haskell.Exts
import qualified Language.Haskell.Exts.Annotated          as Ann
import           Language.Haskell.Exts.Annotated.Simplify

-- | Abstract values    

data Sign  = Pos | Zero | Neg
    deriving (Bounded, Enum, Eq, Ord, Show)

toSign :: Integer -> Sign
toSign n | n <  0 = Neg
         | n == 0 = Zero
         | n >  0 = Pos

data Shape = Nil | Singleton | Cons
    deriving (Bounded, Enum, Eq, Ord, Show)

data AbsVal
    = AbsPoly
    | AbsBool (Set Bool)
    | AbsInt  (Set Sign)
    | AbsList (Set Shape)
    deriving (Eq, Ord, Show)

enumerateAll :: Type -> [AbsVal]
enumerateAll (TyVar _)
    = [AbsPoly]
enumerateAll (TyCon (UnQual (Ident "Bool")))
    = enumerateAll' AbsBool
enumerateAll (TyCon (UnQual (Ident "Int")))
    = enumerateAll' AbsInt

enumerateAll' :: (Bounded a, Enum a, Ord a) => (Set a -> b) -> [b]
enumerateAll' x
    = fmap (x . Set.fromList) (subsequences (enumFromTo minBound maxBound))

type Env = Map QName AbsVal

-- | Main

run :: Ann.Exp Type -> String
run = show . abstractInterpret Map.empty

-- | Abstract interpretation

abstractInterpret :: Env -> Ann.Exp Type -> AbsVal

-- * Variables
abstractInterpret gamma (Ann.Var _ qname)
    = fromMaybe (error "abstractInterpret: Var") (Map.lookup (sQName qname) gamma)
    
-- * Constructors
abstractInterpret gamma (Ann.Con _ (Ann.UnQual _ (Ann.Ident _ "True")))
    = AbsBool (singleton True)
abstractInterpret gamma (Ann.Con _ (Ann.UnQual _ (Ann.Ident _ "False")))
    = AbsBool (singleton False)
abstractInterpret gamma (Ann.Lit _ (Ann.Int _ n _))
    = AbsInt (singleton (toSign n))
--abstractInterpret gamma 

-- * Abstraction
abstractInterpret gamma (Ann.Lambda t {-[Ann.PVar _ name]-}_ e)
    = last $ enumerateAll t

-- * Application

