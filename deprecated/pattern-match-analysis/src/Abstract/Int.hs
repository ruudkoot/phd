module Abstract.Int {- (AbsInt, injectInt, mergeAbsInt, subsetAbsInt) -} where

import Data.List (intersperse)
import Data.Set hiding (map)

import Abstract.Bool

{- -- | Set-abstracted integer

newtype AbsInt = AbsInt (Set Integer)
    deriving (Eq, Ord)

mkAbsInt :: Integer -> AbsInt
mkAbsInt n = AbsInt (singleton n)

joinAbsInt :: AbsInt -> AbsInt -> AbsInt
joinAbsInt (AbsInt a) (AbsInt b) = AbsInt (a `union` b)

instance Show AbsInt where
    show (AbsInt a) = "{" ++ concat (intersperse "," (map show (toList a))) ++ "}"
-}

-- | Sign-abstracted integer

data Sign = Neg | Zero | Pos
    deriving (Eq, Ord)

instance Show Sign where
    show Neg  = "-"
    show Zero = "0"
    show Pos  = "+"

newtype AbsInt = AbsInt (Set Sign)
    deriving (Eq, Ord)
    
instance Show AbsInt where
    show (AbsInt s) = "{" ++ concat (intersperse "," (map show (toList s))) ++ "}"

injectInt :: Integer -> AbsInt
injectInt = AbsInt . singleton . int2sign

int2sign :: Integer -> Sign
int2sign n = case signum n of
                -1 -> Neg
                0  -> Zero
                1  -> Pos
                
mergeAbsInt :: AbsInt -> AbsInt -> AbsInt
mergeAbsInt (AbsInt a) (AbsInt b) = AbsInt (a `union` b)

subsetAbsInt :: AbsInt -> AbsInt -> Bool
subsetAbsInt (AbsInt a) (AbsInt b) = a `isSubsetOf` b

topAbsInt :: AbsInt
topAbsInt = injectInt (-1) `mergeAbsInt` injectInt 0 `mergeAbsInt` injectInt 1

-- | Primitive operators

absIntPlus :: AbsInt -> AbsInt -> AbsInt
absIntPlus (AbsInt xs) (AbsInt ys) = AbsInt (unions [signPlus x y | x <- toList xs, y <- toList ys])
    where signPlus :: Sign -> Sign -> Set Sign
          signPlus Zero y    = fromList [y]
          signPlus x    Zero = fromList [x]
          signPlus Neg  Neg  = fromList [Neg]
          signPlus Pos  Pos  = fromList [Pos]
          signPlus Neg  Pos  = fromList [Neg, Zero, Pos]
          signPlus Pos  Neg  = fromList [Neg, Zero, Pos]
          
absIntMul :: AbsInt -> AbsInt -> AbsInt
absIntMul (AbsInt xs) (AbsInt ys) = AbsInt (unions [signMul x y | x <- toList xs, y <- toList ys])
    where signMul :: Sign -> Sign -> Set Sign
          signMul Zero _    = fromList [Zero]
          signMul _    Zero = fromList [Zero]
          signMul x    y    | x == y    = fromList [Pos]
                            | otherwise = fromList [Neg]

absIntEq :: AbsInt -> AbsInt -> AbsBool
absIntEq (AbsInt xs) (AbsInt ys) = AbsBool (unions [signEq x y | x <- toList xs, y <- toList ys])
    where signEq :: Sign -> Sign -> Set Bool
          signEq Zero Zero = fromList [True]
          signEq x    y    | x == y    = fromList [True, False]
                           | otherwise = fromList [False]
                           
absIntLT :: AbsInt -> AbsInt -> AbsBool
absIntLT (AbsInt xs) (AbsInt ys) = AbsBool (unions [signLT x y | x <- toList xs, y <- toList ys])
    where signLT :: Sign -> Sign -> Set Bool
          signLT Neg  Neg  = fromList [True, False]
          signLT Neg  Zero = fromList [True]
          signLT Neg  Pos  = fromList [True]
          signLT Zero Neg  = fromList [False]
          signLT Zero Zero = fromList [False]
          signLT Zero Pos  = fromList [True]
          signLT Pos  Neg  = fromList [False]
          signLT Pos  Zero = fromList [False]
          signLT Pos  Pos  = fromList [True, False]

absIntLE :: AbsInt -> AbsInt -> AbsBool
absIntLE (AbsInt xs) (AbsInt ys) = AbsBool (unions [signLE x y | x <- toList xs, y <- toList ys])
    where signLE :: Sign -> Sign -> Set Bool
          signLE Neg  Neg  = fromList [True, False]
          signLE Neg  Zero = fromList [True]
          signLE Neg  Pos  = fromList [True]
          signLE Zero Neg  = fromList [False]
          signLE Zero Zero = fromList [True]
          signLE Zero Pos  = fromList [True]
          signLE Pos  Neg  = fromList [False]
          signLE Pos  Zero = fromList [False]
          signLE Pos  Pos  = fromList [True, False]

absIntGT :: AbsInt -> AbsInt -> AbsBool
absIntGT (AbsInt xs) (AbsInt ys) = AbsBool (unions [signGT x y | x <- toList xs, y <- toList ys])
    where signGT :: Sign -> Sign -> Set Bool
          signGT Neg  Neg  = fromList [True, False]
          signGT Neg  Zero = fromList [False]
          signGT Neg  Pos  = fromList [False]
          signGT Zero Neg  = fromList [True]
          signGT Zero Zero = fromList [False]
          signGT Zero Pos  = fromList [False]
          signGT Pos  Neg  = fromList [True]
          signGT Pos  Zero = fromList [True]
          signGT Pos  Pos  = fromList [True, False]

absIntGE :: AbsInt -> AbsInt -> AbsBool
absIntGE (AbsInt xs) (AbsInt ys) = AbsBool (unions [signGE x y | x <- toList xs, y <- toList ys])
    where signGE :: Sign -> Sign -> Set Bool
          signGE Neg  Neg  = fromList [True, False]
          signGE Neg  Zero = fromList [False]
          signGE Neg  Pos  = fromList [False]
          signGE Zero Neg  = fromList [True]
          signGE Zero Zero = fromList [True]
          signGE Zero Pos  = fromList [False]
          signGE Pos  Neg  = fromList [True]
          signGE Pos  Zero = fromList [True]
          signGE Pos  Pos  = fromList [True, False]
