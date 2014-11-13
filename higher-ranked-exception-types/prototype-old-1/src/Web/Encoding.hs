{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns           #-}

module Web.Encoding (
    Encoding(..),
    URLEncoded(..),
    WWWFormURLEncoded(..)
) where

import Control.Arrow
import Data.Char
import Data.List
import Data.List.Split
import Data.List.Utils
import Data.Map (Map, fromList, toList)

-- | Class

class Encoding a b | a -> b where
    encode :: b -> a
    decode :: a -> b

{-    
instance Encoding a [(k,v)] => Encoding a (Map k v) where
    encode = fromList . encode
    decode = decode . toList
-}

-- | Instances

-- * urlencoded

newtype URLEncoded = URLEncoded String
    deriving Show

-- * application/x-www-form-urlencoded

newtype WWWFormURLEncoded = WWWFormURLEncoded { wwwFormURLEncoded :: String }
    deriving Show

instance Encoding WWWFormURLEncoded [(String,String)] where
    decode = wwwFormURLEncoded >>> splitOn "&"
             >>> map (break' (== '=') >>> fmap (replace "+" " " >>> percentDecode))

-- | Generic helpers

break' :: (a -> Bool) -> [a] -> ([a] , [a])
break' p = fmap tail . break p

hexDigit :: Char -> Int
hexDigit (ord -> c) | between (ord '0') (ord 'F') c = c - ord '0'
    where between l u x = l <= x && x <= u
    
percentDecode :: String -> String
percentDecode ""
    = ""
percentDecode ('%':(hexDigit -> d1):(hexDigit -> d0):xs)
    = chr (16 * d1 + d0) : percentDecode xs
percentDecode (x:xs)
    = x : percentDecode xs
