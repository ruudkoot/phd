module Util where

-- | Fixed point

fix f x = fix' (iterate f x)
    where fix' (a1:as@(a2:_)) | a1 == a2  = a1
                              | otherwise = fix' as

-- | Show

listPerLine :: [String] -> String
listPerLine = concatMap (++ "\n")
