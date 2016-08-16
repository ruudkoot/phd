module Test.Util
    ( (=?=) )
where

(=?=) :: (Eq a, Show a) => a -> a -> Bool
x =?= y =
    if x == y then
        True
    else
        error $ "\n" ++ show x ++ "\n\n" ++ show y

