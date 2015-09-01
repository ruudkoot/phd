module Main where

pmfail = error "pattern-match failure"

f1 (a1:as)    | a1 >= 20 = 'A'
f1 (a1:a2:as) | a2 >= 30 = 'B'
f1 (a1:as)    | a1 >= 10 = 'C'

f2 (a1:as)    | a1 >= 20 = 'A'
f2 (a1:as)    | a1 >= 10 = 'C'
f2 (a1:a2:as) | a2 >= 30 = 'B'

test = f1 [10,30] == f2 [10,30]

f' a = case a of
        (a1:as) -> if a1 >= 20
                     then 'a'
                     else case as of
                            []       -> case a of
                                            (a1x:asx) -> if a1x >= 10
                                                            then 'c'
                                                            else pmfail
                            (a2:as') -> if a2 >= 30
                                            then 'b'
                                            else pmfail


{-

f P1 | G1 = E1
f P2 | G2 = E3
f P3 | G3 = E3

    ~~>

f x = let C1 = case x of
                 P1 -> if G1 then E1 else C2
                 _  -> C2
          C2 = case x of
                 P2 -> if G2 then E2 else C3
                 _  -> C3
          C3 = case x of
                 P3 -> if G3 then E3 else C4
                 _  -> C4
          C4 = pmfail
       in C1

    ~~>
    
f x = let C4 = pmfail
       in let C3 = case x of
                     P3 -> if G3 then E3 else C4
                     _  -> C4
           in let C2 = case x of
                         P2 -> if G2 then E2 else C3
                         _  -> C3
               in let C1 = case x of
                             P1 -> if G1 then E1 else C2
                             _  -> C2
                   in C1

-}
