module Examples where

import Names
import Syntax

-- | Examples

allExamples =
    -- basic constructs
    [("id", exId)
    ,("const", exConst)
    ,("id True", exIdApp)
    ,("const 42", exConstApp1)
    ,("const 42 False", exConstApp2)
    ,("\\f x. f x", exApply)
    ,("(\\f x. f x) id", exApplyId)
    ,("(\\f x. f x) id id", exApplyIdId)
    ,("4", exCon1)
    ,("-3", exCon2)
    ,("\\k -> False", exCon3)
    ,("let y = (\\x -> if x then False else x) in y", exLet1)
    ,("let y = (\\x -> if x then False else x) in y True", exLet2)
    ,("let y = (\\x -> if x then False else x) in (y True, y False)", exLet3)
    ,("if True then 3 else -3", exIf1)
    ,("\\x -> if x then 3 else -3", exIf2)
    ,("(\\x -> if x then 3 else -3) True", exIf2App)
    ,("\\x -> if x then False else x", exIf3)
    ,("(\\x -> if x then False else x) True", exIf3App)
    ,("5 <= 6", exOp1)
    ,("\\x y -> x + y", exOp2)
    -- polyvariance
    ,("(id CRASH, id True)", exIdPoison)
    -- conditionals
    ,("(\\x -> if x then CRASH else True) False", ex17)
    -- complex functions
    ,("length", exLength)
    ,("length [1,2,3]", exLengthApp)
    ,("map", exMap)
    ,("map (+1) [1,2,3] {- inlined -}", exMapPlus1_Fix)
    ,("map (+1) [1,2,3] {- let-bound -}", exMapPlus1_Let)
    ,("map length []", exMapLengthE)
    ,("map length [[1,2,3],[],[4]]", exMapLengthNE)
    ,("risers", exR0)
    ,("risers (if False then [] else [2,3,1])", exR1)
    ,("risers (if True then [] else [2,3,1])", exR2)
    ,("map risers [...]", exMapRisers)
    -- crashing
    ,("[..,[],..]", someList)
    ,("crashing list", crashingList)
    ,("head []", exHeadNil)
    ,("map head NE[]", exMapHeadNE)
    ,("map head [..,[],..]", exMapHeadE)
    ,("map heap (map risers [..,[],..])", exMapHeadMapRisers)
    ]
    
-- * Converting constants to expressions

class ToExpr a where
    toExpr :: a -> Expr ()
    
instance ToExpr Int where
    toExpr n = Con (Int n) ()

instance ToExpr a => ToExpr [a] where
    toExpr = foldr (\x r -> Cons (toExpr x) r ()) (Nil ())

-- * Basic constructs

exId = Abs (Name "x") (Var (Name "x") ()) ()

exConst = Abs (Name "k") (Abs (Name "x") (Var (Name "k") ()) ()) ()

exIdApp = App exId (Con (Bool True) ()) ()

exConstApp1 = App exConst (Con (Int 42) ()) ()

exConstApp2 = App exConstApp1 (Con (Bool False) ()) ()

exApply = Abs (Name "f") (Abs (Name "x") (App (Var (Name "f") ()) (Var (Name "x") ()) ()) () ) ()

exApplyId = App exApply idY ()
    where idY = Abs (Name "y") (Var (Name "y") ()) ()
    
exApplyIdId = App exApplyId idZ ()
    where idZ = Abs (Name "z") (Var (Name "z") ()) ()

exCon1 = Con (Int 4) ()
exCon2 = Con (Int (-3)) ()
exCon3 = Abs (Name "k") (Con (Bool False) ()) ()

-- Fix

exLet1 = Let (Name "if3") exIf3 (Var (Name "if3") ()) ()
exLet2 = Let (Name "if3") exIf3 (App (Var (Name "if3") ()) (Con (Bool True) ()) ()) ()
exLet3 = Let (Name "if3") exIf3 (Pair ((App (Var (Name "if3") ()) (Con (Bool True) ()) ())) ((App (Var (Name "if3") ()) (Con (Bool False) ()) ())) ()) ()

exIf1 = If "een" (Con (Bool True) ()) (Con (Int 3) ()) (Con (Int (-3)) () ) ()
exIf2 = Abs (Name "x") (If "twee" (Var (Name "x") ()) (Con (Int 3) ()) (Con (Int (-3)) ()) ()) ()
exIf2App = App exIf2 (Con (Bool True) ()) ()
exIf3 = Abs (Name "x") (If "twee" (Var (Name "x") ()) (Con (Bool False) ()) (Var (Name "x") ()) ()) ()
exIf3App = App exIf3 (Con (Bool True) ()) ()

exOp1 = Op LEQ (Con (Int 5) ()) (Con (Int 6) ()) ()
exOp2 = Abs (Name "x") (Abs (Name "y") (Op ADD (Var (Name "x") ()) (Var (Name "y") ()) ()) ()) ()


-- * Polyvariance

crash = Con (ExnC "q" Crash) ()

exIdPoison = Let (Name "id") (Abs (Name "x") (Var (Name "x") ()) ()) (Pair (App (Var (Name "id") ()) (crash) ()) (App (Var (Name "id") ()) (Con (Bool True) ()) ()) ()) ()

-- * Conditionals

ex17 = App (Abs (Name "x") (If "if" (Var (Name "x") ()) crash (Con (Bool True) ()) ()) ()) (Con (Bool False) ()) ()

-- * Complex functions

testList = Cons (Con (Int 1) ()) (Cons (Con (Int 2) ()) (Cons (Con (Int 3) ()) (Nil ()) ()) ()) ()

exLength = Fix (Name "length'") (Abs (Name "xs") (Case "case" (Var (Name "xs") ()) (Just (Con (Int 0) ())) (Just ((Name "a"), (Name "as"), Op ADD (Con (Int 1) ()) (App (Var (Name "length'") ()) (Var (Name "as") ()) ()) ())) ()) ()) ()

exLengthApp = Let (Name "length") exLength (App (Var (Name "length") ()) testList ()) ()

exMap = Fix (Name "map'") (Abs (Name "fM") (Abs (Name "xxsM") (Case "caseM" (Var (Name "xxsM") ()) (Just (Nil ())) (Just (Name "xM", Name "xsM", Cons (App (Var (Name "fM") ()) (Var (Name "xM") ()) ()) (App (App (Var (Name "map'") ()) (Var (Name "fM") ()) ()) (Var (Name "xsM") ()) ()) ())) ()) ()) ()) ()

exMap' = Fix (Name "map'2") (Abs (Name "fM2") (Abs (Name "xxsM2") (Case "caseM2" (Var (Name "xxsM2") ()) (Just (Nil ())) (Just (Name "xM2", Name "xsM2", Cons (App (Var (Name "fM2") ()) (Var (Name "xM2") ()) ()) (App (App (Var (Name "map'2") ()) (Var (Name "fM2") ()) ()) (Var (Name "xsM2") ()) ()) ())) ()) ()) ()) ()

exPlus1 = Abs (Name "n") (Op ADD (Var (Name "n") ()) (Con (Int 1) ()) ()) ()

exMapPlus1_Fix = App (App exMap exPlus1 ()) testList ()

exMapPlus1_Let = Let (Name "map") exMap (App (App (Var (Name "map") ()) exPlus1 ()) testList ()) ()

exMapLength_ xs = Let (Name "map") exMap (Let (Name "length") exLength (App (App (Var (Name "map") ()) (Var (Name "length") ()) ()) xs ()) ()) ()

exMapLengthE = exMapLength_ (Nil ())
exMapLengthNE = exMapLength_ (toExpr ([[1,2,3],[],[4]] :: [[Int]]))

exR0 = Let (Name "r1") (Abs (Name "a") (Abs (Name "b") (Abs (Name "c") (If "b" (Var (Name "b") ()) (Cons (Cons (Var (Name "c") ()) (Snd (Var (Name "a") ()) ()) ()) (Fst (Var (Name "a") ()) ()) ()) (Cons (Cons (Var (Name "c") ()) (Nil ()) ()) (Cons (Snd (Var (Name "a") ()) ()) (Fst (Var (Name "a") ()) ()) ()) ()) ()) ()) ()) ())
       (Let (Name "r2") (Abs (Name "d") (Case "d" (Var (Name "d") ()) (Nothing) (Just (Name "e",Name "es",Pair (Var (Name "es") ()) (Var (Name "e") ()) ())) ()) ())
       (Let (Name "rl") (Fix (Name "rf") (Pair (Abs (Name "u") (Case "u" (Var (Name "u") ()) (Just (Nil ())) (Just (Name "v",Name "vs",Case "vs" (Var (Name "vs") ()) (Just (Cons (Cons (Var (Name "v") ()) (Nil ()) ()) (Nil ()) ())) (Just (Name "w",Name "ws",App (App (App (Var (Name "r1") ()) (App (App (Snd (Var (Name "rf") ()) ()) (Var (Name "w") ()) ()) (Var (Name "ws") ()) ()) ()) (Op LEQ (Var (Name "v") ()) (Var (Name "w") ()) ()) ()) (Var (Name "v") ()) ())) ())) ()) ()) (Abs (Name "x") (Abs (Name "y") (App (Var (Name "r2") ()) (App (Fst (Var (Name "rf") ()) ()) (Cons (Var (Name "x") ()) (Var (Name "y") ()) ()) ()) ()) ()) ()) ()) ())
       (Fst (Var (Name "rl") ()) ())
     ()) ()) ()

exR_ b = Let (Name "r1") (Abs (Name "a") (Abs (Name "b") (Abs (Name "c") (If "b" (Var (Name "b") ()) (Cons (Cons (Var (Name "c") ()) (Snd (Var (Name "a") ()) ()) ()) (Fst (Var (Name "a") ()) ()) ()) (Cons (Cons (Var (Name "c") ()) (Nil ()) ()) (Cons (Snd (Var (Name "a") ()) ()) (Fst (Var (Name "a") ()) ()) ()) ()) ()) ()) ()) ())
       (Let (Name "r2") (Abs (Name "d") (Case "d" (Var (Name "d") ()) (Nothing) (Just (Name "e",Name "es",Pair (Var (Name "es") ()) (Var (Name "e") ()) ())) ()) ())
       (Let (Name "rl") (Fix (Name "rf") (Pair (Abs (Name "u") (Case "u" (Var (Name "u") ()) (Just (Nil ())) (Just (Name "v",Name "vs",Case "vs" (Var (Name "vs") ()) (Just (Cons (Cons (Var (Name "v") ()) (Nil ()) ()) (Nil ()) ())) (Just (Name "w",Name "ws",App (App (App (Var (Name "r1") ()) (App (App (Snd (Var (Name "rf") ()) ()) (Var (Name "w") ()) ()) (Var (Name "ws") ()) ()) ()) (Op LEQ (Var (Name "v") ()) (Var (Name "w") ()) ()) ()) (Var (Name "v") ()) ())) ())) ()) ()) (Abs (Name "x") (Abs (Name "y") (App (Var (Name "r2") ()) (App (Fst (Var (Name "rf") ()) ()) (Cons (Var (Name "x") ()) (Var (Name "y") ()) ()) ()) ()) ()) ()) ()) ())
       (If "if" (Con (Bool b) ())
        (App (Fst (Var (Name "rl") ()) ()) (Nil ()) ())
        (App (Fst (Var (Name "rl") ()) ()) (Cons (Con (Int 2) ()) (Cons (Con (Int 3) ()) (Cons (Con (Int 1) ()) (Nil ()) ()) ()) ()) ())
        ())
     ()) ()) ()
     
exR1 = exR_ False
exR2 = exR_ True

listOfNonEmptyLists = toExpr ([[1,2,3],[4,5,6],[7,8,9]] :: [[Int]])
someList = toExpr ([[1,5,4,3,5,7,3,2,5],[5,6,5,3],[],[7],[3,5,6,3,5]] :: [[Int]])
crashingList = Cons (Con (Int 0) ()) (Cons (Con (ExnC "q" Crash) ()) (Cons (Con (Int 1) ()) (Nil ()) ()) ()) ()

exMapRisers
    = Let
        (Name "map")
        exMap
        (Let
            (Name "risers")
            exR0
            (App
                (App
                    (Var (Name "map") ())
                    (Var (Name "risers") ())
                    ()
                )
                someList
                ()
            )
            ()
        )
        ()
        
exHead = Abs (Name "xxsH") (Case "caseH" (Var (Name "xxsH") ()) (Nothing) (Just (Name "xH",Name "xsH",Var (Name "xH") ())) ()) ()

exHeadNil = App exHead (Nil ()) ()

exMapHead_ xs = Let (Name "map") exMap (Let (Name "head") exHead (App (App (Var (Name "map") ()) (Var (Name "head") ()) ()) xs ()) ()) ()

exMapHeadNE = exMapHead_ listOfNonEmptyLists
exMapHeadE  = exMapHead_ someList

exMapHeadMapRisers
    = Let
        (Name "map1")   -- FIXME: no polymorphism in the underlying language...
        exMap
        (Let
            (Name "map2")
            exMap'
            (Let
                (Name "head")
                exHead
                (Let
                    (Name "risers")
                    exR0
                    (App
                        (App
                            (Var (Name "map1") ())
                            (Var (Name "head") ())
                            ()
                        )
                        (App
                            (App
                                (Var (Name "map2") ())
                                (Var (Name "risers") ())
                                ()
                            )
                            someList
                            ()
                        )
                        ()
                    )
                    ()
                )
                ()
            )
            ()
        )
        ()
