-- for each, what are the rules applied/non-deterministic choices made?

-- WITHOUT SIMPLIFICATION
([(X 1,C 0),(X' 5,C 1)],[(X 0,X 1),(X' 0,F' "f" [X 1]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  1]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 1     NOT IDEMPOTENT ON X
([(X 1,C 0),(X' 5,C 1)],[          (X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  1]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 2     ???????????????????
([(X 1,C 0),(X' 5,C 1)],[          (X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  1]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 2     ???????????????????
([(X 1,C 0),(X' 5,C 1)],[(X 0,X 1),(X' 0,F' "f" [X 1]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  1]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 1     NOT IDEMPOTENT ON X
([(X 1,C 0),(X' 5,C 1)],[(X 0,X 1),(X' 0,F' "f" [X 1]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  1]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 1     NOT IDEMPOTENT ON X
([(X 1,C 0),(X' 5,C 1)],[(X 0,X 1),(X' 0,F' "f" [X 1]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  1]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 1     NOT IDEMPOTENT ON X
([(X 1,C 0),(X' 5,C 1)],[(X 0,X 1),(X' 0,F' "f" [X 1]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  1]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 1     NOT IDEMPOTENT ON X
([(X 0,C 0),(X' 5,C 1)],[          (X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  0]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 3     ???????????????????
([(X 0,C 0),(X' 5,C 1)],[(X 1,X 0),(X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 0]),(X' 2,F' "f" [X  0]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 4     NOT IDEMPOTENT ON X
([(X 0,C 0),(X  1,C 1)],[          (X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  0]),(X' 3,F' "f" [X  1])],[],[])    SOLUTION 1      -------------------
([(X 1,C 1),(X' 4,C 0)],[(X 0,X 1),(X' 0,F' "f" [X 1]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X' 4]),(X' 3,F' "f" [X  1])],[],[])    INCORRECT 5     NOT IDEMPOTENT ON X
([(X 0,C 1),(X' 4,C 0)],[          (X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X' 4]),(X' 3,F' "f" [X  0])],[],[])    INCORRECT 6     ???????????????????
([(X 0,C 1),(X  1,C 0)],[          (X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  1]),(X' 3,F' "f" [X  0])],[],[])    SOLUTION 2      -------------------
([(X 0,C 1),(X' 4,C 0)],[(X 1,X 0),(X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 0]),(X' 2,F' "f" [X' 4]),(X' 3,F' "f" [X  0])],[],[])    INCORRECT 7     NOT IDEMPOTENT ON X



-- WITH SIMPLIFICATION AND STRICTER SOLVED FORM (EXACTLY THE SOLUTION AND "QUESTION MARK" NON-SOLUTIONS...)
([(X 1,C 0),(X' 5,C 1)],[          (X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  1]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 2     ([(X 1,C 0)],[],[],[])
([(X 1,C 0),(X' 5,C 1)],[          (X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  1]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 2     ([(X 1,C 0)],[],[],[])
([(X 0,C 0),(X' 5,C 1)],[          (X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X  0]),(X' 3,F' "f" [X' 5])],[],[])    INCORRECT 3     ([(X 0,C 0)],[],[],[])
([(X 0,C 1),(X' 4,C 0)],[          (X' 0,F' "f" [X 0]),(X' 1,F' "f" [X 1]),(X' 2,F' "f" [X' 4]),(X' 3,F' "f" [X  0])],[],[])    INCORRECT 6     ([(X 0,C 1)],[],[],[])



--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


([(X 0,C 0),(X 1,C 0)],[],[],[])    INCORRECT 1
([(X 1,C 0)          ],[],[],[])    INCORRECT 2
([(X 1,C 0)          ],[],[],[])    INCORRECT 2
([(X 0,C 0),(X 1,C 0)],[],[],[])    INCORRECT 1
([(X 0,C 0),(X 1,C 0)],[],[],[])    INCORRECT 1
([(X 0,C 0),(X 1,C 0)],[],[],[])    INCORRECT 1
([(X 0,C 0),(X 1,C 0)],[],[],[])    INCORRECT 1
([(X 0,C 0)          ],[],[],[])    INCORRECT 3
([(X 0,C 0),(X 1,C 0)],[],[],[])    INCORRECT 1
([(X 0,C 0),(X 1,C 1)],[],[],[])    SOLUTION 1
([(X 0,C 1),(X 1,C 1)],[],[],[])    INCORRECT 4
([(X 0,C 1)          ],[],[],[])    INCORRECT 5
([(X 0,C 1),(X 1,C 0)],[],[],[])    SOLUTION 2
([(X 0,C 1),(X 1,C 1)],[],[],[])    INCORRECT 4


-- miscellaneous fixme's in several of the rules and helper functions...
-- can we get rid of the usual ones by the non-idempotent restriction? (why is this not a "problem" anymore? missing Elim?)
-- can we get rid of the remaining ones by being "less defined"?
