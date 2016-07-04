([],(4,[
    START
        ([]
        ,[]
        ,[]
        ,[(F Mul [F' "f" [F' "c_1" []],F' "f" [F' "c_1" []]],F Mul [F' "f" [F' "c_0" []],F' "f" [F' "c_1" []]])])
,
    VA
        ([(F Mul [X' 0,X' 1],F Mul [X' 2,X' 3])]
        ,[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,F' "f" [F' "c_1" []])]
        ,[]
        ,[])
,
    E_Res { e_resIn = [(F Mul [X' 0,X' 1],F Mul [X' 2,X' 3])]
          , e_resOut = [(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]]),(X' 1,X' 1),(X' 2,X' 2),(X' 3,X' 3)]}
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])]
        ,[(X' 0,F' "f" [F' "c_1" []]),(X' 1,X' 1),(X' 1,F' "f" [F' "c_1" []]),(X' 2,X' 2),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 3),(X' 3,F' "f" [F' "c_1" []])]
        ,[]
        ,[])
,
    Var_Rep
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])]
        ,[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,X' 2),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 3),(X' 3,F' "f" [F' "c_1" []])]
        ,[]
        ,[])
,
    Var_Rep
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])]
        ,[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 3),(X' 3,F' "f" [F' "c_1" []])]
        ,[]
        ,[])
,
    Var_Rep
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])]
        ,[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,F' "f" [F' "c_1" []])]
        ,[]           --        ^ ------------- this is UNSOLVABLE, equivalent to the input problem.
        ,[])
,
    Mem_Init { mem_initX = X' 0
             , mem_initS = F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]]
             , mem_initT = F' "f" [F' "c_1" []]}
        ([]
        ,[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,F' "f" [F' "c_1" []])]
        ,[]
        ,[])
,
    Mem_Rec { mem_recGivenStack = [((F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]],X' 0),[X' 0])]
            , mem_recChosenZ = X' 3
            , mem_recChosenZFrom = [X' 0,X' 1,X' 2,X' 3]
            , mem_recSigma = [(X' 0,X' 0),(X' 1,F Mul [X' 2,F Mul [X' 3,F Inv [X' 0]]]),(X' 2,X' 2),(X' 3,X' 3)]
            , mem_recSigma' = []
            , mem_recTheta = [(X' 3,X' 0)]
            , mem_recYs = [X' 1]
            , mem_recStack' = [((F Mul [X' 2,F Mul [X' 0,F Inv [X' 0]]],X' 1),[X' 1,X' 0])]
            , mem_recStack'' = []}
        ([]
        ,[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 0),(X' 3,F' "f" [F' "c_1" []])]
        ,[]
        ,[])
                            --          v--------  f(c0)*f(c1)*f(c1)^-1=f(c1) <=> f(c0)=f(c1)  is still UNSOLVABLE.
    Mem_Rec { mem_recGivenStack = [((F Mul [X' 2,F Mul [X' 0,F Inv [X' 0]]],X' 1),[X' 1,X' 0])]
            , mem_recChosenZ = X' 0
            , mem_recChosenZFrom = [X' 0,X' 1,X' 2,X' 3]
            , mem_recSigma = [(X' 0,X' 0),(X' 1,X' 1),(X' 2,X' 1)]
            , mem_recSigma' = []
            , mem_recTheta = [(X' 0,X' 1)]
            , mem_recYs = []
            , mem_recStack' = []
            , mem_recStack'' = []}
        ([]
        ,[(X' 0,X' 1),(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 0),(X' 3,F' "f" [F' "c_1" []])]
        ,[]                     --    ^ ---------- this is SOLVABLE with the empty substitution, we've now thus lost critical information!
        ,[])
,
    Var_Rep
        ([]
        ,[(X' 1,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 1),(X' 3,F' "f" [F' "c_1" []])]
        ,[]
        ,[])
,
    Var_Rep
        ([]
        ,[(X' 1,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []])]
        ,[]
        ,[])
,
    Simplify
        ([]
        ,[(X' 1,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []])]
        ,[]
        ,[])
,
    E'_Res
        ([]
        ,[(X' 1,F' "f" [F' "c_1" []])]
        ,[]
        ,[])
,
    Simplify
        ([],[],[],[])
,
    SOLVED
        ([],[],[],[])
]))








--------------------------------------------------------------------------------------------------------------------------------------------------------------------








([],(4,[
    START
        ([],[],[],[(F Mul [F' "f" [F' "c_1" []],F' "f" [F' "c_1" []]],F Mul [F' "f" [F' "c_0" []],F' "f" [F' "c_1" []]])])
,
    VA
        ([(F Mul [X' 0,X' 1],F Mul [X' 2,X' 3])],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    E_Res {e_resIn = [(F Mul [X' 0,X' 1],F Mul [X' 2,X' 3])], e_resOut = [(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]]),(X' 1,X' 1),(X' 2,X' 2),(X' 3,X' 3)]}
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,X' 1),(X' 1,F' "f" [F' "c_1" []]),(X' 2,X' 2),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 3),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Var_Rep
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,X' 2),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 3),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Var_Rep
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 3),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Var_Rep
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Mem_Init {mem_initX = X' 0, mem_initS = F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]], mem_initT = F' "f" [F' "c_1" []]}
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Mem_Rec {mem_recGivenStack = [((F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]],X' 0),[X' 0])], mem_recChosenZ = X' 3, mem_recChosenZFrom = [X' 0,X' 1,X' 2,X' 3], mem_recSigma = [(X' 0,X' 0),(X' 1,F Mul [X' 2,F Mul [X' 3,F Inv [X' 0]]]),(X' 2,X' 2),(X' 3,X' 3)], mem_recSigma' = [], mem_recTheta = [(X' 3,X' 0)], mem_recYs = [X' 1], mem_recStack' = [((F Mul [X' 2,F Mul [X' 0,F Inv [X' 0]]],X' 1),[X' 1,X' 0])], mem_recStack'' = []}
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 0),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Mem_Rec {mem_recGivenStack = [((F Mul [X' 2,F Mul [X' 0,F Inv [X' 0]]],X' 1),[X' 1,X' 0])], mem_recChosenZ = X' 1, mem_recChosenZFrom = [X' 0,X' 1,X' 2,X' 3], mem_recSigma = [(X' 0,X' 0),(X' 1,X' 1),(X' 2,X' 1)], mem_recSigma' = [], mem_recTheta = [], mem_recYs = [], mem_recStack' = [], mem_recStack'' = []}
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 0),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Var_Rep
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []])],[],[])
,
    Simplify
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 0,F' "f" [F' "c_1" []])],[],[])
,
    E'_Res
        ([],[(X' 0,F' "f" [F' "c_1" []])],[],[])
,
    Simplify
        ([],[],[],[])
,
    SOLVED
        ([],[],[],[])
]))











--------------------------------------------------------------------------------------------------------------------------------------------------------------------
















([],(4,[
    START
        ([],[],[],[(F Mul [F' "f" [F' "c_1" []],F' "f" [F' "c_1" []]],F Mul [F' "f" [F' "c_0" []],F' "f" [F' "c_1" []]])])
,
    VA
        ([(F Mul [X' 0,X' 1],F Mul [X' 2,X' 3])],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    E_Res {e_resIn = [(F Mul [X' 0,X' 1],F Mul [X' 2,X' 3])], e_resOut = [(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]]),(X' 1,X' 1),(X' 2,X' 2),(X' 3,X' 3)]}
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,X' 1),(X' 1,F' "f" [F' "c_1" []]),(X' 2,X' 2),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 3),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Var_Rep
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,X' 2),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 3),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Var_Rep
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 3),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Var_Rep
        ([(X' 0,F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]])],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Mem_Init {mem_initX = X' 0, mem_initS = F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]], mem_initT = F' "f" [F' "c_1" []]}
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Mem_Rec {mem_recGivenStack = [((F Mul [F Inv [X' 1],F Mul [X' 2,X' 3]],X' 0),[X' 0])], mem_recChosenZ = X' 3, mem_recChosenZFrom = [X' 0,X' 1,X' 2,X' 3], mem_recSigma = [(X' 0,X' 0),(X' 1,F Mul [X' 2,F Mul [X' 3,F Inv [X' 0]]]),(X' 2,X' 2),(X' 3,X' 3)], mem_recSigma' = [], mem_recTheta = [(X' 3,X' 0)], mem_recYs = [X' 1], mem_recStack' = [((F Mul [X' 2,F Mul [X' 0,F Inv [X' 0]]],X' 1),[X' 1,X' 0])], mem_recStack'' = []}
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 0),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Mem_Rec {mem_recGivenStack = [((F Mul [X' 2,F Mul [X' 0,F Inv [X' 0]]],X' 1),[X' 1,X' 0])], mem_recChosenZ = X' 3, mem_recChosenZFrom = [X' 0,X' 1,X' 2,X' 3], mem_recSigma = [(X' 0,X' 0),(X' 1,X' 1),(X' 2,X' 1)], mem_recSigma' = [], mem_recTheta = [(X' 3,X' 1)], mem_recYs = [], mem_recStack' = [], mem_recStack'' = []}
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []]),(X' 3,X' 1),(X' 3,X' 0),(X' 3,F' "f" [F' "c_1" []])],[],[])
,
    Var_Rep
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 1,F' "f" [F' "c_1" []]),(X' 1,X' 0),(X' 1,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []])],[],[])
,
    Var_Rep
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 0,F' "f" [F' "c_1" []]),(X' 0,F' "f" [F' "c_1" []]),(X' 2,F' "f" [F' "c_0" []])],[],[])
,
    Simplify
        ([],[(X' 0,F' "f" [F' "c_1" []]),(X' 0,F' "f" [F' "c_1" []]),(X' 0,F' "f" [F' "c_1" []])],[],[])
,
    E'_Res
        ([],[(X' 0,F' "f" [F' "c_1" []])],[],[])
,
    Simplify
        ([],[],[],[])
,
    SOLVED
        ([],[],[],[])
]))

