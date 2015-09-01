module PatternTyping where

import Data.Maybe
import Util.List

import Language.Haskell.Exts.Annotated

import Common
import Refinement

import Abstract.Int

-- | Pattern typing

-- TODO: Consider using a simpler reprentation for the type of constructors:
-- type Env     = [(Name, ConType)]
-- type ConType = ([Type], Type)

patternType :: Env -> Fresh -> Pat Phi -> (Type Phi, Env)
patternType conenv fresh pat
    = let (ty, env, cs) = patternType' conenv fresh pat
          subst         = unify cs
       in (subst $@ ty, subst $&& env)

-- *

patternType' :: Env -> Fresh -> Pat Phi -> (Type Phi, Env, [Constr])

patternType' env (f1:f2:_) (PVar _ name)
    = let freshTyVar = TyVar (Phi (RefVar f2)) f1
       in (freshTyVar, [(UnQual NoPhi name, freshTyVar)], [])
    
patternType' env fresh (PLit _ lit)
    = (literalType lit, [], [])
    
patternType' env fresh (PNeg _ lit)
    = patternType' env fresh lit
    
patternType' env fresh (PApp _ con ps)
    = let ((f1:f2:fs):fss) = splice (length ps + 1) fresh
          freshTyVar   = TyVar (Phi (RefVar f2)) f1
          conTy        = fst $ inst fs (fromJust $ lookup con env) -- NOTE: fst introduces after type-change of inst
          (ts, es, cs) = unzip3 (zipWith (patternType' env) fss ps)
          patTy        = foldr (TyFun (Phi RefLambda)) freshTyVar ts
       in (freshTyVar, concat es, (conTy =: patTy) : concat cs)

patternType' env fresh (PInfixApp phi p1 con p2)
    = patternType' env fresh (PApp phi con [p1, p2])

patternType' env (f:fresh) (PTuple _ ps)
    = let fs           = splice (length ps) fresh
          (ts, es, cs) = unzip3 (zipWith (patternType' env) fs ps)
       in (TyTuple (Phi (RefVar f)) Boxed ts, concat es, concat cs)

patternType' env (f1:f2:fresh) (PList _ ps)
    = let fss          = splice (length ps) fresh
          freshTyVar   = TyVar (Phi (RefVar f2)) f1
          (ts, es, cs) = unzip3 (zipWith (patternType' env) fss ps)
       in (freshTyVar, concat es, map (\t -> freshTyVar =: TyList (error "patternType': PList") t) ts ++ concat cs)
    
patternType' env fresh (PParen _ pat)
    = patternType' env fresh pat
    
patternType' env fresh (PRec _ _ _)
    = error "patternType': PRec"

patternType' env (f1:f2:fresh) (PAsPat _ name pat)
    = let freshTyVar = TyVar (Phi (RefVar f2)) f1
          (t, e, c)  = patternType' env fresh pat
       in (freshTyVar, (UnQual NoPhi name, freshTyVar) : e, (freshTyVar =: t) : c)

patternType' env (f1:f2:_) (PWildCard _)
    = let freshTyVar = TyVar (Phi (RefVar f2)) f1
       in (freshTyVar, [], [])

patternType' enf fresh (PIrrPat _ _)
    = error "patternType': PIrrPat"


-- | Constructor typing

dataDeclType :: Decl l -> Env
dataDeclType (DataDecl _ _ Nothing (DHead _ dataTypeName params) qualConDecls _)
    = map constructorType qualConDecls

    where constructorType :: QualConDecl l -> (QName Phi, Type Phi)
          constructorType (QualConDecl _ Nothing Nothing (ConDecl _ name bangTypes))
              = (UnQual NoPhi (stripNameAnn name), TyForall NoPhi (Just (map stripTyVarBindAnn params)) Nothing (foldr
                           (\(UnBangedTy _ ty) r -> TyFun NoPhi (stripTypeAnn ty) r)
                           (foldl (\r (UnkindedVar NoPhi name) -> TyApp NoPhi r (TyVar NoPhi name))
                                  (TyCon NoPhi (UnQual NoPhi (stripNameAnn dataTypeName)))
                                  (map stripTyVarBindAnn params)
                           )
                           bangTypes
                ))
          constructorType x
              = error ("constructorType: unexpected QualConDecl (" ++ prettyPrint x ++ ")")

-- | Literal typing

literalType :: Literal Phi -> Type Phi
literalType (Char   _ c _)
    = TyCon (Phi RefTop) (UnQual NoPhi (Ident NoPhi "Char"))
literalType (String _ s _)
    = TyList (Phi RefTop) (TyCon (Phi RefTop) (UnQual NoPhi (Ident NoPhi "Char")))
literalType (Int    _ i _)
    = TyCon (Phi (RefInt (injectInt i))) (UnQual NoPhi (Ident NoPhi "Int" ))


-- | Built-in constructors

-- TODO: TupleCon (arbitrary lenght), FunCon
-- TODO: not only constructors anymore...

builtinConstructors :: Env
builtinConstructors
    = [(UnQual NoPhi (Ident NoPhi "undefined"),
            TyForall NoPhi (Just [UnkindedVar NoPhi (Ident NoPhi "a")]) Nothing (TyVar NoPhi (Ident NoPhi "a"))
       )
      ,(UnQual NoPhi (Ident NoPhi "error"),
            TyForall NoPhi (Just [UnkindedVar NoPhi (Ident NoPhi "a")]) Nothing (TyFun NoPhi (TyList NoPhi (TyCon NoPhi (UnQual NoPhi (Ident NoPhi "Char")))) (TyVar NoPhi (Ident NoPhi "a")))

       )
      ,(Special NoPhi (UnitCon NoPhi), TyCon NoPhi (Special NoPhi (UnitCon NoPhi)))
      ,(Special NoPhi (ListCon NoPhi), TyCon NoPhi (Special NoPhi (ListCon NoPhi)))
      ,(Special NoPhi (Cons    NoPhi), TyForall NoPhi (Just [UnkindedVar NoPhi (Ident NoPhi "a")])
                                           Nothing
                                           (TyVar NoPhi (Ident NoPhi "a")
                                               `tf`
                                           ((TyList NoPhi (TyVar NoPhi (Ident NoPhi "a")))
                                               `tf`
                                            (TyList NoPhi (TyVar NoPhi (Ident NoPhi "a")))
                                           ))
       )
      ,(Special NoPhi (TupleCon NoPhi Boxed 2), tyTupleCon 2)
      ,(Special NoPhi (TupleCon NoPhi Boxed 3), tyTupleCon 3)
      ,(Special NoPhi (TupleCon NoPhi Boxed 4), tyTupleCon 4)
      ,(Special NoPhi (TupleCon NoPhi Boxed 5), tyTupleCon 5)
      ,(Special NoPhi (TupleCon NoPhi Boxed 6), tyTupleCon 6)
      ,(Special NoPhi (TupleCon NoPhi Boxed 7), tyTupleCon 7)
      ,(Special NoPhi (TupleCon NoPhi Boxed 8), tyTupleCon 8)
      ,(Special NoPhi (TupleCon NoPhi Boxed 9), tyTupleCon 9)
      ]
    where tf = TyFun NoPhi

tyTupleCon :: Int -> Type Phi
tyTupleCon n
    = let ns = map (\n -> Ident NoPhi ("t" ++ show n)) [1..n]
          ts = map (TyVar NoPhi) ns
       in TyForall NoPhi
                   (Just (map (UnkindedVar NoPhi) ns))
                   Nothing
                   (foldr (TyFun NoPhi) (TyTuple NoPhi Boxed ts) ts)
