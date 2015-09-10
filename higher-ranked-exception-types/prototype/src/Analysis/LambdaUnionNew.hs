module Analysis.LambdaUnionNew (
    module Analysis.LambdaUnionNew.Types,
    module Analysis.LambdaUnionNew.Reduce,
    module Analysis.LambdaUnionNew.Equality
) where

-- import Analysus.LambdaUnionOld.Syntax as Old
import Analysis.LambdaUnionNew.Types
import Analysis.LambdaUnionNew.Reduce
import Analysis.LambdaUnionNew.Equality

{-
upgradeTm :: Old.Tm a -> Tm
upgradeTm (Old.Var x)
    = undefined
upgradeTm (Old.Con c)
    = undefined
upgradeTm (Abs x s tm)
    = undefined
upgradeTm (App tm1 tm2)
    = undefined
upgradeTm (Union tm1 tm2)
    = let Tm tys1 tms1 = upgradeTm tm1
          Tm tys2 tms2 = upgradeTm tm2
       in if tys1 == tys2 then
            Tm tys1 (tms1 ++ tms2)
          else
            error "upgradeTm: Union"
upgradeTm (Empty)
    = Tm [{- don't know sort.. -}] []
-}
