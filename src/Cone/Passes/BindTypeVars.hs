module Cone.Passes.BindTypeVars () where

import Cone.Parser.AST
import Control.Lens
import Control.Lens.Plated
import Unbound.Generics.LocallyNameless

-- bindFuncDef :: FuncDef -> FuncDef
-- bindFuncDef f@(BoundFuncDef{}) = f
-- bindFuncDef f@(FuncDef{}) =
--            let vars = f ^. funcBoundVars
--             in BoundFuncDef (bind vars
--                (transformOn (funcExpr.traverse) bindExpr f))
--
-- bindExpr :: Expr -> Expr
-- bindExpr e = case e of
--     l@ELam{} -> BoundExpr $ bind (l ^. elamBoundVars) e
--     a@EApp{} ->  (transformOn eappFunc bindExpr)
--                . (transformOn (eappArgs.traverse) bindExpr) $ a
--     l@ELet{} ->  (transformOn (eletVars.traverse._2) bindExpr)
--                . (transformOn eletBody bindExpr) $ l
--     h@EHandle{} -> (transformOn ehandleExpr bindExpr)
--                . (transformOn (ehandleBindings.traverse) bindFuncDef) $ h
--     c@ECase{} -> (transformOn ecaseExpr bindExpr)
--                . (transformOn (ecaseBody.traverse) bindCase) $ c
--     a@EAnn{} -> transformOn eannExpr bindExpr a
--     _ -> e
--
-- bindCase :: Case -> Case
-- bindCase = (transformOn (casePattern.traverse) bindPattern)
--          . (transformOn (caseGuard.traverse) bindExpr)
--          . (transformOn caseExpr bindExpr)
--
-- bindPattern :: Pattern -> Pattern
-- bindPattern p = case p of
--     a@PAnn{} -> transformOn pannPattern bindPattern $ a
--     a@PApp{} -> transformOn (pappArgs.traverse) bindPattern $ a
--
-- bindTypeDef :: TypeDef -> TypeDef
-- bindTypeDef f@(BoundTypeDef{}) = f
-- bindTypeDef f@(TypeDef{}) =
--            let vars = f ^. typeBoundVars
--             in BoundTypeDef (bind vars f)
--
-- bindEffectDef :: EffectDef -> EffectDef
-- bindEffectDef f@(BoundEffectDef{}) = f
-- bindEffectDef f@(EffectDef{}) =
--            let vars = f ^. effectBoundVars
--             in BoundEffectDef (bind vars f)
--
-- bindTVars :: Module -> Module
-- bindTVars = (transformOn (topStmts.traverse._FDef) bindFuncDef)
--           . (transformOn (topStmts.traverse._TDef) bindTypeDef)
--           . (transformOn (topStmts.traverse._EDef) bindEffectDef)
