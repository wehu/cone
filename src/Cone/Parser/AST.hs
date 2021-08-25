{-# LANGUAGE TemplateHaskell #-}

module Cone.Parser.AST
       (NamePath, Location(..), Module(..), NamedAttr, Attr(..), TopStmt(..),
        FuncDef(..), Type(..), Kind(..), Case(..), Pattern(..), Expr(..),
        TypeDef(..), TypeCon(..), EffectDef(..), EffKind(..), EffectType(..),
        ImportStmt(..))
       where
import Control.Lens

import Data.Maybe

type NamePath = [String]

data Attr = String
          | Int
          | Bool
              deriving (Eq, Show)

data Location = Location{_fileName :: String, _lineNo :: !Int, _colNo :: !Int}
                  deriving (Eq, Show)

type NamedAttr = (String, Attr)

data Type = I8
          | I16
          | I32
          | I64
          | U8
          | U16
          | U32
          | U64
          | F16
          | F32
          | F64
          | BF16
          | Pred
          | TVar{_tvar :: String}
          | TFunc{_tfuncArgs :: [Type], _tfuncEff :: EffectType,
                  _tfuncResult :: Type}
          | TApp{_tappName :: NamePath, _tappArgs :: [Type]}
          | TAnn{_tannType :: Type, _tannKind :: Kind}
          | TLoc{_tlocType :: Type, _tloc :: Location}
              deriving (Eq, Show)

data Kind = KStar
          | KFunc{_kfuncArgs :: [Kind], _kfuncResult :: Kind}
          | KLoc{_klocKind :: Kind, _kloc :: Location}
              deriving (Eq, Show)

data EffKind = EKStar
             | EKFunc{_ekfuncArgs :: [Kind], _ekfuncResult :: EffKind}
             | EKLoc{_eklocKind :: EffKind, _ekloc :: Location}
                 deriving (Eq, Show)

data EffectType = EffVar{_effVarName :: String}
                | EffApp{_effAppName :: String, _effAppArgs :: [Type]}
                | EffList{_effList :: [EffectType]}
                | EffAnn{_effAnnType :: EffectType, _effAnnKind :: EffKind}
                | EffLoc{_effLocType :: EffectType, _effLoc :: Location}
                    deriving (Eq, Show)

data Pattern = PVar{_pvarName :: String}
             | PApp{_pappName :: NamePath, _pappArgs :: [Pattern]}
             | PAnn{_pannPattern :: Pattern, _pannType :: Type}
             | PLoc{_plocPattern :: Pattern, _ploc :: Location}
                 deriving (Eq, Show)

data Expr = EVar{_evarName :: NamePath}
          | ELam{_elamArgs :: [(String, Maybe Type)], _elamBody :: Expr}
          | ECase{_ecaseExpr :: Expr, _ecaseBody :: [Case]}
          | EApp{_eappFunc :: Expr, _eappArgs :: [Expr]}
          | ELet{_eletVars :: [(String, Expr)], _eletBody :: Expr}
          | EHandle{_ehandleExpr :: Expr, _ehandleBindings :: [FuncDef]}
          | ESeq{_eseq :: [Expr]}
          | EAnn{_eannExpr :: Expr, _eannType :: Type}
          | ELoc{_elocExpr :: Expr, _eloc :: Location}
              deriving (Eq, Show)

data Case = Case{_casePattern :: Maybe Pattern, _caseGuard :: Maybe Expr,
                 _caseExpr :: Expr, _caseLoc :: Location}
              deriving (Eq, Show)

data TypeDef = TypeDef{_typeName :: String, _typeArgs :: [(String, Maybe Kind)],
                       _typeCons :: [TypeCon], _typeLoc :: Location}
                 deriving (Eq, Show)

data TypeCon = TypeCon{_typeConName :: String, _typeConArgs :: [Type],
                       _typeConLoc :: Location}
                 deriving (Eq, Show)

data EffectDef = EffectDef{_effectName :: String,
                           _effectArgs :: [(String, Maybe Kind)],
                           _effectIntfs :: [FuncDef], _effectLoc :: Location}
                   deriving (Eq, Show)

data ImportStmt = ImportStmt{_importStmt :: NamePath,
                             _importAlias :: Maybe String,
                             _importAttrs :: [NamedAttr],
                             _importLoc :: Location}
                    deriving (Eq, Show)

data FuncDef = FuncDef{_funcName :: String, _funcArgs :: [(String, Type)],
                       _funcEffectType :: EffectType, _funcResultType :: Type,
                       _funcExpr :: Expr, _funcLoc :: Location}
                 deriving (Eq, Show)

data TopStmt = FDef{_fdef :: FuncDef}
             | TDef{_tdef :: TypeDef}
             | EDef{_edef :: EffectDef}
             | Import{_importS :: ImportStmt}
                 deriving (Eq, Show)

data Module = Module{_moduleName :: NamePath, _moduleAttrs :: [NamedAttr],
                     _moduleExports :: [String], _topStmts :: [TopStmt],
                     _moduleLoc :: Location}
                deriving (Eq, Show)

makeLenses ''Attr

makeLenses ''Location

makeLenses ''Type

makeLenses ''Kind

makeLenses ''EffKind

makeLenses ''EffectType

makeLenses ''Pattern

makeLenses ''Expr

makeLenses ''Case

makeLenses ''TypeDef

makeLenses ''TypeCon

makeLenses ''EffectDef

makeLenses ''ImportStmt

makeLenses ''FuncDef

makeLenses ''TopStmt

makeLenses ''Module
