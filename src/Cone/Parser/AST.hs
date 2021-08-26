{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Cone.Parser.AST where

import Control.Lens
import Control.Lens.Plated
import Data.Data.Lens (uniplate)
import Data.Data
import Data.Maybe

type NamePath = [String]

data Attr = String
          | Int
          | Bool
              deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated Attr where
  plate = uniplate

data Location = Location{_fileName :: String, _lineNo :: !Int, _colNo :: !Int}
                  deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated Location where
  plate = uniplate

type NamedAttr = (String, Attr)

data PrimType = I8
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
                  deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated PrimType where
  plate = uniplate

data Type = TPrim{_tprim :: PrimType, _tloc :: Location}
          | TVar{_tvar :: String, _tloc :: Location}
          | TFunc{_tfuncArgs :: [Type], _tfuncEff :: Maybe EffectType,
                  _tfuncResult :: Type, _tloc :: Location}
          | TApp{_tappName :: NamePath, _tappArgs :: [Type], _tloc :: Location}
          | TAnn{_tannType :: Type, _tannKind :: Kind, _tloc :: Location}
              deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated Type where
  plate = uniplate

data Kind = KStar{_kloc :: Location}
          | KFunc{_kfuncArgs :: [Kind], _kfuncResult :: Kind, _kloc :: Location}
              deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated Kind where
  plate = uniplate

data EffKind = EKStar{_ekloc :: Location}
             | EKFunc{_ekfuncArgs :: [Kind], _ekfuncResult :: EffKind,
                      _ekloc :: Location}
                 deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated EffKind where
  plate = uniplate

data EffectType = EffVar{_effVarName :: String, _effLoc :: Location}
                | EffApp{_effAppName :: NamePath, _effAppArgs :: [Type],
                         _effLoc :: Location}
                | EffList{_effList :: [EffectType], _effLoc :: Location}
                | EffAnn{_effAnnType :: EffectType, _effAnnKind :: EffKind,
                         _effLoc :: Location}
                    deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated EffectType where
  plate = uniplate

data Pattern = PVar{_pvarName :: String, _ploc :: Location}
             | PApp{_pappName :: NamePath, _pappArgs :: [Pattern],
                    _ploc :: Location}
             | PAnn{_pannPattern :: Pattern, _pannType :: Type,
                    _ploc :: Location}
                 deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated Pattern where
  plate = uniplate

data Expr = EVar{_evarName :: NamePath, _eloc :: Location}
          | ELam{_elamArgs :: [(String, Type)], _elamEffType :: Maybe EffectType,
                 _elamResultType :: Type, _elamExpr :: Expr,
                 _eloc :: Location}
          | ECase{_ecaseExpr :: Expr, _ecaseBody :: [Case], _eloc :: Location}
          | EApp{_eappFunc :: Expr, _eappArgs :: [Expr], _eloc :: Location}
          | ELet{_eletVars :: [(String, Expr)], _eletBody :: Expr,
                 _eloc :: Location}
          | EHandle{_ehandleExpr :: Expr, _ehandleBindings :: [FuncDef],
                    _eloc :: Location}
          -- | ESeq{_eseq :: [Expr], _eloc :: Location}
          | EAnn{_eannExpr :: Expr, _eannType :: Type, _eloc :: Location}
              deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated Expr where
  plate = uniplate

data Case = Case{_casePattern :: Maybe Pattern, _caseGuard :: Maybe Expr,
                 _caseExpr :: Expr, _caseLoc :: Location}
              deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated Case where
  plate = uniplate

data TypeDef = TypeDef{_typeName :: String, _typeArgs :: [(String, Maybe Kind)],
                       _typeCons :: [TypeCon], _typeLoc :: Location}
                 deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated TypeDef where
  plate = uniplate

data TypeCon = TypeCon{_typeConName :: String, _typeConArgs :: [Type],
                       _typeConLoc :: Location}
                 deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated TypeCon where
  plate = uniplate

data EffectDef = EffectDef{_effectName :: String,
                           _effectArgs :: [(String, Maybe Kind)],
                           _effectIntfs :: [FuncDef], _effectLoc :: Location}
                   deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated EffectDef where
  plate = uniplate

data ImportStmt = ImportStmt{_importPath :: NamePath,
                             _importAlias :: Maybe String,
                             _importAttrs :: [NamedAttr],
                             _importLoc :: Location}
                    deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated ImportStmt where
  plate = uniplate

data FuncDef = FuncDef{_funcName :: String, _funcArgs :: [(String, Type)],
                       _funcEffectType :: Maybe EffectType, _funcResultType :: Type,
                       _funcExpr :: Expr, _funcLoc :: Location}
                 deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated FuncDef where
  plate = uniplate

data TopStmt = FDef{_fdef :: FuncDef}
             | TDef{_tdef :: TypeDef}
             | EDef{_edef :: EffectDef}
                 deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated TopStmt where
  plate = uniplate

data Module = Module{_moduleName :: NamePath, _moduleAttrs :: [NamedAttr],
                     _moduleExports :: [String],
                     _imports :: [ImportStmt], _topStmts :: [TopStmt],
                     _moduleLoc :: Location}
                deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Plated Module where
  plate = uniplate

makeLenses ''Attr

makePrisms ''Attr

makeLenses ''Location

makePrisms ''Location

makeLenses ''Type

makePrisms ''Type

makeLenses ''Kind

makePrisms ''Kind

makeLenses ''EffKind

makePrisms ''EffKind

makeLenses ''EffectType

makePrisms ''EffectType

makeLenses ''Pattern

makePrisms ''Pattern

makeLenses ''Expr

makePrisms ''Expr

makeLenses ''Case

makePrisms ''Case

makeLenses ''TypeDef

makePrisms ''TypeDef

makeLenses ''TypeCon

makePrisms ''TypeCon

makeLenses ''EffectDef

makePrisms ''EffectDef

makeLenses ''ImportStmt

makePrisms ''ImportStmt

makeLenses ''FuncDef

makePrisms ''FuncDef

makeLenses ''TopStmt

makePrisms ''TopStmt

makeLenses ''Module

makePrisms ''Module
