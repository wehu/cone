{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cone.Parser.AST where

import Control.Lens
import Control.Lens.Plated
import Data.Data.Lens (uniplate)
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Data
import Data.Maybe

deriving instance Data a => Data (Name a)
deriving instance Read a => Read (Name a)

instance Semigroup (Name a) where
  (<>) a b = s2n $ name2String a ++ name2String b

instance Monoid (Name a) where
  mempty = s2n ""

type NamePath = String

data Attr = String
          | Int
          | Bool
              deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data Location = Location{_fileName :: String, _lineNo :: !Int, _colNo :: !Int}
                  deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

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
                  deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

type TVar = Name Type

data Type = TPrim{_tprim :: PrimType, _tloc :: Location}
          | TVar{_tvar :: TVar, _tloc :: Location}
          | TFunc{_tfuncArgs :: [Type], _tfuncEff :: Maybe EffectType,
                  _tfuncResult :: Type, _tloc :: Location}
          | TApp{_tappName :: TVar, _tappArgs :: [Type], _tloc :: Location}
          | TAnn{_tannType :: Type, _tannKind :: Kind, _tloc :: Location}
              deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data Kind = KStar{_kloc :: Location}
          | KFunc{_kfuncArgs :: [Kind], _kfuncResult :: Kind, _kloc :: Location}
              deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data EffKind = EKStar{_ekloc :: Location}
             | EKFunc{_ekfuncArgs :: [Kind], _ekfuncResult :: EffKind,
                      _ekloc :: Location}
                 deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data EffectType = EffVar{_effVarName :: String, _effLoc :: Location}
                | EffApp{_effAppName :: NamePath, _effAppArgs :: [Type],
                         _effLoc :: Location}
                | EffList{_effList :: [EffectType], _effLoc :: Location}
                | EffAnn{_effAnnType :: EffectType, _effAnnKind :: EffKind,
                         _effLoc :: Location}
                    deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data Pattern = PVar{_pvarName :: String, _ploc :: Location}
             | PApp{_pappName :: NamePath, _pappArgs :: [Pattern],
                    _ploc :: Location}
             | PAnn{_pannPattern :: Pattern, _pannType :: Type,
                    _ploc :: Location}
                 deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data Expr = EVar{_evarName :: NamePath, _eloc :: Location}
          | ELam{_elamBoundVars :: [TVar], _elamArgs :: [(String, Maybe Type)], _elamEffType :: Maybe EffectType,
                 _elamResultType :: Maybe Type, _elamExpr :: Maybe Expr,
                 _eloc :: Location}
          | ECase{_ecaseExpr :: Expr, _ecaseBody :: [Case], _eloc :: Location}
          | EApp{_eappFunc :: Expr, _eappArgs :: [Expr], _eloc :: Location}
          | ELet{_eletVars :: [(String, Expr)], _eletBody :: Expr,
                 _eloc :: Location}
          | EHandle{_ehandleExpr :: Expr, _ehandleBindings :: [FuncDef],
                    _eloc :: Location}
          -- | ESeq{_eseq :: [Expr], _eloc :: Location}
          | EAnn{_eannExpr :: Expr, _eannType :: Type, _eloc :: Location}
              deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data Case = Case{_casePattern :: Maybe Pattern, _caseGuard :: Maybe Expr,
                 _caseExpr :: Expr, _caseLoc :: Location}
              deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data TypeDef = TypeDef{_typeName :: String, _typeBoundVars :: [TVar], _typeArgs :: [(TVar, Maybe Kind)],
                       _typeCons :: [TypeCon], _typeLoc :: Location}
                 deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data TypeCon = TypeCon{_typeConName :: String, _typeConArgs :: [Type],
                       _typeConLoc :: Location}
                 deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data FuncIntf = FuncIntf{_intfName :: String, _intfBoundVars :: [TVar], _intfArgs :: [Type],
                         _intfResultType :: Type, _intfLoc :: Location}
                  deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data EffectDef = EffectDef{_effectName :: String,
                           _effectBoundVars :: [TVar],
                           _effectArgs :: [(TVar, Maybe Kind)],
                           _effectIntfs :: [FuncIntf], _effectLoc :: Location}
                   deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data ImportStmt = ImportStmt{_importPath :: NamePath,
                             _importAlias :: Maybe String,
                             _importAttrs :: [NamedAttr],
                             _importLoc :: Location}
                    deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data FuncDef = FuncDef{_funcName :: String, _funcBoundVars :: [TVar], _funcArgs :: [(String, Maybe Type)],
                       _funcEffectType :: Maybe EffectType, _funcResultType :: Maybe Type,
                       _funcExpr :: Maybe Expr, _funcLoc :: Location}
                 deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data TopStmt = FDef{_fdef :: FuncDef}
             | TDef{_tdef :: TypeDef}
             | EDef{_edef :: EffectDef}
                 deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

data Module = Module{_moduleName :: NamePath, _moduleAttrs :: [NamedAttr],
                     _moduleExports :: [String],
                     _imports :: [ImportStmt], _topStmts :: [TopStmt],
                     _moduleLoc :: Location}
                deriving (Eq,Ord,Show,Read,Data,Typeable,Generic)

-------------------------------

instance Plated Attr where
  plate = uniplate

instance Alpha Attr

instance Subst Type Attr

makeLenses ''Attr

makePrisms ''Attr

-------------------------------

instance Plated Location where
  plate = uniplate

instance Alpha Location

instance Subst Type Location

makeLenses ''Location

makePrisms ''Location

-------------------------------

instance Plated PrimType where
  plate = uniplate

instance Alpha PrimType

instance Subst Type PrimType

makeLenses ''PrimType

makePrisms ''PrimType

-------------------------------

instance Plated Type where
  plate = uniplate

instance Alpha Type

instance Subst Type Type where
  isvar (TVar x _) = Just (SubstName x)
  isvar _     = Nothing

makeLenses ''Type

makePrisms ''Type

-------------------------------

instance Plated Kind where
  plate = uniplate

instance Alpha Kind

instance Subst Type Kind

makeLenses ''Kind

makePrisms ''Kind

-------------------------------

instance Plated EffKind where
  plate = uniplate

instance Alpha EffKind

instance Subst Type EffKind

makeLenses ''EffKind

makePrisms ''EffKind

-------------------------------

instance Plated EffectType where
  plate = uniplate

instance Alpha EffectType

instance Subst Type EffectType

makeLenses ''EffectType

makePrisms ''EffectType

-------------------------------

instance Plated Pattern where
  plate = uniplate

instance Alpha Pattern

instance Subst Type Pattern

makeLenses ''Pattern

makePrisms ''Pattern

-------------------------------

instance Plated Expr where
  plate = uniplate

instance Alpha Expr

instance Subst Type Expr

makeLenses ''Expr

makePrisms ''Expr

-------------------------------

instance Plated Case where
  plate = uniplate

instance Alpha Case

instance Subst Type Case

makeLenses ''Case

makePrisms ''Case

-------------------------------

instance Plated TypeDef where
  plate = uniplate

instance Alpha TypeDef

instance Subst Type TypeDef

makeLenses ''TypeDef

makePrisms ''TypeDef

-------------------------------

instance Plated TypeCon where
  plate = uniplate

instance Alpha TypeCon

instance Subst Type TypeCon

makeLenses ''TypeCon

makePrisms ''TypeCon

-------------------------------

instance Plated EffectDef where
  plate = uniplate

instance Alpha EffectDef

instance Subst Type EffectDef

makeLenses ''EffectDef

makePrisms ''EffectDef

-------------------------------

instance Plated ImportStmt where
  plate = uniplate

instance Alpha ImportStmt

instance Subst Type ImportStmt

makeLenses ''ImportStmt

makePrisms ''ImportStmt

-------------------------------

instance Plated FuncIntf where
  plate = uniplate

instance Alpha FuncIntf

instance Subst Type FuncIntf

makeLenses ''FuncIntf

makePrisms ''FuncIntf

-------------------------------

instance Plated FuncDef where
  plate = uniplate

instance Alpha FuncDef

instance Subst Type FuncDef

makeLenses ''FuncDef

makePrisms ''FuncDef

-------------------------------

instance Plated TopStmt where
  plate = uniplate

instance Alpha TopStmt

instance Subst Type TopStmt

makeLenses ''TopStmt

makePrisms ''TopStmt

-------------------------------

instance Plated Module where
  plate = uniplate

instance Alpha Module

instance Subst Type Module

makeLenses ''Module

makePrisms ''Module

-------------------------------