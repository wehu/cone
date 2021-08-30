{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Cone.Parser.AST where

import Control.Lens
import Control.Lens.Plated
import Data.Data
import Data.Data.Lens (uniplate)
import Data.Maybe
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name
import Prettyprinter

deriving instance Data a => Data (Name a)

deriving instance Read a => Read (Name a)

deriving instance (Data a, Data b) => Data (Bind a b)

deriving instance (Read a, Read b) => Read (Bind a b)

deriving instance (Eq a, Eq b) => Eq (Bind a b)

deriving instance (Ord a, Ord b) => Ord (Bind a b)

instance Semigroup (Name a) where
  (<>) a b = s2n $ name2String a ++ name2String b

instance Monoid (Name a) where
  mempty = s2n ""

ppr :: Pretty a => a -> String
ppr = show . pretty

type NamePath = String

data Attr
  = String
  | Int
  | Bool
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Attr where
  pretty = pretty . show

data Location = Location {_fileName :: String, _lineNo :: !Int, _colNo :: !Int}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Location where
  pretty l = pretty $ "@" ++ (_fileName l) ++ "[" ++ (show $ _lineNo l) ++ ", " ++ (show $ _colNo l) ++ "]"

type NamedAttr = (String, Attr)

data PrimType
  = I8
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
  | Str
  | Ch
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty PrimType where
  pretty = pretty . show

type TVar = Name Type

instance Show a => Pretty (Name a) where
  pretty = pretty . show

data Type
  = TPrim {_tprim :: PrimType, _tloc :: Location}
  | TVar {_tvar :: TVar, _tloc :: Location}
  | TFunc
      { _tfuncArgs :: [Type],
        _tfuncEff :: Maybe EffectType,
        _tfuncResult :: Type,
        _tloc :: Location
      }
  | TApp {_tappName :: TVar, _tappArgs :: [Type], _tloc :: Location}
  | TAnn {_tannType :: Type, _tannKind :: Kind, _tloc :: Location}
  | BoundType {_boundType :: Bind [TVar] Type}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Type where
  pretty TPrim{..} = pretty _tprim <+> pretty _tloc
  pretty TVar{..} = pretty _tvar <+> pretty _tloc
  pretty TFunc{..} = (encloseSep lparen rparen comma (map pretty _tfuncArgs)) <+> "->" <+> colon <+> pretty _tfuncEff <+> pretty _tfuncResult <+> pretty _tloc
  pretty TApp{..} = pretty _tappName <+> (encloseSep lparen rparen comma $ map pretty _tappArgs) <+> pretty _tloc
  pretty TAnn{..} = pretty _tannType <+> colon <+> pretty _tannKind <+> pretty _tloc
  pretty (BoundType (B tvars t)) = (encloseSep lbracket rbracket comma (map pretty tvars)) <+> colon <+> pretty t

data Kind
  = KStar {_kloc :: Location}
  | KFunc {_kfuncArgs :: [Kind], _kfuncResult :: Kind, _kloc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Kind where
  pretty KStar {..} = "*" <+> pretty _kloc
  pretty KFunc {..} = (encloseSep lparen rparen comma $ map pretty _kfuncArgs) <+> "->" <+> pretty _kfuncResult <+> pretty _kloc

data EffKind
  = EKStar {_ekloc :: Location}
  | EKFunc
      { _ekfuncArgs :: [Kind],
        _ekfuncResult :: EffKind,
        _ekloc :: Location
      }
  | EKList {_ekList :: [EffKind], _ekloc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty EffKind where
  pretty EKStar{..} = "*" <+> pretty _ekloc
  pretty EKFunc{..} = (encloseSep lparen rparen comma $ map pretty _ekfuncArgs) <+> "->" <+> pretty _ekfuncResult <+> pretty _ekloc
  pretty EKList{..} = (encloseSep langle rangle comma $ map pretty _ekList) <+> pretty _ekloc

data EffectType
  = EffTotal {_effLoc :: Location}
  | EffVar {_effVarName :: TVar, _effLoc :: Location}
  | EffApp
      { _effAppName :: TVar,
        _effAppArgs :: [Type],
        _effLoc :: Location
      }
  | EffList {_effList :: [EffectType], _effLoc :: Location}
  | EffAnn
      { _effAnnType :: EffectType,
        _effAnnKind :: EffKind,
        _effLoc :: Location
      }
  | BoundEffType {_boundEffType :: Bind [TVar] EffectType}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty EffectType where
  pretty EffTotal{..} = "total" <+> pretty _effLoc
  pretty EffVar{..} = pretty _effVarName <+> pretty _effLoc
  pretty EffApp{..} = pretty _effAppName <+> (encloseSep lparen rparen comma $ map pretty _effAppArgs) <+> pretty _effLoc
  pretty EffList{..} = (encloseSep langle rangle comma $ map pretty _effList) <+> pretty _effLoc
  pretty EffAnn{..} = pretty _effAnnType <+> colon <+> pretty _effAnnKind <+> pretty _effLoc
  pretty (BoundEffType (B tvars e)) = (encloseSep lbracket rbracket comma (map pretty tvars)) <+> colon <+> pretty e

data Pattern
  = PVar {_pvarName :: String, _ploc :: Location}
  | PApp
      { _pappName :: NamePath,
        _pappArgs :: [Pattern],
        _ploc :: Location
      }
  | PAnn
      { _pannPattern :: Pattern,
        _pannType :: Type,
        _ploc :: Location
      }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

data Expr
  = EVar {_evarName :: NamePath, _eloc :: Location}
  | ELit {_lit :: String, _litType :: Type, _eloc :: Location}
  | ELam
      { _elamBoundVars :: [TVar],
        _elamArgs :: [(String, Maybe Type)],
        _elamEffType :: Maybe EffectType,
        _elamResultType :: Maybe Type,
        _elamExpr :: Maybe Expr,
        _eloc :: Location
      }
  | ECase {_ecaseExpr :: Expr, _ecaseBody :: [Case], _eloc :: Location}
  | EApp {_eappFunc :: Expr, _eappArgs :: [Expr], _eloc :: Location}
  | ELet
      { _eletVars :: [(String, Expr)],
        _eletBody :: Expr,
        _eloc :: Location
      }
  | EHandle
      { _ehandleExpr :: Expr,
        _ehandleBindings :: [FuncDef],
        _eloc :: Location
      }
  | -- | ESeq{_eseq :: [Expr], _eloc :: Location}
    EAnn {_eannExpr :: Expr, _eannType :: Type, _eloc :: Location}
  deriving
    ( -- | BoundExpr{_exprBound :: Bind [TVar] Expr}
      Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

data Case = Case
  { _casePattern :: Maybe Pattern,
    _caseGuard :: Maybe Expr,
    _caseExpr :: Expr,
    _caseLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

data TypeDef = TypeDef
  { _typeName :: String,
    _typeArgs :: [(TVar, Maybe Kind)],
    _typeCons :: [TypeCon],
    _typeLoc :: Location
  }
  deriving
    ( -- | BoundTypeDef{_typeBound :: Bind [TVar] TypeDef}
      Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

data TypeCon = TypeCon
  { _typeConName :: String,
    _typeConArgs :: [Type],
    _typeConLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

data FuncIntf = FuncIntf
  { _intfName :: String,
    _intfBoundVars :: [TVar],
    _intfArgs :: [Type],
    _intfResultType :: Type,
    _intfLoc :: Location
  }
  deriving
    ( -- | BoundFuncIntf{_intfBound :: Bind [TVar] FuncIntf}
      Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

data EffectDef = EffectDef
  { _effectName :: String,
    _effectArgs :: [(TVar, Maybe Kind)],
    _effectIntfs :: [FuncIntf],
    _effectLoc :: Location
  }
  deriving
    ( -- | BoundEffectDef{_effectBound :: Bind [TVar] EffectDef}
      Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

data ImportStmt = ImportStmt
  { _importPath :: NamePath,
    _importAlias :: Maybe String,
    _importAttrs :: [NamedAttr],
    _importLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

data FuncDef = FuncDef
  { _funcName :: String,
    _funcBoundVars :: [TVar],
    _funcArgs :: [(String, Maybe Type)],
    _funcEffectType :: Maybe EffectType,
    _funcResultType :: Maybe Type,
    _funcExpr :: Maybe Expr,
    _funcLoc :: Location
  }
  deriving
    ( -- | BoundFuncDef{_funcBound :: Bind [TVar] FuncDef}
      Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

data TopStmt
  = FDef {_fdef :: FuncDef}
  | TDef {_tdef :: TypeDef}
  | EDef {_edef :: EffectDef}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

data Module = Module
  { _moduleName :: NamePath,
    _moduleAttrs :: [NamedAttr],
    _moduleExports :: [String],
    _imports :: [ImportStmt],
    _topStmts :: [TopStmt],
    _moduleLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

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

instance Alpha Location where
  aeq' _ctx i j = True

  fvAny' _ctx _nfn i = pure i

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = EQ

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
  isvar _ = Nothing

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
