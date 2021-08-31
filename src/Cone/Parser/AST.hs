{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Cone.Parser.AST where

import Control.Lens
import Control.Lens.Plated
import Data.Data
import Data.Data.Lens (uniplate)
import Data.Maybe
import GHC.Generics (Generic)
import Prettyprinter
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Name

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
  pretty l = "" -- pretty $ "@" ++ (_fileName l) ++ "[" ++ (show $ _lineNo l) ++ ", " ++ (show $ _colNo l) ++ "]"

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
  pretty I8 = "i8"
  pretty I16 = "i16"
  pretty I32 = "i32"
  pretty I64 = "i64"
  pretty U8 = "u8"
  pretty U16 = "u16"
  pretty U32 = "u32"
  pretty U64 = "u64"
  pretty F16 = "f16"
  pretty F32 = "f32"
  pretty F64 = "f64"
  pretty BF16 = "bf16"
  pretty Pred = "bool"
  pretty Str = "str"
  pretty Ch = "char"

type TVar = Name Type

instance Show a => Pretty (Name a) where
  pretty = pretty . show

parensList :: Pretty a => forall ann. [a] -> Doc ann
parensList ls = encloseSep lparen rparen comma $ map pretty ls

bracketsList :: Pretty a => forall ann. [a] -> Doc ann
bracketsList ls = encloseSep lbracket rbracket comma $ map pretty ls

anglesList :: Pretty a => forall ann. [a] -> Doc ann
anglesList ls = encloseSep langle rangle comma $ map pretty ls

bracesList :: Pretty a => forall ann. [a] -> Doc ann
bracesList ls = encloseSep lbrace rbrace semi $ map pretty ls

parensList' :: [Doc ann] -> Doc ann
parensList' ls = encloseSep lparen rparen comma ls

bracketsList' :: [Doc ann] -> Doc ann
bracketsList' ls = encloseSep lbracket rbracket comma ls

anglesList' :: [Doc ann] -> Doc ann
anglesList' ls = encloseSep langle rangle comma ls

bracesList' :: [Doc ann] -> Doc ann
bracesList' ls = encloseSep lbrace rbrace semi ls

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
  pretty TPrim {..} = pretty _tprim <+> pretty _tloc
  pretty TVar {..} = pretty _tvar <+> pretty _tloc
  pretty TFunc {..} = parens $ parensList _tfuncArgs <+> "->" <+> colon <+> pretty _tfuncEff <+> pretty _tfuncResult <+> pretty _tloc
  pretty TApp {..} = parens $ pretty _tappName <+> parensList _tappArgs <+> pretty _tloc
  pretty TAnn {..} = parens $ pretty _tannType <+> colon <+> pretty _tannKind <+> pretty _tloc
  pretty (BoundType (B tvars t)) = parens $ bracketsList tvars <+> colon <+> pretty t

data Kind
  = KStar {_kloc :: Location}
  | KFunc {_kfuncArgs :: [Kind], _kfuncResult :: Kind, _kloc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Kind where
  pretty KStar {..} = "*" <+> pretty _kloc
  pretty KFunc {..} = parens $ parensList _kfuncArgs <+> "->" <+> pretty _kfuncResult <+> pretty _kloc

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
  pretty EKStar {..} = "*" <+> pretty _ekloc
  pretty EKFunc {..} = parens $ parensList _ekfuncArgs <+> "->" <+> pretty _ekfuncResult <+> pretty _ekloc
  pretty EKList {..} = anglesList _ekList <+> pretty _ekloc

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
  pretty EffTotal {..} = "total" <+> pretty _effLoc
  pretty EffVar {..} = pretty _effVarName <+> pretty _effLoc
  pretty EffApp {..} = parens $ pretty _effAppName <+> parensList _effAppArgs <+> pretty _effLoc
  pretty EffList {..} = anglesList _effList <+> pretty _effLoc
  pretty EffAnn {..} = parens $ pretty _effAnnType <+> colon <+> pretty _effAnnKind <+> pretty _effLoc
  pretty (BoundEffType (B tvars e)) = parens $ bracketsList tvars <+> colon <+> pretty e

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

instance Pretty Pattern where
  pretty PVar {..} = pretty _pvarName <+> pretty _ploc
  pretty PApp {..} = parens $ pretty _pappName <+> parensList _pappArgs <+> pretty _ploc
  pretty PAnn {..} = parens $ pretty _pannPattern <+> colon <+> pretty _pannType <+> pretty _ploc

data Case = Case
  { _casePattern :: Maybe Pattern,
    _caseGuard :: Maybe Expr,
    _caseExpr :: Expr,
    _caseLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Case where
  pretty Case {..} =
    parens $
      pretty _casePattern <+> "|"
        <+> pretty _caseGuard
        <+> "->"
        <+> pretty _caseExpr
        <+> pretty _caseLoc

data Expr
  = EVar {_evarName :: NamePath, _eloc :: Location}
  | ELit {_lit :: String, _litType :: Type, _eloc :: Location}
  | ELam
      { _elamBoundVars :: [TVar],
        _elamArgs :: [(String, Type)],
        _elamEffType :: Maybe EffectType,
        _elamResultType :: Type,
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

instance Pretty Expr where
  pretty EVar {..} = pretty _evarName <+> pretty _eloc
  pretty ELit {..} = pretty _lit <+> pretty _eloc
  pretty ELam {..} =
    parens $
      "fn" <+> bracketsList _elamBoundVars
        <+> parensList' (fmap (\(v, t) -> pretty v <+> colon <+> pretty t) _elamArgs)
        <+> colon
        <+> pretty _elamEffType
        <+> pretty _elamResultType
        <+> pretty _elamExpr
        <+> pretty _eloc
  pretty ECase {..} = parens $ "case" <+> pretty _ecaseExpr <+> "of" <+> bracesList _ecaseBody <+> pretty _eloc
  pretty EApp {..} = parens $ pretty _eappFunc <+> parensList _eappArgs <+> pretty _eloc
  pretty ELet {..} = parens $ "let" <+> bracketsList _eletVars <+> pretty _eletBody <+> pretty _eloc
  pretty EHandle {..} = parens $ "handle" <+> pretty _ehandleExpr <+> pretty _eloc
  pretty EAnn {..} = parens $ pretty _eannExpr <+> colon <+> pretty _eannType <+> pretty _eloc

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

instance Pretty TypeDef where
  pretty TypeDef {..} = pretty _typeName <+> anglesList' (fmap (\(t, k) -> pretty t <+> colon <+> pretty k) _typeArgs) <+> bracesList _typeCons <+> pretty _typeLoc

data TypeCon = TypeCon
  { _typeConName :: String,
    _typeConArgs :: [Type],
    _typeConLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty TypeCon where
  pretty TypeCon {..} = pretty _typeConName <+> parensList _typeConArgs <+> pretty _typeConLoc

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

instance Pretty FuncIntf where
  pretty FuncIntf {..} = pretty _intfName <+> bracesList _intfBoundVars <+> parensList _intfArgs <+> colon <+> pretty _intfResultType <+> pretty _intfLoc

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

instance Pretty EffectDef where
  pretty EffectDef {..} = "effect" <+> pretty _effectName <+> anglesList' (fmap (\(t, k) -> pretty t <+> colon <+> pretty k) _effectArgs) <+> bracesList _effectIntfs <+> pretty _effectLoc

data ImportStmt = ImportStmt
  { _importPath :: NamePath,
    _importAlias :: Maybe String,
    _importAttrs :: [NamedAttr],
    _importLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty ImportStmt where
  pretty ImportStmt {..} = "import" <+> pretty _importPath <+> pretty _importLoc

data FuncDef = FuncDef
  { _funcName :: String,
    _funcBoundVars :: [TVar],
    _funcArgs :: [(String, Type)],
    _funcEffectType :: Maybe EffectType,
    _funcResultType :: Type,
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

instance Pretty FuncDef where
  pretty FuncDef {..} =
    "fun" <+> pretty _funcName <+> bracketsList _funcBoundVars <+> parensList' (fmap (\(v, t) -> pretty v <+> colon <+> pretty t) _funcArgs) <+> colon <+> pretty _funcEffectType
      <+> pretty _funcResultType
      <+> bracesList [_funcExpr]
      <+> pretty _funcLoc

data TopStmt
  = FDef {_fdef :: FuncDef}
  | TDef {_tdef :: TypeDef}
  | EDef {_edef :: EffectDef}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty TopStmt where
  pretty FDef {..} = pretty _fdef
  pretty TDef {..} = pretty _tdef
  pretty EDef {..} = pretty _edef

data Module = Module
  { _moduleName :: NamePath,
    _moduleAttrs :: [NamedAttr],
    _moduleExports :: [String],
    _imports :: [ImportStmt],
    _topStmts :: [TopStmt],
    _moduleLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Module where
  pretty Module {..} =
    vsep $
      ["module" <+> pretty _moduleName]
        ++ (map pretty _imports)
        ++ (map pretty _topStmts)
        ++ [pretty _moduleLoc]

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
