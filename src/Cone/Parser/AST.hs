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
import qualified Data.List as L
import Data.Maybe
import GHC.Generics (Generic)
import Prettyprinter
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless (Alpha)
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
  pretty l = pretty $ "@" ++ _fileName l ++ "[" ++ show (_lineNo l) ++ ", " ++ show (_colNo l) ++ "]"

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
  | Unit
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
  pretty Unit = "unit"

type TVar = Name Type

instance Show a => Pretty (Name a) where
  pretty = pretty . show

parensList :: Pretty a => forall ann. [a] -> Doc ann
parensList ls = align $ encloseSep lparen rparen comma $ map pretty ls

bracketsList :: Pretty a => forall ann. [a] -> Doc ann
bracketsList ls = align $ if null ls then emptyDoc else encloseSep lbracket rbracket comma $ map pretty ls

anglesList :: Pretty a => forall ann. [a] -> Doc ann
anglesList ls = align $ if null ls then emptyDoc else encloseSep langle rangle comma $ map pretty ls

parensList' :: [Doc ann] -> Doc ann
parensList' ls = align $ encloseSep lparen rparen comma ls

bracketsList' :: [Doc ann] -> Doc ann
bracketsList' ls = align $ if null ls then emptyDoc else encloseSep lbracket rbracket comma ls

anglesList' :: [Doc ann] -> Doc ann
anglesList' ls = align $ if null ls then emptyDoc else encloseSep langle rangle comma ls

data Type
  = TPrim {_tprim :: PrimType, _tloc :: Location}
  | TVar {_tvar :: TVar, _tloc :: Location}
  | TFunc
      { _tfuncArgs :: [Type],
        _tfuncEff :: EffectType,
        _tfuncResult :: Type,
        _tloc :: Location
      }
  | TNum {_tnum :: Maybe Int, _tloc :: Location}
  | TApp {_tappName :: Type, _tappArgs :: [Type], _tloc :: Location}
  | TAnn {_tannType :: Type, _tannKind :: Kind, _tloc :: Location}
  | BoundType {_boundType :: Bind [(TVar, Maybe Kind)] Type, _tloc :: Location}
  | BoundEffVarType {_boundEffVarType :: Bind [EffVar] Type, _tloc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Type where
  pretty TPrim {..} = pretty _tprim
  pretty TVar {..} = pretty _tvar
  pretty TNum {..} =
    maybe "?" pretty _tnum
  pretty TFunc {..} = parens $ parensList _tfuncArgs <+> "->" <+> pretty _tfuncEff <+> pretty _tfuncResult
  pretty TApp {..} = parens $ pretty _tappName <+> parensList _tappArgs
  pretty TAnn {..} = parens $ pretty _tannType <+> colon <+> pretty _tannKind
  pretty (BoundType (B tvars t) _) = parens $ anglesList tvars <+> pretty t
  pretty (BoundEffVarType (B tvars t) _) = parens $ bracketsList tvars <+> pretty t

data Kind
  = KStar {_kloc :: Location}
  | KNum {_kloc :: Location}
  | KList {_kListElem :: Kind, _kloc :: Location}
  | KFunc {_kfuncArgs :: [Kind], _kfuncResult :: Kind, _kloc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Kind where
  pretty KStar {..} = "*"
  pretty KNum {..} = "num"
  pretty KList {..} = brackets $ pretty _kListElem
  pretty KFunc {..} = parens $ parensList _kfuncArgs <+> "->" <+> pretty _kfuncResult

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
  pretty EKStar {..} = "*"
  pretty EKFunc {..} = parens $ parensList _ekfuncArgs <+> "->" <+> pretty _ekfuncResult
  pretty EKList {..} = bracketsList _ekList

type EffVar = Name EffectType

data EffectType
  = EffVar {_effVar :: EffVar, _effLoc :: Location}
  | EffApp
      { _effAppName :: EffectType,
        _effAppArgs :: [Type],
        _effLoc :: Location
      }
  | EffList {_effList :: [EffectType], _effLoc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty EffectType where
  pretty EffVar {..} = pretty _effVar
  pretty EffApp {..} = parens $ pretty _effAppName <+> parensList _effAppArgs
  pretty EffList {..} = bracketsList _effList

type PVar = Name Pattern

data Pattern
  = PVar {_pvar :: PVar, _ploc :: Location}
  | PApp
      { _pappName :: Expr,
        _pappTypeArgs :: [Type],
        _pappArgs :: [Pattern],
        _ploc :: Location
      }
  | PExpr {_pExpr :: Expr, _ploc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Pattern where
  pretty PVar {..} = pretty _pvar
  pretty PApp {..} = parens $ pretty _pappName <+> anglesList _pappTypeArgs <+> parensList _pappArgs
  pretty PExpr {..} = pretty _pExpr

data Case
  = Case
      { _casePattern :: Pattern,
        _caseGuard :: Maybe Expr,
        _caseExpr :: Expr,
        _caseLoc :: Location
      }
  | BoundCase {_boundCase :: Bind [PVar] Case, _caseLoc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Case where
  pretty Case {..} =
    parens $
      pretty _casePattern -- <+> "|"
      -- <+> pretty _caseGuard
        <+> "->"
        <+> align (braces $ line <> pretty _caseExpr <> line)
  pretty (BoundCase (B vs c) _) = bracketsList vs <+> pretty c

type EVar = Name Expr

data Expr
  = EVar {_evarName :: EVar, _eloc :: Location}
  | ELit {_lit :: String, _litType :: Type, _eloc :: Location}
  | ELam
      { _elamBoundVars :: [(TVar, Maybe Kind)],
        _elamBoundEffVars :: [EffVar],
        _elamArgs :: [(String, Type)],
        _elamEffType :: EffectType,
        _elamResultType :: Type,
        _elamExpr :: Maybe Expr,
        _eloc :: Location
      }
  | ECase {_ecaseExpr :: Expr, _ecaseBody :: [Case], _eloc :: Location}
  | EWhile {_ewhileCond :: Expr, _ewhileBody :: Expr, _eloc :: Location}
  | EApp {_eappDiff :: Bool, _eappFunc :: Expr, _eappTypeArgs :: [Type], _eappArgs :: [Expr], _eloc :: Location}
  | ELet
      { _eletPattern :: Pattern,
        _eletExpr :: Expr,
        _eletBody :: Expr,
        _eletState :: Bool,
        _eloc :: Location
      }
  | EHandle
      { _ehandleEff :: EffectType,
        _ehandleScope :: Expr,
        _ehandleBindings :: [FuncDef],
        _eloc :: Location
      }
  | ESeq {_eseq :: [Expr], _eloc :: Location}
  | EAnn {_eannExpr :: Expr, _eannType :: Type, _eloc :: Location}
  | EAnnMeta {_eannMetaExpr :: Expr, _eannMetaType :: Type, _eannMetaEffType :: EffectType, _eloc :: Location}
  | EBoundTypeVars {_eboundTypeVars :: Bind [TVar] Expr, _eloc :: Location}
  | EBoundEffTypeVars {_eboundEffTypeVars :: Bind [EffVar] Expr, _eloc :: Location}
  | EBoundVars {_eboundVars :: Bind [EVar] Expr, _eloc :: Location}
  deriving
    ( Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

instance Pretty Expr where
  pretty EVar {..} = pretty _evarName
  pretty ELit {..} = pretty _lit
  pretty ELam {..} =
    parens $
      vsep
        [ "fn" <+> anglesList _elamBoundVars <+> bracketsList _elamBoundEffVars
            <+> parensList' (fmap (\(v, t) -> pretty v <+> colon <+> pretty t) _elamArgs)
            <+> colon
            <+> pretty _elamEffType
            <+> pretty _elamResultType,
          braces $ line <> indent 4 (pretty _elamExpr) <> line
        ]
  pretty EWhile {..} = parens $ vsep ["while" <+> pretty _ewhileCond, braces (line <> indent 4 (pretty _ewhileBody) <> line)]
  pretty ECase {..} =
    parens $
      vsep
        [ "case" <+> pretty _ecaseExpr,
          braces $ line <> indent 4 (vsep (map (\c -> braces (line <> indent 4 (pretty c) <> line)) _ecaseBody)) <> line
        ]
  pretty EApp {..} = parens $ (if _eappDiff then "diff " else "") <+> pretty _eappFunc <+> parensList _eappArgs
  pretty ELet {..} =
    parens $
      vsep
        [ (if _eletState then "var" else "val")
            <+> pretty _eletPattern
            <+> "="
            <+> align (pretty _eletExpr),
          pretty _eletBody
        ]
  pretty EHandle {..} =
    parens $
      vsep
        [ "handle" <+> pretty _ehandleEff,
          braces (line <> indent 4 (pretty _ehandleScope) <> line),
          "with" <+> braces (line <> vsep (map (indent 4 . pretty) _ehandleBindings) <> line)
        ]
  pretty ESeq {..} = vsep $ map pretty _eseq
  pretty EAnn {..} = parens $ pretty _eannExpr <+> colon <+> pretty _eannType
  pretty EAnnMeta {..} = parens $ pretty _eannMetaExpr <+> colon <+> pretty _eannMetaEffType <+> pretty _eannMetaType
  pretty (EBoundTypeVars (B bs e) _) = anglesList bs <+> pretty e
  pretty (EBoundEffTypeVars (B bs e) _) = bracketsList bs <+> pretty e
  pretty (EBoundVars (B bs e) _) = bracketsList bs <+> pretty e

eappBool :: Bool
eappBool = error "not implemented"

data TypeDef
  = TypeDef
      { _typeName :: String,
        _typeArgs :: [(TVar, Maybe Kind)],
        _typeCons :: [TypeCon],
        _typeLoc :: Location
      }
  | BoundTypeDef {_tbound :: Bind [TVar] TypeDef, _typeLoc :: Location}
  deriving
    ( Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

instance Pretty TypeDef where
  pretty TypeDef {..} =
    vsep
      [ "type" <+> pretty _typeName
          <+> anglesList' (fmap (\(t, k) -> pretty t <+> colon <+> pretty k) _typeArgs),
        braces $ line <> vsep (map (indent 4 . pretty) _typeCons) <> line
      ]
  pretty (BoundTypeDef (B vs t) _) = anglesList vs <+> pretty t

data TypeCon = TypeCon
  { _typeConName :: String,
    _typeConArgs :: [Type],
    _typeConLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty TypeCon where
  pretty TypeCon {..} = pretty _typeConName <+> parensList _typeConArgs

data TypeAlias
  = TypeAlias {_typeAliasName :: String, _typeAliasArgs :: [(TVar, Maybe Kind)], _typeAliasType :: Type, _typeAliasLoc :: Location}
  | BoundTypeAlias {_boundTypeAlias :: Bind [TVar] TypeAlias, _typeAliasLoc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty TypeAlias where
  pretty TypeAlias {..} = "alias" <+> pretty _typeAliasName <> parensList _typeAliasArgs <+> "=" <+> pretty _typeAliasType
  pretty (BoundTypeAlias (B vs t) _) = anglesList vs <> pretty t

data FuncIntf
  = FuncIntf
      { _intfName :: String,
        _intfBoundVars :: [(TVar, Maybe Kind)],
        _intfBoundEffVars :: [EffVar],
        _intfArgs :: [Type],
        _intfEffectType :: EffectType,
        _intfResultType :: Type,
        _intfLoc :: Location
      }
  | BoundFuncIntf {_boundFuncIntf :: Bind [TVar] FuncIntf, _intfLoc :: Location}
  | BoundEffFuncIntf {_boundEffFuncIntf :: Bind [EffVar] FuncIntf, _intfLoc :: Location}
  deriving
    ( Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

instance Pretty FuncIntf where
  pretty FuncIntf {..} =
    pretty _intfName <+> anglesList _intfBoundVars <+> bracketsList _intfBoundEffVars
      <+> parensList _intfArgs
      <+> colon
      <+> pretty _intfEffectType
      <+> pretty _intfResultType
  pretty (BoundFuncIntf (B vs f) _) = anglesList vs <+> pretty f
  pretty (BoundEffFuncIntf (B vs f) _) = bracketsList vs <+> pretty f

data EffectDef
  = EffectDef
      { _effectName :: String,
        _effectArgs :: [(TVar, Maybe Kind)],
        _effectIntfs :: [FuncIntf],
        _effectLoc :: Location
      }
  | BoundEffectDef {_boundEffDef :: Bind [TVar] EffectDef, _effectLoc :: Location}
  deriving
    ( Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

instance Pretty EffectDef where
  pretty EffectDef {..} =
    vsep
      [ "effect" <+> pretty _effectName
          <+> anglesList' (fmap (\(t, k) -> pretty t <+> colon <+> pretty k) _effectArgs),
        braces $ line <> vsep (map (indent 4 . pretty) _effectIntfs) <> line
      ]
  pretty (BoundEffectDef (B vs e) _) = bracketsList vs <+> pretty e

data ImportStmt = ImportStmt
  { _importPath :: NamePath,
    _importAlias :: Maybe String,
    _importAttrs :: [NamedAttr],
    _importLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty ImportStmt where
  pretty ImportStmt {..} =
    "import" <+> pretty _importPath
      <+> ( case _importAlias of
              Just a -> "as" <+> pretty a
              Nothing -> emptyDoc
          )

data InterfaceDef = InterfaceDef
  { _interfaceName :: String,
    _interfaceTVar :: (TVar, Maybe Kind),
   -- _interfaceDeps :: [Type],
    _interfaceFuncs :: [FuncIntf],
    _interfaceLoc :: Location
  }
  | BoundInterfaceDef {_boundInterfaceDef :: Bind [TVar] InterfaceDef, _interfaceLoc :: Location}
  deriving
    ( Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

instance Pretty InterfaceDef where
  pretty InterfaceDef {..} =
    vsep
      [ "interface" <+> pretty _interfaceName <+> anglesList [_interfaceTVar],
        braces $ line <> indent 4 (vsep $ map pretty _interfaceFuncs) <> line
      ]
  pretty (BoundInterfaceDef (B vs i) _) = anglesList vs <+> pretty i

data ImplInterfaceDef = ImplInterfaceDef
  { _implInterfaceBoundVars :: [(TVar, Maybe Kind)],
    _implInterfaceDefName :: String,
    _implInterfaceDefType :: Type,
    _implInterfaceDefFuncs :: [FuncDef],
    _implInferfaceLoc :: Location
  }
  | BoundImplInterfaceDef {_boundImplInterfaceDef :: Bind [TVar] ImplInterfaceDef, _implInterfaceLoc :: Location}
  deriving
    ( Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

instance Pretty ImplInterfaceDef where
  pretty ImplInterfaceDef {..} =
    vsep
      [ "impl" <+> "interface" <+> pretty _implInterfaceDefName <+> anglesList [_implInterfaceDefType],
        braces $ line <> indent 4 (vsep $ map pretty _implInterfaceDefFuncs) <> line
      ]
  pretty (BoundImplInterfaceDef (B vs i) _) = anglesList vs <+> pretty i

data FuncDef
  = FuncDef
      { _funcName :: String,
        _funcBoundVars :: [(TVar, Maybe Kind)],
        _funcBoundEffVars :: [EffVar],
        _funcArgs :: [(String, Type)],
        _funcEffectType :: EffectType,
        _funcResultType :: Type,
        _funcExpr :: Maybe Expr,
        _funcLoc :: Location
      }
  | BoundFuncDef {_boundFuncDef :: Bind [TVar] FuncDef, _funcLoc :: Location}
  | BoundEffFuncDef {_boundEffFuncDef :: Bind [EffVar] FuncDef, _funcLoc :: Location}
  deriving
    ( Eq,
      Ord,
      Show,
      Read,
      Data,
      Typeable,
      Generic
    )

instance Pretty FuncDef where
  pretty FuncDef {..} =
    vsep
      [ "fun" <+> pretty _funcName <+> anglesList _funcBoundVars <+> bracketsList _funcBoundEffVars
          <+> parensList' (fmap (\(v, t) -> pretty v <+> colon <+> pretty t) _funcArgs)
          <+> colon
          <+> pretty _funcEffectType
          <+> pretty _funcResultType,
        braces $ line <> indent 4 (pretty _funcExpr) <> line
      ]
  pretty (BoundFuncDef (B vs f) _) = anglesList vs <+> pretty f
  pretty (BoundEffFuncDef (B vs f) _) = bracketsList vs <+> pretty f

data ImplFuncDef = ImplFuncDef {_implFunDef :: FuncDef}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty ImplFuncDef where
  pretty ImplFuncDef {..} = "impl" <+> pretty _implFunDef

data DiffDef
  = DiffDef {_diffFunc :: String, _diffWRT :: [String], _diffAdj :: Maybe Expr, _diffLoc :: Location}
  | BoundDiffDef {_boundDiff :: Bind [EVar] DiffDef, _diffLoc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty DiffDef where
  pretty DiffDef {..} = "diff" <+> pretty _diffFunc <+> "wrt" <+> parensList _diffWRT <+> "=" <+> pretty _diffAdj
  pretty (BoundDiffDef (B vs d) _) = anglesList vs <+> pretty d

data TopStmt
  = FDef {_fdef :: FuncDef}
  | TDef {_tdef :: TypeDef}
  | TAlias {_talias :: TypeAlias}
  | EDef {_edef :: EffectDef}
  | DDef {_ddef :: DiffDef}
  | IDef {_idef :: InterfaceDef}
  | ImplIDef {_implIdef :: ImplInterfaceDef}
  | ImplFDef {_implFdef :: ImplFuncDef}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty TopStmt where
  pretty FDef {..} = pretty _fdef
  pretty TDef {..} = pretty _tdef
  pretty TAlias {..} = pretty _talias
  pretty EDef {..} = pretty _edef
  pretty DDef {..} = pretty _ddef
  pretty IDef {..} = pretty _idef
  pretty ImplIDef {..} = pretty _implIdef
  pretty ImplFDef {..} = pretty _implFdef

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
        ++ map pretty _imports
        ++ map pretty _topStmts

-------------------------------

instance Plated Attr where
  plate = uniplate

instance Alpha Attr

instance Subst Type Attr

instance Subst EffectType Attr

instance Subst Expr Attr

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

instance Subst EffectType Location

instance Subst Expr Location

instance Subst InterfaceDef Location

instance Subst ImplInterfaceDef Location

makeLenses ''Location

makePrisms ''Location

-------------------------------

instance Plated PrimType where
  plate = uniplate

instance Alpha PrimType

instance Subst Type PrimType

instance Subst EffectType PrimType

instance Subst Expr PrimType

instance Subst InterfaceDef PrimType

instance Subst ImplInterfaceDef PrimType

makeLenses ''PrimType

makePrisms ''PrimType

-------------------------------

instance Plated Type where
  plate = uniplate

instance Alpha Kind

instance Alpha EffectType

instance Alpha Type

instance Subst Type Kind

instance Subst Type EffectType

instance Subst Type Type where
  isvar (TVar x _) = Just (SubstName x)
  isvar _ = Nothing

instance Subst EffectType Kind

instance Subst EffectType EffectType where
  isvar (EffVar x _) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Expr Kind

instance Subst InterfaceDef Kind

instance Subst ImplInterfaceDef Kind

instance Subst InterfaceDef EffectType

instance Subst ImplInterfaceDef EffectType

instance Subst EffectType Type

instance Subst Expr EffectType

instance Subst Expr Type

instance Subst InterfaceDef Type

instance Subst ImplInterfaceDef Type

makeLenses ''Type

makePrisms ''Type

-------------------------------

instance Plated Kind where
  plate = uniplate

makeLenses ''Kind

makePrisms ''Kind

-------------------------------

instance Plated EffKind where
  plate = uniplate

instance Alpha EffKind

instance Subst Type EffKind

instance Subst EffectType EffKind

makeLenses ''EffKind

makePrisms ''EffKind

-------------------------------

instance Plated EffectType where
  plate = uniplate

makeLenses ''EffectType

makePrisms ''EffectType

-------------------------------

instance Plated Pattern where
  plate = uniplate

instance Alpha FuncDef

instance Alpha Case

instance Alpha Expr

instance Alpha Pattern

instance Subst Type Case

instance Subst Type FuncDef

instance Subst InterfaceDef FuncDef

instance Subst ImplInterfaceDef FuncDef

instance Subst InterfaceDef Pattern

instance Subst ImplInterfaceDef Pattern

instance Subst InterfaceDef Case

instance Subst ImplInterfaceDef Case

instance Subst InterfaceDef Expr

instance Subst ImplInterfaceDef Expr

instance Subst Type Expr

instance Subst Type Pattern

instance Subst EffectType Case

instance Subst EffectType FuncDef

instance Subst EffectType Expr

instance Subst EffectType Pattern

instance Subst Expr FuncDef

instance Subst Expr Case

instance Subst Expr Expr where
  isvar (EVar x _) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Expr Pattern

instance Subst Pattern Location

instance Subst Pattern Kind

instance Subst Pattern EffectType

instance Subst Pattern Case

instance Subst Pattern FuncDef

instance Subst Pattern PrimType

instance Subst Pattern Type

instance Subst Pattern Expr

instance Subst Pattern Pattern where
  isvar (PVar x _) = Just (SubstName x)
  isvar _ = Nothing

makeLenses ''Pattern

makePrisms ''Pattern

-------------------------------

instance Plated Expr where
  plate = uniplate

makeLenses ''Expr

makePrisms ''Expr

-------------------------------

instance Plated Case where
  plate = uniplate

makeLenses ''Case

makePrisms ''Case

-------------------------------

instance Plated TypeDef where
  plate = uniplate

instance Alpha TypeCon

instance Alpha TypeDef

instance Subst Type TypeCon

instance Subst Type TypeDef

instance Subst EffectType TypeCon

instance Subst EffectType TypeDef

instance Subst Expr TypeCon

instance Subst Expr TypeDef

instance Subst InterfaceDef TypeCon

instance Subst ImplInterfaceDef TypeCon

instance Subst InterfaceDef TypeDef

instance Subst ImplInterfaceDef TypeDef

makeLenses ''TypeDef

makePrisms ''TypeDef

-------------------------------

instance Plated TypeAlias where
  plate = uniplate

instance Alpha TypeAlias

instance Subst Type TypeAlias

instance Subst EffectType TypeAlias

instance Subst Expr TypeAlias

instance Subst InterfaceDef TypeAlias

instance Subst ImplInterfaceDef TypeAlias

makeLenses ''TypeAlias

makePrisms ''TypeAlias

-------------------------------

instance Plated TypeCon where
  plate = uniplate

makeLenses ''TypeCon

makePrisms ''TypeCon

-------------------------------

instance Plated EffectDef where
  plate = uniplate

instance Alpha FuncIntf

instance Alpha EffectDef

instance Subst Type FuncIntf

instance Subst Type EffectDef

instance Subst EffectType FuncIntf

instance Subst EffectType EffectDef

instance Subst Expr FuncIntf

instance Subst Expr EffectDef

instance Subst InterfaceDef FuncIntf

instance Subst ImplInterfaceDef FuncIntf

instance Subst InterfaceDef EffectDef

instance Subst ImplInterfaceDef EffectDef

makeLenses ''EffectDef

makePrisms ''EffectDef

-------------------------------

instance Plated ImportStmt where
  plate = uniplate

instance Alpha ImportStmt

instance Subst Type ImportStmt

instance Subst EffectType ImportStmt

instance Subst Expr ImportStmt

makeLenses ''ImportStmt

makePrisms ''ImportStmt

-------------------------------

instance Plated FuncIntf where
  plate = uniplate

makeLenses ''FuncIntf

makePrisms ''FuncIntf

-------------------------------

instance Plated FuncDef where
  plate = uniplate

makeLenses ''FuncDef

makePrisms ''FuncDef

-------------------------------

instance Plated InterfaceDef where
  plate = uniplate

instance Subst Expr InterfaceDef

instance Subst EffectType InterfaceDef

instance Subst Type InterfaceDef

instance Subst InterfaceDef InterfaceDef

instance Subst ImplInterfaceDef InterfaceDef

instance Alpha InterfaceDef

makeLenses ''InterfaceDef

makePrisms ''InterfaceDef

-------------------------------

instance Plated ImplInterfaceDef where
  plate = uniplate

instance Subst Expr ImplInterfaceDef

instance Subst EffectType ImplInterfaceDef

instance Subst Type ImplInterfaceDef

instance Subst ImplInterfaceDef ImplInterfaceDef

instance Subst InterfaceDef ImplInterfaceDef

instance Alpha ImplInterfaceDef

makeLenses ''ImplInterfaceDef

makePrisms ''ImplInterfaceDef

-------------------------------

instance Plated DiffDef where
  plate = uniplate

instance Alpha DiffDef

instance Subst Type DiffDef

instance Subst EffectType DiffDef

instance Subst Expr DiffDef

instance Subst InterfaceDef DiffDef

instance Subst ImplInterfaceDef DiffDef

makeLenses ''DiffDef

makePrisms ''DiffDef

-------------------------------

instance Plated ImplFuncDef where
  plate = uniplate

instance Alpha ImplFuncDef

instance Subst Type ImplFuncDef

instance Subst EffectType ImplFuncDef

instance Subst Expr ImplFuncDef

instance Subst InterfaceDef ImplFuncDef

instance Subst ImplInterfaceDef ImplFuncDef

makeLenses ''ImplFuncDef

makePrisms ''ImplFuncDef

-------------------------------

instance Plated TopStmt where
  plate = uniplate

instance Alpha TopStmt

instance Subst Type TopStmt

instance Subst EffectType TopStmt

instance Subst Expr TopStmt

instance Subst InterfaceDef TopStmt

instance Subst ImplInterfaceDef TopStmt

makeLenses ''TopStmt

makePrisms ''TopStmt

-------------------------------

instance Plated Module where
  plate = uniplate

instance Alpha Module

instance Subst Type Module

instance Subst EffectType Module

instance Subst Expr Module

makeLenses ''Module

makePrisms ''Module

-------------------------------
