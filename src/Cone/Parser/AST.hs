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
parensList ls = encloseSep lparen rparen comma $ map pretty ls

bracketsList :: Pretty a => forall ann. [a] -> Doc ann
bracketsList ls = encloseSep lbracket rbracket comma $ map pretty ls

anglesList :: Pretty a => forall ann. [a] -> Doc ann
anglesList ls = encloseSep langle rangle comma $ map pretty ls

bracesList :: Pretty a => forall ann. [a] -> Doc ann
bracesList ls = align $ encloseSep lbrace rbrace semi $ map pretty ls

parensList' :: [Doc ann] -> Doc ann
parensList' ls = encloseSep lparen rparen comma ls

bracketsList' :: [Doc ann] -> Doc ann
bracketsList' ls = encloseSep lbracket rbracket comma ls

anglesList' :: [Doc ann] -> Doc ann
anglesList' ls = encloseSep langle rangle comma ls

bracesList' :: [Doc ann] -> Doc ann
bracesList' ls = align $ encloseSep lbrace rbrace semi ls

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
  | BoundType {_boundType :: Bind [TVar] Type, _tloc :: Location}
  | BoundEffVarType {_boundEffVarType :: Bind [EffVar] Type, _tloc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Type where
  pretty TPrim {..} = pretty _tprim 
  pretty TVar {..} = pretty _tvar
  pretty TNum {..} =
    ( case _tnum of
        Just t -> pretty t
        Nothing -> "?"
    )
  pretty TFunc {..} = parens $ parensList _tfuncArgs <+> "->" <+> pretty _tfuncEff <+> pretty _tfuncResult
  pretty TApp {..} = parens $ pretty _tappName <+> parensList _tappArgs
  pretty TAnn {..} = parens $ pretty _tannType <+> colon <+> pretty _tannKind
  pretty (BoundType (B tvars t) _) = parens $ anglesList tvars <+> pretty t
  pretty (BoundEffVarType (B tvars t) _) = parens $ bracketsList tvars <+> pretty t

data Kind
  = KStar {_kloc :: Location}
  | KNum {_kloc :: Location}
  | KFunc {_kfuncArgs :: [Kind], _kfuncResult :: Kind, _kloc :: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Kind where
  pretty KStar {..} = "*"
  pretty KNum {..} = "num"
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
  pretty EKList {..} = anglesList _ekList

type EffVar = Name EffectType

data EffectType
  = EffVar { _effVar :: EffVar, _effLoc :: Location}
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

data Pattern
  = PVar {_pvar :: NamePath, _ploc :: Location}
  | PApp
      { _pappName :: NamePath,
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

data Case = Case
  { _casePattern :: Pattern,
    _caseGuard :: Maybe Expr,
    _caseExpr :: Expr,
    _caseLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty Case where
  pretty Case {..} =
    parens $
      pretty _casePattern -- <+> "|"
        -- <+> pretty _caseGuard
        <+> "->"
        <+> pretty _caseExpr

type IndexVar = Name TCExpr

data TCExpr
  = TCAccess {_tcVarName :: NamePath, _tcIndices :: [IndexVar], _tcloc :: Location}
  | TCApp {_tcAppName :: NamePath, _tcAppArgs :: [TCExpr], _tcloc :: Location}
  | TCVar {_tcVarName :: NamePath, _tcloc:: Location}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty TCExpr where
  pretty TCAccess {..} = parens $ pretty _tcVarName <+> bracketsList _tcIndices
  pretty TCApp {..} = parens $ pretty _tcAppName <+> parensList _tcAppArgs
  pretty TCVar {..} = pretty _tcVarName

data Expr
  = EVar {_evarName :: NamePath, _eloc :: Location}
  | ELit {_lit :: String, _litType :: Type, _eloc :: Location}
  | ELam
      { _elamBoundVars :: [TVar],
        _elamBoundEffVars :: [EffVar],
        _elamArgs :: [(String, Type)],
        _elamEffType :: EffectType,
        _elamResultType :: Type,
        _elamExpr :: Maybe Expr,
        _eloc :: Location
      }
  | ECase {_ecaseExpr :: Expr, _ecaseBody :: [Case], _eloc :: Location}
  | EWhile {_ewhileCond :: Expr, _ewhileBody :: Expr, _eloc :: Location}
  | EApp {_eappFunc :: Expr, _eappTypeArgs:: [Type], _eappArgs :: [Expr], _eloc :: Location}
  | ELet
      { _eletPattern :: Pattern,
        _eletExpr :: Expr,
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
  | ETC {_etc :: TCExpr, _eloc :: Location}
  | EAnn {_eannExpr :: Expr, _eannType :: Type, _eloc :: Location}
  | EAnnMeta {_eannMetaExpr :: Expr, _eannMetaType :: Type, _eloc :: Location}
  | EBoundTypeVars {_eboundTypeVars :: Bind [TVar] Expr, _eloc :: Location}
  | EBoundEffTypeVars {_eboundEffTypeVars :: Bind [EffVar] Expr, _eloc :: Location}
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
  pretty EVar {..} = pretty _evarName
  pretty ELit {..} = pretty _lit
  pretty ELam {..} =
    parens $
      "fn" <+> anglesList _elamBoundVars <+> bracesList _elamBoundEffVars
        <+> parensList' (fmap (\(v, t) -> pretty v <+> colon <+> pretty t) _elamArgs)
        <+> colon
        <+> pretty _elamEffType
        <+> pretty _elamResultType
        <+> pretty _elamExpr
  pretty EWhile {..} = parens $ "while" <+> pretty _ewhileCond <+> braces (pretty _ewhileBody)
  pretty ECase {..} = parens $ "case" <+> pretty _ecaseExpr <+> bracesList _ecaseBody 
  pretty EApp {..} = parens $ pretty _eappFunc <+> parensList _eappArgs 
  pretty ELet {..} = parens $ (if _eletState then "var" else "val") 
       <+> pretty _eletPattern <+> "=" <+> pretty _eletExpr
  pretty EHandle {..} = parens $ "handle" <+> pretty _ehandleEff <+> braces (pretty _ehandleScope)
                        <+> "with" <+> bracesList _ehandleBindings
  pretty ESeq {..} = vsep $ fmap pretty _eseq
  pretty ETC {..} = pretty _etc
  pretty EAnn {..} = parens $ pretty _eannExpr <+> colon <+> pretty _eannType
  pretty EAnnMeta {..} = parens $ pretty _eannMetaExpr <+> colon <+> pretty _eannMetaType
  pretty (EBoundTypeVars (B bs e) _) = anglesList bs <+> pretty e
  pretty (EBoundEffTypeVars (B bs e) _) = bracketsList bs <+> pretty e

data TypeDef = TypeDef
  { _typeName :: String,
    _typeArgs :: [(TVar, Maybe Kind)],
    _typeCons :: [TypeCon],
    _typeLoc :: Location
  }
  | BoundTypeDef {_tbound :: Bind [TVar] TypeDef, _typeLoc :: Location}
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
  pretty TypeDef {..} =
    "type" <+> pretty _typeName
      <+> anglesList' (fmap (\(t, k) -> pretty t <+> colon <+> pretty k) _typeArgs)
      <+> bracesList _typeCons
  pretty (BoundTypeDef (B _ t) _) = pretty t

data TypeCon = TypeCon
  { _typeConName :: String,
    _typeConArgs :: [Type],
    _typeConLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty TypeCon where
  pretty TypeCon {..} = pretty _typeConName <+> parensList _typeConArgs

data FuncIntf = FuncIntf
  { _intfName :: String,
    _intfBoundVars :: [TVar],
    _intfBoundEffVars :: [EffVar],
    _intfArgs :: [Type],
    _intfEffectType :: EffectType,
    _intfResultType :: Type,
    _intfLoc :: Location
  }
  | BoundFuncIntf {_boundFuncIntf :: Bind [TVar] FuncIntf, _intfLoc :: Location}
  | BoundEffFuncIntf {_boundEffFuncIntf :: Bind [EffVar] FuncIntf, _intfLoc :: Location}
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
  pretty FuncIntf {..} =
    pretty _intfName <+> anglesList _intfBoundVars <+> bracketsList _intfBoundEffVars
      <+> parensList _intfArgs
      <+> colon
      <+> pretty _intfEffectType
      <+> pretty _intfResultType
  pretty (BoundFuncIntf (B _ f) _) = pretty f
  pretty (BoundEffFuncIntf (B _ f) _) = pretty f

data EffectDef = EffectDef
  { _effectName :: String,
    _effectArgs :: [(TVar, Maybe Kind)],
    _effectIntfs :: [FuncIntf],
    _effectLoc :: Location
  }
  | BoundEffectDef {_boundEffDef :: Bind [TVar] EffectDef, _effectLoc :: Location}
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
  pretty EffectDef {..} =
    "effect" <+> pretty _effectName
      <+> anglesList' (fmap (\(t, k) -> pretty t <+> colon <+> pretty k) _effectArgs)
      <+> bracesList _effectIntfs
  pretty (BoundEffectDef (B _ e) _) = pretty e

data ImportStmt = ImportStmt
  { _importPath :: NamePath,
    _importAlias :: Maybe String,
    _importAttrs :: [NamedAttr],
    _importLoc :: Location
  }
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty ImportStmt where
  pretty ImportStmt {..} = "import" <+> pretty _importPath <+> 
     (case _importAlias of
       Just a -> "as" <+> pretty a
       Nothing -> emptyDoc)

data FuncDef = FuncDef
  { _funcName :: String,
    _funcBoundVars :: [TVar],
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
    (
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
    "fun" <+> pretty _funcName <+> anglesList _funcBoundVars <+> bracketsList _funcBoundEffVars <+>
     parensList' (fmap (\(v, t) -> pretty v <+> colon <+> pretty t) _funcArgs) <+> colon <+> pretty _funcEffectType
      <+> pretty _funcResultType
      <+> bracesList [_funcExpr]
  pretty (BoundFuncDef (B _ f) _) = pretty f
  pretty (BoundEffFuncDef (B _ f) _) = pretty f

data ImplFuncDef = ImplFuncDef {_implFunDef :: FuncDef}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty ImplFuncDef where
  pretty ImplFuncDef {..} = "impl" <+> pretty _implFunDef

data TopStmt
  = FDef {_fdef :: FuncDef}
  | TDef {_tdef :: TypeDef}
  | EDef {_edef :: EffectDef}
  | ImplFDef {_implFdef :: ImplFuncDef}
  deriving (Eq, Ord, Show, Read, Data, Typeable, Generic)

instance Pretty TopStmt where
  pretty FDef {..} = pretty _fdef
  pretty TDef {..} = pretty _tdef
  pretty EDef {..} = pretty _edef
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
        ++ (map pretty _imports)
        ++ (map pretty _topStmts)

-------------------------------

instance Plated Attr where
  plate = uniplate

instance Alpha Attr

instance Subst Type Attr

instance Subst EffectType Attr

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

makeLenses ''Location

makePrisms ''Location

-------------------------------

instance Plated PrimType where
  plate = uniplate

instance Alpha PrimType

instance Subst Type PrimType

instance Subst EffectType PrimType

makeLenses ''PrimType

makePrisms ''PrimType

-------------------------------

instance Plated Type where
  plate = uniplate

instance Alpha Type

instance Subst Type Type where
  isvar (TVar x _) = Just (SubstName x)
  isvar _ = Nothing

instance Subst EffectType Type

makeLenses ''Type

makePrisms ''Type

-------------------------------

instance Plated Kind where
  plate = uniplate

instance Alpha Kind

instance Subst Type Kind

instance Subst EffectType Kind

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

instance Alpha EffectType

instance Subst EffectType EffectType where
  isvar (EffVar x _) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Type EffectType

makeLenses ''EffectType

makePrisms ''EffectType

-------------------------------

instance Plated Pattern where
  plate = uniplate

instance Alpha Pattern

instance Subst Type Pattern

instance Subst EffectType Pattern

makeLenses ''Pattern

makePrisms ''Pattern

-------------------------------

instance Plated TCExpr where
  plate = uniplate

instance Alpha TCExpr

instance Subst Type TCExpr

instance Subst EffectType TCExpr

makeLenses ''TCExpr

makePrisms ''TCExpr

-------------------------------

instance Plated Expr where
  plate = uniplate

instance Alpha Expr

instance Subst Type Expr

instance Subst EffectType Expr

makeLenses ''Expr

makePrisms ''Expr

-------------------------------

instance Plated Case where
  plate = uniplate

instance Alpha Case

instance Subst Type Case

instance Subst EffectType Case

makeLenses ''Case

makePrisms ''Case

-------------------------------

instance Plated TypeDef where
  plate = uniplate

instance Alpha TypeDef

instance Subst Type TypeDef

instance Subst EffectType TypeDef

makeLenses ''TypeDef

makePrisms ''TypeDef

-------------------------------

instance Plated TypeCon where
  plate = uniplate

instance Alpha TypeCon

instance Subst Type TypeCon

instance Subst EffectType TypeCon

makeLenses ''TypeCon

makePrisms ''TypeCon

-------------------------------

instance Plated EffectDef where
  plate = uniplate

instance Alpha EffectDef

instance Subst Type EffectDef

instance Subst EffectType EffectDef

makeLenses ''EffectDef

makePrisms ''EffectDef

-------------------------------

instance Plated ImportStmt where
  plate = uniplate

instance Alpha ImportStmt

instance Subst Type ImportStmt

instance Subst EffectType ImportStmt

makeLenses ''ImportStmt

makePrisms ''ImportStmt

-------------------------------

instance Plated FuncIntf where
  plate = uniplate

instance Alpha FuncIntf

instance Subst Type FuncIntf

instance Subst EffectType FuncIntf

makeLenses ''FuncIntf

makePrisms ''FuncIntf

-------------------------------

instance Plated FuncDef where
  plate = uniplate

instance Alpha FuncDef

instance Subst Type FuncDef

instance Subst EffectType FuncDef

makeLenses ''FuncDef

makePrisms ''FuncDef

-------------------------------

instance Plated ImplFuncDef where
  plate = uniplate

instance Alpha ImplFuncDef

instance Subst Type ImplFuncDef

instance Subst EffectType ImplFuncDef

makeLenses ''ImplFuncDef

makePrisms ''ImplFuncDef

-------------------------------

instance Plated TopStmt where
  plate = uniplate

instance Alpha TopStmt

instance Subst Type TopStmt

instance Subst EffectType TopStmt

makeLenses ''TopStmt

makePrisms ''TopStmt

-------------------------------

instance Plated Module where
  plate = uniplate

instance Alpha Module

instance Subst Type Module

instance Subst EffectType Module

makeLenses ''Module

makePrisms ''Module

-------------------------------
