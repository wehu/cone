
module Cone.Parser.AST
       (NamePath, Location(..), Module(..), NamedAttr, Attr(..), TopStmt(..),
        FuncDef(..), Type(..), Kind(..), Case(..), Pattern(..), Expr(..),
        TypeDef(..), TypeCon(..), EffectDef(..), EffKind(..), EffectType(..),
        ImportStmt(..))
       where
import Data.Maybe

type NamePath = [String]

data Location = Location{fileName :: String, lineNo :: Int, colNo :: Int}

data Module = Module{moduleName :: NamePath, moduleAttrs :: [NamedAttr],
                     moduleExports :: [String], topStmts :: [TopStmt],
                     moduleLoc :: Location}

type NamedAttr = (String, Attr)

data Attr = String
          | Int
          | Bool

data TopStmt = FDef FuncDef
             | TDef TypeDef
             | EDef EffectDef
             | Import ImportStmt

data FuncDef = FuncDef{funcName :: String, funcType :: Maybe Type,
                       funcCases :: [Case], funcLoc :: Location}

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
          | TVar String
          | TFunc [Type] EffectType Type
          | TApp NamePath [Type]
          | TAnn Type Kind
          | TLoc Type Location

data Kind = KStar
          | KFunc Kind Kind
          | KLoc Kind Location

data Case = Case{casePattern :: Maybe Pattern, caseGuard :: Maybe Expr,
                 caseExpr :: Expr, caseLoc :: Location}

data Pattern = PVar String
             | PApp NamePath [Pattern]
             | PAnn Pattern Type
             | PLoc Pattern Location

data Expr = EVar NamePath
          | ELam [(String, Maybe Type)] Expr
          | ECase Expr [Case]
          | EApp Expr [Expr]
          | EHandle Expr [FuncDef]
          | ESeq [Expr]
          | EAnn Expr Type
          | ELoc Expr Location

data TypeDef = TypeDef{typeName :: String, typeArgs :: [(String, Maybe Kind)],
                       typeCons :: [TypeCon], typeLoc :: Location}

data TypeCon = TypeCon{typeConName :: String, typeConArgs :: [Type],
                       typeConLoc :: Location}

data EffectDef = EffectDef{effectName :: String,
                           effectArgs :: [(String, Maybe Kind)],
                           effectIntfs :: [FuncDef], effectLoc :: Location}

data EffKind = EKStar
             | EKFunc [Kind] EffKind
             | EKLoc EffKind Location

data EffectType = EffVar String
                | EffApp String [Type]
                | EffList [EffectType]
                | EffAnn EffectType EffKind
                | EffLoc EffectType Location

data ImportStmt = ImportStmt{importStmt :: NamePath,
                             importAlias :: Maybe String,
                             importAttrs :: [NamedAttr], importLoc :: Location}

