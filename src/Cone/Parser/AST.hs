module Cone.Parser.AST
       (NamePath, Location(..), Module(..), NamedAttr, Attr(..), TopStmt(..),
        FuncDef(..), Type(..), Kind(..), Case(..), Pattern(..), Expr(..),
        TypeDef(..), TypeCon(..), EffectDef(..), EffKind(..), EffectType(..),
        ImportStmt(..))
       where
import Data.Maybe

type NamePath = [String]

data Location = Location{fileName :: String, lineNo :: !Int, colNo :: !Int}
                  deriving (Eq, Show)

data Module = Module{moduleName :: NamePath, moduleAttrs :: [NamedAttr],
                     moduleExports :: [String], topStmts :: [TopStmt],
                     moduleLoc :: Location}
                deriving (Eq, Show)

type NamedAttr = (String, Attr)

data Attr = String
          | Int
          | Bool
              deriving (Eq, Show)

data TopStmt = FDef FuncDef
             | TDef TypeDef
             | EDef EffectDef
             | Import ImportStmt
                 deriving (Eq, Show)

data FuncDef = FuncDef{funcName :: String, funcType :: Maybe Type,
                       funcCases :: [Case], funcLoc :: Location}
                 deriving (Eq, Show)

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
              deriving (Eq, Show)

data Kind = KStar
          | KFunc Kind Kind
          | KLoc Kind Location
              deriving (Eq, Show)

data Case = Case{casePattern :: Maybe Pattern, caseGuard :: Maybe Expr,
                 caseExpr :: Expr, caseLoc :: Location}
              deriving (Eq, Show)

data Pattern = PVar String
             | PApp NamePath [Pattern]
             | PAnn Pattern Type
             | PLoc Pattern Location
                 deriving (Eq, Show)

data Expr = EVar NamePath
          | ELam [(String, Maybe Type)] Expr
          | ECase Expr [Case]
          | EApp Expr [Expr]
          | ELet [(String, Expr)] Expr
          | EHandle Expr [FuncDef]
          | ESeq [Expr]
          | EAnn Expr Type
          | ELoc Expr Location
              deriving (Eq, Show)

data TypeDef = TypeDef{typeName :: String, typeArgs :: [(String, Maybe Kind)],
                       typeCons :: [TypeCon], typeLoc :: Location}
                 deriving (Eq, Show)

data TypeCon = TypeCon{typeConName :: String, typeConArgs :: [Type],
                       typeConLoc :: Location}
                 deriving (Eq, Show)

data EffectDef = EffectDef{effectName :: String,
                           effectArgs :: [(String, Maybe Kind)],
                           effectIntfs :: [FuncDef], effectLoc :: Location}
                   deriving (Eq, Show)

data EffKind = EKStar
             | EKFunc [Kind] EffKind
             | EKLoc EffKind Location
                 deriving (Eq, Show)

data EffectType = EffVar String
                | EffApp String [Type]
                | EffList [EffectType]
                | EffAnn EffectType EffKind
                | EffLoc EffectType Location
                    deriving (Eq, Show)

data ImportStmt = ImportStmt{importStmt :: NamePath,
                             importAlias :: Maybe String,
                             importAttrs :: [NamedAttr], importLoc :: Location}
                    deriving (Eq, Show)

