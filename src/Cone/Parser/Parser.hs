{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Cone.Parser.Parser (parse) where

import qualified Cone.Parser.AST as A
import qualified Cone.Parser.Lexer as L
import Control.Lens
import Data.Functor.Identity
import Data.List
import qualified Text.Parsec as P
import qualified Text.Parsec.Expr as PE
import Text.Parsec.Pos (newPos)
import Unbound.Generics.LocallyNameless

makePrisms ''L.Tok

type Parser a = P.ParsecT [L.Token] () Identity a

token :: (L.Tok -> Bool) -> (L.Tok -> a) -> Parser a
token test getVal = do
  pos <- P.getPosition
  P.tokenPrim (showTok pos) nextPos testTok
  where
    nextPos :: P.SourcePos -> L.Token -> [L.Token] -> P.SourcePos
    nextPos pos _ ((L.AlexPn _ l c, _) : _) =
      P.setSourceColumn (P.setSourceLine pos l) c
    nextPos pos _ [] = pos
    testTok (_, t) = if (test t) then Just (getVal t) else Nothing
    showTok pos (L.AlexPn _ l c, t) =
      (show t) ++ "@" ++ (P.sourceName pos) ++ "[" ++ (show l) ++ ":" ++ (show c) ++ "]"

keyword :: L.Tok -> Parser L.Tok
keyword t = token (== t) (\_ -> t)

symbol = keyword

kModule = keyword L.Module

kImport = keyword L.Import

kAs = keyword L.As

kFunc = keyword L.Func

kFn = keyword L.Fn

kImpl = keyword L.Impl

kType = keyword L.Type

kEffect = keyword L.Effect

kHandle = keyword L.Handle

kWith = keyword L.With

kVar = keyword L.Var

kVal = keyword L.Val

kCase = keyword L.Case

kOf = keyword L.Of

kIf = keyword L.If

kElse = keyword L.Else

kWhile = keyword L.While

semi = P.many1 $ symbol L.Semi

lParen = symbol L.LParen

rParen = symbol L.RParen

lBrace = symbol L.LBrace

rBrace = symbol L.RBrace

lBracket = symbol L.LBracket

rBracket = symbol L.RBracket

colon = symbol L.Colon

comma = symbol L.Comma

less = symbol L.Less

greater = symbol L.Greater

le = symbol L.Le

ge = symbol L.Ge

eq = symbol L.Eq

ne = symbol L.Ne

not_ = symbol L.Not

and_ = symbol L.And

or_ = symbol L.Or

add = symbol L.Add

sub = symbol L.Sub

div_ = symbol L.Div

mod_ = symbol L.Mod

pipe_ = symbol L.Pipe

assign_ = symbol L.Assign

addAssign = symbol L.AddAssign

subAssign = symbol L.SubAssign

mulAssign = symbol L.MulAssign

divAssign = symbol L.DivAssign

modAssign = symbol L.ModAssign

backSlash = symbol L.Backslash

question = symbol L.Question

arrow = symbol L.Arrow

star = symbol L.Star

i8 = keyword L.I8

i16 = keyword L.I16

i32 = keyword L.I32

i64 = keyword L.I64

u8 = keyword L.U8

u16 = keyword L.U16

u32 = keyword L.U32

u64 = keyword L.U64

f16 = keyword L.F16

f32 = keyword L.F32

f64 = keyword L.F64

bf16 = keyword L.BF16

bool = keyword L.Pred

str = keyword L.Str

char = keyword L.Char

true = keyword L.True_

false = keyword L.False_

unit = keyword L.Unit

tokenP :: Monoid a => Prism' L.Tok a -> Parser a
tokenP p = token (not . isn't p) (view p)

ident = tokenP _Ident

literalInt = tokenP _LInt

literalFloat = tokenP _LFloat

literalStr = tokenP _LStr

literalChar = tokenP _LChar

getPos :: Parser A.Location
getPos =
  do
    pos <- P.getPosition
    return $
      A.Location (P.sourceName pos) (P.sourceLine pos) (P.sourceColumn pos)

parens e = lParen *> e <* rParen

braces e = lBrace *> (P.optional semi) *> e <* (P.optional semi) <* rBrace

brackets e = lBracket *> e <* rBracket

angles e = less *> e <* greater

namePath :: Parser A.NamePath
namePath = intercalate "/" <$> P.sepBy1 ident div_

imports :: Parser [A.ImportStmt]
imports =
  P.many (
    f <$ kImport <*> namePath <*> getPos
      <*> (P.optionMaybe $ kAs *> ident)
      <* semi P.<?> "import stmt")
  where
    f n pos alias = A.ImportStmt n alias [] pos

kind :: Parser A.Kind
kind =
  ( A.KStar <$ (star P.<?> "star kind")
      P.<|> P.try (A.KFunc <$> parens (P.sepBy kind comma) <* arrow <*> kind P.<?> "function kind")
  )
    <*> getPos
    P.<|> parens kind

primType :: Parser A.PrimType
primType =
  A.I8 <$ i8
    P.<|> (A.I16 <$ i16)
    P.<|> (A.I32 <$ i32)
    P.<|> (A.I64 <$ i64)
    P.<|> (A.U8 <$ u8)
    P.<|> (A.U16 <$ u16)
    P.<|> (A.U32 <$ u32)
    P.<|> (A.U64 <$ u64)
    P.<|> (A.F16 <$ f16)
    P.<|> (A.F32 <$ f32)
    P.<|> (A.F64 <$ f64)
    P.<|> (A.BF16 <$ bf16)
    P.<|> (A.Pred <$ bool)
    P.<|> (A.Str <$ str)
    P.<|> (A.Unit <$ unit)

typeTable =
  [ [ typeBinary star "____mul" PE.AssocLeft,
      typeBinary div_ "____div" PE.AssocLeft,
      typeBinary mod_ "____mod" PE.AssocLeft
    ],
    [ typeBinary add "____add" PE.AssocLeft,
      typeBinary sub "____sub" PE.AssocLeft
    ]
  ]

typeBinary op name assoc =
  PE.Infix
    ( do
        op
        pos <- getPos
        return $
          \a b ->
            let args = a : b : []
             in A.TApp (s2n name) args pos
    )
    assoc

typeTerm :: Parser A.Type
typeTerm =
  ( tann
      <$> ( ( P.try ((A.TApp <$> (s2n <$> namePath) <*> angles (P.sepBy1 type_ comma)) P.<?> "application type")
                P.<|> P.try (tfunc <$> (angles (P.sepBy1 (s2n <$> ident) comma)
                                        P.<|> return [])
                                       <*> parens (P.sepBy type_ comma) <* arrow <*> resultType P.<?> "function type")
                P.<|> (A.TVar <$> (s2n <$> ident) P.<?> "type variable")
                P.<|> (A.TPrim <$> primType P.<?> "primitive type")
                P.<|> (A.TNum <$> (Just . read <$> literalInt) P.<?> "number type")
                P.<|> (A.TNum Nothing <$ question P.<?> "unknown number type")
                P.<|> (tList <$> brackets (P.sepBy1 type_ comma) P.<?> "type list")
            )
              <*> getPos
          )
  )
    <*> (P.optionMaybe $ colon *> kind)
    <*> getPos
    P.<|> parens type_
  where
    tfunc bvs args (effT, resultT) pos = 
      let ft = A.TFunc args effT resultT pos
       in if bvs == [] then ft
          else A.BoundType (bind bvs ft) pos
    tann t k pos = case k of
      Just k' -> A.TAnn t k' pos
      _ -> t
    tList (t : []) pos = t
    tList (t : ts) pos = A.TApp (s2n "____pair") [t, (tList ts pos)] pos

type_ :: Parser A.Type
type_ = PE.buildExpressionParser typeTable typeTerm

boundTVars :: Parser [A.TVar]
boundTVars =
  ((angles $ P.sepBy1 (s2n <$> ident) comma) P.<?> "type variable list")
    P.<|> return []

resultType :: Parser (A.EffectType, A.Type)
resultType = (,) <$> ((P.try $ effType <* P.lookAhead type_) P.<|> (A.EffList [] Nothing) <$> getPos) <*> type_

effKind :: Parser A.EffKind
effKind =
  ( A.EKStar <$ (star P.<?> "eff star kind")
      P.<|> P.try (A.EKFunc <$> parens (P.sepBy kind comma) <* arrow <*> effKind P.<?> "eff function kind")
  )
    <*> getPos
    P.<|> parens effKind

effType :: Parser A.EffectType
effType =
  parens effType
    P.<|> ( ekann
              <$> ( ( (P.try (A.EffApp <$> namePath <*> angles (P.sepBy1 type_ comma) P.<?> "eff application type"))
                        P.<|> ((brackets (A.EffList <$> (P.sepBy effType comma) <*> (P.optionMaybe $ pipe_ *> (s2n <$> ident)))) P.<?> "eff type list")
                    )
                      <*> getPos
                  )
              <*> (P.optionMaybe (colon *> effKind P.<?> "eff type annotation"))
              <*> getPos
          )
  where
    ekann t ek pos = case ek of
      Just ek' -> A.EffAnn t ek' pos
      _ -> t

funcArgs :: Parser [(String, A.Type)]
funcArgs = (P.sepBy ((,) <$> ident <* colon <*> type_) comma) P.<?> "function argument types"

funcProto =
  f <$> getPos <*> boundTVars
    <*> parens funcArgs
    <* colon
    <*> resultType P.<?> "function prototype"
  where
    f pos bound args (effT, resT) = (pos, bound, args, (effT, resT))

exprSeq = f <$> expr <*> P.optionMaybe (P.many1 $ P.try $ semi *> expr) <*> getPos P.<?> "expr sequence"
  where
    f e es pos = case es of
      Just es' -> A.ESeq (e : es') pos
      Nothing -> e

funcDef = (,) <$> funcProto <*> (P.optionMaybe $ braces exprSeq)

tcExprTable =
  [ [tcExprPrefix sub "-"],
    [ tcExprBinary star "*" PE.AssocLeft,
      tcExprBinary div_ "/" PE.AssocLeft,
      tcExprBinary mod_ "%" PE.AssocLeft
    ],
    [ tcExprBinary add "+" PE.AssocLeft,
      tcExprBinary sub "/" PE.AssocLeft
    ],
    [ tcExprBinary less "<" PE.AssocLeft,
      tcExprBinary greater ">" PE.AssocLeft,
      tcExprBinary le "<=" PE.AssocLeft,
      tcExprBinary ge ">=" PE.AssocLeft
    ],
    [ tcExprBinary eq "==" PE.AssocLeft,
      tcExprBinary ne "!=" PE.AssocLeft
    ],
    [tcExprPrefix not_ "!"],
    [ tcExprBinary and_ "&&" PE.AssocLeft,
      tcExprBinary or_ "||" PE.AssocLeft
    ]
  ]

tcExprPrefix op name = PE.Prefix $ do
  op
  pos <- getPos
  return $ \i -> A.TCApp name [i] pos

tcExprBinary op name assoc =
  PE.Infix
    ( do
        op
        pos <- getPos
        return $
          \a b ->
            let args = a : b : []
             in A.TCApp name args pos
    )
    assoc

tcAccess = A.TCAccess <$> ident <*> brackets (P.sepBy1 (s2n <$> ident) comma) <*> getPos P.<?> "tc access"

tcTerm = parens tc
  P.<|> P.try tcAccess
  P.<|> P.try (A.TCApp <$> ident <*> parens (P.sepBy1 tc comma) <*> getPos P.<?> "tc application")
  P.<|> (A.TCVar <$> ident <*> getPos P.<?> "variable")

tc :: Parser A.TCExpr
tc = brackets $
       f <$> tcAccess <*>
        (assign_ *> return "="
        P.<|> addAssign *> return "+="
        P.<|> subAssign *> return "-="
        P.<|> mulAssign *> return "*="
        P.<|> divAssign *> return "/="
        P.<|> modAssign *> return "%=") 
        <*> PE.buildExpressionParser tcExprTable tcTerm <*> getPos
  where f a op e pos = A.TCApp op [a, e] pos

exprTable =
  [ [exprPrefix sub "____negative"],
    [ exprBinary star "____mul" PE.AssocLeft,
      exprBinary div_ "____div" PE.AssocLeft,
      exprBinary mod_ "____mod" PE.AssocLeft
    ],
    [ exprBinary add "____add" PE.AssocLeft,
      exprBinary sub "____sub" PE.AssocLeft
    ],
    [ exprBinary less "____lt" PE.AssocLeft,
      exprBinary greater "____gt" PE.AssocLeft,
      exprBinary le "____le" PE.AssocLeft,
      exprBinary ge "____ge" PE.AssocLeft
    ],
    [ exprBinary eq "____eq" PE.AssocLeft,
      exprBinary ne "____ne" PE.AssocLeft
    ],
    [exprPrefix not_ "____not"],
    [ exprBinary and_ "____and" PE.AssocLeft,
      exprBinary or_ "____or" PE.AssocLeft
    ]
  ]

exprPrefix op name = PE.Prefix $ do
  op
  pos <- getPos
  return $ \i -> A.EApp (A.EVar name pos) [] [i] pos

exprBinary op name assoc =
  PE.Infix
    ( do
        op
        pos <- getPos
        return $
          \a b ->
            let args = a : b : []
             in A.EApp (A.EVar name pos) [] args pos
    )
    assoc

pat :: Parser A.Pattern
pat =
  parens pat
    P.<|> ((P.try (A.PApp <$> namePath <*> (angles (P.sepBy1 type_ comma) P.<|> return []) <*> parens (P.sepBy1 pat comma) <*> getPos)) P.<?> "pattern application")
    P.<|> ((P.try (A.PApp <$> namePath <*> angles (P.sepBy1 type_ comma) <*> return [] <*> getPos)) P.<?> "pattern application")
    P.<|> (A.PVar <$> ident <*> getPos P.<?> "pattern variable")
    P.<|> (A.PExpr <$> literal <*> getPos P.<?> "pattern literal")

literal =
  ( A.ELit <$ true <*> return "true" <*> ((A.TPrim A.Pred) <$> getPos)
      P.<|> A.ELit <$ false <*> return "false" <*> ((A.TPrim A.Pred) <$> getPos)
      P.<|> A.ELit <$> literalInt <*> (colon *> type_ P.<|> (A.TPrim A.I32) <$> getPos)
      P.<|> A.ELit <$> literalFloat <*> (colon *> type_ P.<|> (A.TPrim A.F32) <$> getPos)
      P.<|> A.ELit <$> literalChar <*> (colon *> type_ P.<|> (A.TPrim A.Ch) <$> getPos)
      P.<|> A.ELit <$> literalStr <*> (colon *> type_ P.<|> (A.TPrim A.Str) <$> getPos)
  )
    <*> getPos P.<?> "literal"

term :: Parser A.Expr
term =
  eapp
    <$> ( eann
            <$> ( parens expr
                    P.<|> ( ( ( (\((pos, bound, args, (effT, resT)), e) -> A.ELam bound args effT resT e)
                                  <$ kFn <*> funcDef P.<?> "lambda expression"
                              )
                                P.<|> (A.ELet <$ kVar <*> pat <* assign_ <*> expr <*> return True P.<?> "var experssion")
                                P.<|> (A.ELet <$ kVal <*> pat <* assign_ <*> expr <*> return False P.<?> "val experssion")
                                P.<|> (A.ECase <$ kCase <*> expr
                                  <*> braces
                                    (P.sepBy1 (A.Case <$> pat <* arrow <*> return Nothing <*> braces exprSeq <*> getPos) $ P.try $ semi <* P.notFollowedBy rBrace) P.<?> "case expression")
                                P.<|> (A.EWhile <$ kWhile <*> term <*> braces exprSeq P.<?> "while expression")
                                P.<|> (A.EHandle <$ kHandle <*> effType <*> braces exprSeq <* kWith <*> (braces $ P.sepBy1 func $ P.try $ semi <* P.notFollowedBy rBrace) P.<?> "handle expression")
                                P.<|> (eif <$ kIf <*> term <*> braces exprSeq <* kElse <*> braces exprSeq P.<?> "ifelse experssion")
                                P.<|> (varOrAssign <$> namePath <*> (P.optionMaybe $ assign_ *> expr) P.<?> "assign expression")
                                P.<|> (A.ETC <$> tc P.<?> "tc expression")
                            )
                              <*> getPos
                          )
                    P.<|> literal
                )
            <*> (P.optionMaybe (colon *> type_ P.<?> "expression type annotation"))
            <*> getPos
        )
    <*> (P.optionMaybe $ angles (P.sepBy type_ comma P.<?> "application expression type argument list"))
    <*> (P.optionMaybe $ parens (P.sepBy expr comma P.<?> "application expression argument list"))
    <*> getPos
  where
    eapp e targs args pos =
      if (isn't _Nothing targs) || (isn't _Nothing args)
      then A.EApp e (targs ^._Just) (args ^._Just) pos
      else e
    eann e t pos = case t of
      Just t' -> A.EAnn e t' pos
      _ -> e
    eif c t f pos =
      A.ECase
        c
        [ A.Case (A.PExpr (A.ELit "true" (A.TPrim A.Pred pos) pos) pos) Nothing t pos,
          A.Case (A.PExpr (A.ELit "false" (A.TPrim A.Pred pos) pos) pos) Nothing f pos
        ]
        pos
    varOrAssign v e pos = case e of
      Nothing -> A.EVar v pos
      Just e -> A.EApp (A.EVar "____assign" pos) [] [A.EVar v pos, e] pos

expr :: Parser A.Expr
expr = PE.buildExpressionParser exprTable term

typeArgs :: Parser [(A.TVar, Maybe A.Kind)]
typeArgs =
  ( (angles (P.sepBy ((,) <$> (s2n <$> ident) <*> (P.optionMaybe $ colon *> kind)) comma)) P.<?> "type arguments")
    P.<|> return []

typeCon :: Parser A.TypeCon
typeCon =
  A.TypeCon <$> ident
    <*> ( parens (P.sepBy type_ comma)
            P.<|> return []
        )
    <*> getPos P.<?> "tyue constructor"

typeDef :: Parser A.TypeDef
typeDef =
  A.TypeDef <$ kType <*> ident <*> typeArgs
    <*> (braces (P.sepBy1 typeCon $ P.try $ semi <* P.notFollowedBy rBrace)
         P.<|> return [])
    <*> getPos P.<?> "type definition"

funcIntf :: Parser A.FuncIntf
funcIntf =
  f <$ kFunc <*> ident <*> boundTVars
    <*> parens (P.sepBy type_ comma) <* colon
    <*> resultType
    <*> getPos P.<?> "effect interface definition"
  where
    f n bs args (e, r) pos = A.FuncIntf n bs args e r pos

effectDef :: Parser A.EffectDef
effectDef =
  A.EffectDef <$ kEffect <*> ident <*> typeArgs
    <*> braces
      ( P.sepBy1 funcIntf $
          P.try $ semi <* P.notFollowedBy rBrace
      )
    <*> getPos P.<?> "effect type definition"

func :: Parser A.FuncDef
func = f <$ kFunc <*> ident <*> funcDef P.<?> "function definition"
  where
    f n ((pos, bound, args, (effT, resT)), e) = A.FuncDef n bound args effT resT e pos

topStmt :: Parser A.TopStmt
topStmt =
  ( (A.FDef <$> func)
      P.<|> A.TDef <$> typeDef
      P.<|> A.EDef <$> effectDef
      P.<|> (A.ImplFDef <$ kImpl <*> (A.ImplFuncDef <$> func) P.<?> "function implementation")
  )
    <* semi

module_ :: Parser A.Module
module_ =
  f <$ (P.optional semi) <* kModule <*> namePath <*> getPos <* semi
    <*> imports
    <*> (P.many topStmt)
    <* P.eof
  where
    f n pos ims stmts = A.Module n [] [] ims stmts pos

parse :: String -> String -> Either P.ParseError A.Module
parse fn input =
  P.runParser module_ () fn (L.tokenize $ input ++ "\n")
