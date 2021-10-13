{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Cone.Parser.Parser (parse) where

import qualified Cone.Parser.AST as A
import qualified Cone.Parser.Lexer as L
import Control.Lens
import Data.Functor
import Data.Functor.Identity
import Data.List
import qualified Text.Parsec as P
import qualified Text.Parsec.Expr as PE
import Text.Parsec.Pos (newPos)
import Text.Parsec.Prim (parserFail)
import Unbound.Generics.LocallyNameless

makePrisms ''L.Tok

type Parser a = P.ParsecT [L.Token] () Identity a

token :: (L.Tok -> Bool) -> (L.Token -> a) -> Parser a
token test getVal = do
  pos <- P.getPosition
  P.tokenPrim (showTok pos) nextPos testTok
  where
    nextPos :: P.SourcePos -> L.Token -> [L.Token] -> P.SourcePos
    nextPos pos _ ((L.AlexPn _ l c, _, _) : _) =
      P.setSourceColumn (P.setSourceLine pos l) c
    nextPos pos _ [] = pos
    testTok tok@(_, t, _) = if test t then Just (getVal tok) else Nothing
    showTok pos (L.AlexPn _ l c, _, s) =
      s ++ "@" ++ P.sourceName pos ++ "[" ++ show l ++ ":" ++ show c ++ "]"

keyword :: L.Tok -> Parser L.Tok
keyword t = token (== t) (const t)

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

kNum = keyword L.Num

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

at_ = symbol L.At

arrow = symbol L.Arrow

star = symbol L.Star

dot = symbol L.Dot

sharp = symbol L.Sharp

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

kAlias = keyword L.Alias

kDiff = keyword L.Diff

kAuto = keyword L.Auto

kWrt = keyword L.WRT

tokenP :: Monoid a => Prism' L.Tok a -> Parser String
tokenP p = token (not . isn't p) (\(_, _, s) -> s)

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

braces e = lBrace *> P.optional semi *> e <* P.optional semi <* rBrace

brackets e = lBracket *> e <* rBracket

angles e = less *> e <* greater

namePath :: Parser A.NamePath
namePath = intercalate "/" <$> P.sepBy1 ident dot

imports :: Parser [A.ImportStmt]
imports =
  P.many
    ( f <$ kImport <*> namePath <*> getPos
        <*> P.optionMaybe (kAs *> ident)
        <* semi P.<?> "import stmt"
    )
  where
    f n pos alias = A.ImportStmt n alias [] pos

kind :: Parser A.Kind
kind =
  (( A.KStar <$ (star P.<?> "star kind")
      P.<|> A.KNum <$ (kNum P.<?> "num kind")
      P.<|> A.KList <$ at_ <*> (brackets kind P.<?> "list kind")
      P.<|> P.try (A.KFunc <$> parens (P.sepBy kind comma) <* arrow <*> kind P.<?> "function kind")
  )
    <*> getPos
    P.<|> parens kind) P.<?> "type kind"

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
  [ [typePrefix sub "neg"],
    [ typeBinary star "mul" PE.AssocLeft,
      typeBinary div_ "div" PE.AssocLeft,
      typeBinary mod_ "mod" PE.AssocLeft
    ],
    [ typeBinary add "add" PE.AssocLeft,
      typeBinary sub "sub" PE.AssocLeft
    ]
  ]

typePrefix op name = PE.Prefix $ do
  op
  pos <- getPos
  return $ \i -> A.TApp (A.TVar (s2n name) pos) [i] pos

typeBinary op name =
  PE.Infix
    ( do
        op
        pos <- getPos
        return $
          \a b ->
            let args = a : [b]
             in A.TApp (A.TVar (s2n name) pos) args pos
    )

typeTerm :: Parser A.Type
typeTerm =
  ( tann
      <$> ( P.try
              ( tfunc
                  <$> boundTVars
                  <*> boundEffVars
                  <*> parens (P.sepBy type_ comma) <* arrow
                  <*> resultType
                  <*> getPos P.<?> "function type"
              )
              P.<|> (ttuple <$> parens (P.sepBy1 type_ comma) <*> getPos P.<?> "type tuple")
              P.<|> ( ( tapp <$> (A.TVar . s2n <$> namePath <*> getPos)
                          <*> P.optionMaybe (angles (P.sepBy type_ comma))
                          <*> getPos
                      )
                        P.<?> "application type or type variable"
                    )
              P.<|> (A.TPrim <$> primType <*> getPos P.<?> "primitive type")
              P.<|> (A.TNum <$> (Just . read <$> literalInt) <*> getPos P.<?> "number type")
              P.<|> (A.TNum Nothing <$ question <*> getPos P.<?> "unknown number type")
              P.<|> (A.TList <$ at_ <*> brackets (P.sepBy1 type_ comma) <*> getPos P.<?> "type list kind")
              P.<|> (tlist <$> brackets type_ <*> getPos P.<?> "type list")
          )
  )
    <*> P.optionMaybe (colon *> kind P.<?> "type kind annotation")
    <*> getPos
  where
    tapp n args pos =
      case args of
        Just args -> A.TApp n args pos
        Nothing -> n
    tfunc bvs evs args (effT, resultT) pos =
      let ft = A.TFunc args effT resultT pos
       in A.BoundEffVarType (bind evs $ A.BoundType (bind bvs ft) pos) pos
    tann t k pos = case k of
      Just k' -> A.TAnn t k' pos
      _ -> t
    tlist t pos = A.TApp (A.TVar (s2n "list") pos) [t] pos
    ttuple (t0 : t1 : ts) pos = A.TApp (A.TVar (s2n "pair") pos) [t0, ttuple (t1 : ts) pos] pos
    ttuple [t] pos = t
    ttuple _ _ = undefined

type_ :: Parser A.Type
type_ = PE.buildExpressionParser typeTable typeTerm P.<?> "type"

boundTVars :: Parser [(A.TVar, Maybe A.Kind)]
boundTVars =
  (angles (P.sepBy1 ((,) <$> (s2n <$> ident) <*> P.optionMaybe (colon *> kind P.<?> "type kind annotation")) comma) P.<?> "type variable list")
    P.<|> return []

boundEffVars :: Parser [A.EffVar]
boundEffVars =
  (brackets (P.sepBy1 (s2n <$> ident) comma) P.<?> "effect type variable list")
    P.<|> return []

resultType :: Parser (A.EffectType, A.Type)
resultType = (,) <$> (P.try (effType <* P.lookAhead type_) P.<|> A.EffList [] <$> getPos) <*> type_

effKind :: Parser A.EffKind
effKind =
  (( A.EKStar <$ (star P.<?> "effect star kind")
      P.<|> P.try (A.EKFunc <$> parens (P.sepBy kind comma) <* arrow <*> effKind P.<?> "effect function kind")
  )
    <*> getPos
    P.<|> parens effKind) P.<?> "effect kind"

effType :: Parser A.EffectType
effType =
  (parens effType
    P.<|> ( ( effapp <$> (A.EffVar . s2n <$> namePath <*> getPos)
                <*> P.optionMaybe (angles (P.sepBy1 type_ comma))
                <*> getPos P.<?> "effect application type"
            )
              P.<|> (brackets (A.EffList <$> P.sepBy effType comma) <*> getPos P.<?> "effect type list")
          )) P.<?> "effect type"
  where
    effapp n args pos =
      case args of
        Just args -> A.EffApp n args pos
        Nothing -> n

funcArgs :: Parser [(String, A.Type)]
funcArgs = P.sepBy ((,) <$> ident <*> (colon *> type_ P.<?> "type annotation")) comma P.<?> "function argument types"

funcProto =
  f <$> getPos <*> boundTVars <*> boundEffVars
    <*> parens funcArgs
    <*> (colon *> resultType P.<?> "result type") P.<?> "function prototype"
  where
    f pos bts bes args (effT, resT) = (pos, bts, bes, args, (effT, resT))

exprSeq = f <$> expr <*> P.optionMaybe (P.many1 $ P.try $ semi *> expr) <*> getPos P.<?> "expr sequence"
  where
    f e es pos = case es of
      Just es' -> A.ESeq (e : es') pos
      Nothing -> e

funcDef = (,) <$> funcProto <*> P.optionMaybe (braces exprSeq)

exprTable =
  [ [exprPrefix sub "____negative"],
    [exprBinary pipe_ "cons" PE.AssocLeft],
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
  return $ \i -> A.EApp False (A.EVar (s2n name) pos) [] [i] pos

exprBinary op name =
  PE.Infix
    ( do
        op
        pos <- getPos
        return $
          \a b ->
            let args = a : [b]
             in A.EApp False (A.EVar (s2n name) pos) [] args pos
    )

pat :: Parser A.Pattern
pat =
  (pcons
    <$> ( (ptuple <$> parens (P.sepBy1 pat comma) <*> getPos P.<?> "pattern tuple or single pattern")
            P.<|> ( papp <$> (A.EVar <$> (s2n <$> namePath) <*> getPos)
                      <*> P.optionMaybe (angles (P.sepBy type_ comma))
                      <*> P.optionMaybe (parens (P.sepBy pat comma))
                      <*> getPos
                      P.<?> "pattern application or variable"
                  )
            P.<|> (A.PExpr <$> expr <*> getPos P.<?> "pattern expr")
        )
    <*> P.optionMaybe (pipe_ *> pat P.<?> "pattern list cons")
    <*> getPos) P.<?> "pattern"
  where
    papp n targs pargs pos =
      if isn't _Nothing targs || isn't _Nothing pargs
        then A.PApp n (targs ^. non []) (pargs ^. non []) pos
        else
          let (A.EVar v pos) = n
           in A.PVar (s2n $ name2String v) pos
    ptuple (p0 : p1 : ps) pos = A.PApp (A.EVar (s2n "pair") pos) [] [p0, ptuple (p1 : ps) pos] pos
    ptuple [p] pos = p
    ptuple _ _ = undefined
    pcons p ps pos =
      case ps of
        Just ps -> A.PApp (A.EVar (s2n "cons") pos) [] [p, ps] pos
        Nothing -> p

literal =
  ( A.ELit <$ true <*> return "true" <*> (A.TPrim A.Pred <$> getPos)
      P.<|> A.ELit <$ false <*> return "false" <*> (A.TPrim A.Pred <$> getPos)
      P.<|> A.ELit <$ unit <*> return "unit" <*> (A.TPrim A.Unit <$> getPos)
      P.<|> A.ELit <$> literalInt <*> (colon *> type_ P.<|> A.TPrim A.I32 <$> getPos)
      P.<|> A.ELit <$> literalFloat <*> (colon *> type_ P.<|> A.TPrim A.F32 <$> getPos)
      P.<|> A.ELit <$> literalChar <*> (colon *> type_ P.<|> A.TPrim A.Ch <$> getPos)
      P.<|> A.ELit <$> literalStr <*> (colon *> type_ P.<|> A.TPrim A.Str <$> getPos)
  )
    <*> getPos P.<?> "literal"

tupleOrExpr :: Parser A.Expr
tupleOrExpr = etuple <$> parens (P.sepBy1 expr comma) <*> getPos P.<?> "tuple expression or single expression"
  where
    etuple (e0 : e1 : es) pos = A.EApp False (A.EVar (s2n "pair") pos) [] [e0, etuple (e1 : es) pos] pos
    etuple [e] pos = e
    etuple _ _ = undefined

lambdaExpr :: Parser A.Expr
lambdaExpr = f <$ kFn <*> funcDef <*> getPos P.<?> "lambda expression"
  where
    f ((pos, bts, bes, args, (effT, resT)), e) = A.ELam bts bes args effT resT e

varExpr :: Parser A.Expr
varExpr = A.ELet <$ kVar <*> pat <* assign_ <*> expr <* semi <*> exprSeq <*> return True <*> getPos P.<?> "var experssion"

valExpr :: Parser A.Expr
valExpr = A.ELet <$ kVal <*> pat <* assign_ <*> expr <* semi <*> exprSeq <*> return False <*> getPos P.<?> "val experssion"

caseExpr :: Parser A.Expr
caseExpr =
  A.ECase <$ kCase <*> expr
    <*> braces
      (P.sepBy1 (A.Case <$> pat <* arrow <*> return Nothing <*> braces exprSeq <*> getPos) $ P.try $ semi <* P.notFollowedBy rBrace)
    <*> getPos P.<?> "case expression"

whileExpr :: Parser A.Expr
whileExpr = A.EWhile <$ kWhile <*> expr <*> braces exprSeq <*> getPos P.<?> "while expression"

handleExpr :: Parser A.Expr
handleExpr = A.EHandle <$ kHandle <*> effType <*> braces exprSeq <* kWith <*> braces (P.sepBy1 handle $ P.try $ semi <* P.notFollowedBy rBrace) <*> getPos P.<?> "handle expression"

ifExpr :: Parser A.Expr
ifExpr = eif <$ kIf <*> expr <*> braces exprSeq <* kElse <*> braces exprSeq <*> getPos P.<?> "ifelse experssion"
  where
    eif c t f pos =
      A.ECase
        c
        [ A.Case (A.PExpr (A.ELit "true" (A.TPrim A.Pred pos) pos) pos) Nothing t pos,
          A.Case (A.PExpr (A.ELit "false" (A.TPrim A.Pred pos) pos) pos) Nothing f pos
        ]
        pos

varOrAssignExpr :: Parser A.Expr
varOrAssignExpr = varOrAssign <$> namePath <*> P.optionMaybe (assign_ *> expr) <*> getPos P.<?> "var or assign expression"
  where
    varOrAssign v e pos = case e of
      Nothing -> A.EVar (s2n v) pos
      Just e -> A.EApp False (A.EVar (s2n "____assign") pos) [] [A.EVar (s2n v) pos, e] pos

listExpr :: Parser A.Expr
listExpr = elist <$> brackets (P.sepBy expr comma) <*> getPos P.<?> "list expression"
  where
    elist (e : es) pos = A.EApp False (A.EVar (s2n "cons") pos) [] [e, elist es pos] pos
    elist [] pos = A.EApp False (A.EVar (s2n "nil") pos) [] [] pos

term :: Parser A.Expr
term =
  ( (,,)
      <$> ( ( (,,,,) <$> (kDiff $> True P.<|> return False)
                <*> ( tupleOrExpr
                        P.<|> lambdaExpr
                        P.<|> varExpr
                        P.<|> valExpr
                        P.<|> caseExpr
                        P.<|> whileExpr
                        P.<|> handleExpr
                        P.<|> ifExpr
                        P.<|> varOrAssignExpr
                        P.<|> listExpr
                        P.<|> literal
                    )
                <*> P.optionMaybe (P.try (angles (P.sepBy type_ comma P.<?> "application expression type argument list")))
                <*> P.optionMaybe (P.try (parens (P.sepBy expr comma P.<?> "application expression argument list")))
                <*> getPos
            )
              >>= eapp
          )
      <*> P.optionMaybe (colon *> type_ P.<?> "expression type annotation")
      <*> getPos
  )
    >>= eann
  where
    eapp (d, e, targs, args, pos)
      | isn't _Nothing targs || isn't _Nothing args = return $ A.EApp d e (targs ^. _Just) (args ^. _Just) pos
      | d = P.unexpected "diff for non function call"
      | otherwise = return e
    eann (e, t, pos) = case t of
      Just t' -> return $ A.EAnn e t' pos
      _ -> return e

handle :: Parser A.FuncDef
handle = do
  pos <- getPos
  A.FuncDef <$ kFunc <*> ident <*> boundTVars <*> boundEffVars <*> parens funcArgs
    <*> return (A.EffList [] pos)
    <*> return (A.TPrim A.Unit pos)
    <*> braces (Just <$> exprSeq)
    <*> getPos P.<?> "handle function"

expr :: Parser A.Expr
expr = PE.buildExpressionParser exprTable term P.<?> "expression"

typeArgs :: Parser [(A.TVar, Maybe A.Kind)]
typeArgs =
  (angles (P.sepBy ((,) <$> (s2n <$> ident) <*> P.optionMaybe (colon *> kind P.<?> "type kind annotation")) comma) P.<?> "type arguments")
    P.<|> return []

typeCon :: Parser A.TypeCon
typeCon =
  A.TypeCon <$> ident
    <*> ( parens (P.sepBy type_ comma)
            P.<|> return []
        )
    <*> getPos P.<?> "type constructor"

typeDef :: Parser A.TypeDef
typeDef =
  A.TypeDef <$ kType <*> ident <*> typeArgs
    <*> ( braces (P.sepBy1 typeCon $ P.try $ semi <* P.notFollowedBy rBrace)
            P.<|> return []
        )
    <*> getPos P.<?> "type definition"

typeAlias :: Parser A.TypeAlias
typeAlias =
  A.TypeAlias <$ kAlias <*> ident <*> typeArgs
    <* assign_ <*> type_ <*> getPos P.<?> "type alias"

funcIntf :: Parser A.FuncIntf
funcIntf =
  f <$ kFunc <*> ident <*> boundTVars <*> boundEffVars
    <*> parens (P.sepBy type_ comma) <*> (colon *> resultType P.<?> "type")
    <*> getPos P.<?> "effect interface definition"
  where
    f n bs es args (e, r) pos = A.FuncIntf n bs es args e r pos

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
    f n ((pos, bts, ets, args, (effT, resT)), e) = A.FuncDef n bts ets args effT resT e pos

diffDef :: Parser A.DiffDef
diffDef =
  A.DiffDef <$ kDiff <*> namePath <* kWrt
    <*> parens (P.sepBy1 ident comma)
    <* assign_
    <*> ( kAuto $> Nothing
            P.<|> Just <$> (A.EVar <$> (s2n <$> namePath) <*> getPos)
        )
    <*> getPos P.<?> "diff rule definition"

topStmt :: Parser A.TopStmt
topStmt =
  ( (A.FDef <$> func)
      P.<|> A.TDef <$> typeDef
      P.<|> A.TAlias <$> typeAlias
      P.<|> A.EDef <$> effectDef
      P.<|> A.DDef <$> diffDef
      P.<|> (A.ImplFDef <$ kImpl <*> (A.ImplFuncDef <$> func) P.<?> "function implementation")
  )
    <* semi

module_ :: Parser A.Module
module_ =
  f <$ P.optional semi <* kModule <*> namePath <*> getPos <* semi
    <*> imports
    <*> P.many topStmt
    <* P.eof
  where
    f n pos ims stmts = A.Module n [] [] ims stmts pos

parse :: String -> String -> Either P.ParseError A.Module
parse fn input =
  P.runParser module_ () fn (L.tokenize $ input ++ "\n")
