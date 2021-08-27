{-# LANGUAGE LambdaCase #-}

module Cone.Parser.Parser (parse) where
import qualified Cone.Parser.AST as A
import qualified Cone.Parser.Lexer as L
import Data.Functor.Identity
import Unbound.Generics.LocallyNameless
import qualified Text.Parsec as P
import Data.List
import Text.Parsec.Pos (newPos)

type Parser a = P.ParsecT [L.Token] () Identity a

token :: (L.Tok -> Bool) -> (L.Tok -> a) -> Parser a
token test getVal = do
  pos <- P.getPosition
  P.tokenPrim (showTok pos) nextPos testTok
  where nextPos :: P.SourcePos -> L.Token -> [L.Token] -> P.SourcePos
        nextPos pos _ ((L.AlexPn _ l c, _) : _)
          = P.setSourceColumn (P.setSourceLine pos l) c
        nextPos pos _ [] = pos
        testTok (_, t) = if (test t) then Just (getVal t) else Nothing
        showTok pos (L.AlexPn _ l c, t) = 
          (show t) ++ "@" ++ (P.sourceName pos) ++ "[" ++ (show l) ++ ":" ++ (show c) ++ "]"

keyword :: L.Tok -> Parser L.Tok
keyword t = token (== t) (\ _ -> t)

symbol = keyword

kModule = keyword L.Module
kImport = keyword L.Import
kAs     = keyword L.As
kFunc   = keyword L.Func
kFn     = keyword L.Fn
kType   = keyword L.Type
kEffect = keyword L.Effect

semi = symbol L.Semi
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
backSlash = symbol L.Backslash
arrow = symbol L.Arrow
star = symbol L.Star

i8   = keyword L.I8
i16  = keyword L.I16
i32  = keyword L.I32
i64  = keyword L.I64
u8   = keyword L.U8
u16  = keyword L.U16
u32  = keyword L.U32
u64  = keyword L.U64
f16  = keyword L.F16
f32  = keyword L.F32
f64  = keyword L.F64
bf16 = keyword L.BF16
bool = keyword L.Pred

ident
  = token
      (\case
           (L.Ident _) -> True
           _ -> False)
      (\ (L.Ident n) -> n)

getPos :: Parser A.Location
getPos
  = do pos <- P.getPosition
       return $
         A.Location (P.sourceName pos) (P.sourceLine pos) (P.sourceColumn pos)

parens e = lParen *> e <* rParen

braces e = lBrace *> (P.optional semi) *> e <* (P.optional semi) <* rBrace

brackets e = lBracket *> e <* rBracket

namePath :: Parser A.NamePath
namePath = intercalate "\\" <$> P.sepBy1 ident backSlash

imports :: Parser [A.ImportStmt]
imports = P.many $ 
    f <$ kImport <*> namePath <*> getPos
      <*> (P.optionMaybe $ kAs *> ident)
      <* semi 
  where f n pos alias = A.ImportStmt n alias [] pos

kind :: Parser A.Kind
kind = (A.KStar <$ star
        P.<|> P.try (A.KFunc <$> parens (P.sepBy kind comma) <* arrow <*> kind))
        <*> getPos
       P.<|> parens kind

primType :: Parser A.PrimType
primType = A.I8 <$ i8
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

type_ :: Parser A.Type
type_ = (tann <$> 
         ((P.try (A.TApp <$> (s2n <$> namePath) <* less <*> (P.many1 type_) <* greater)
           P.<|> P.try (tfunc <$> parens (P.sepBy type_ comma) <* arrow <*> resultType)
           P.<|> (A.TVar <$> (s2n <$> ident))
           P.<|> (A.TPrim <$> primType))
          <*> getPos)) <*> (P.optionMaybe $ colon *> kind) <*> getPos
        P.<|> parens type_
  where tfunc args (effT, resultT) pos = A.TFunc args effT resultT pos
        tann t k pos = case k of
          Just k' -> A.TAnn t k' pos
          _ -> t
  

boundTVars :: Parser [A.TVar]
boundTVars = (brackets $ P.sepBy1 (s2n <$> ident) comma)
              P.<|> return []

resultType :: Parser (Maybe A.EffectType, A.Type)
resultType = (,) <$> (P.optionMaybe $ P.try $ effType <* P.lookAhead type_) <*> type_ 

effKind :: Parser A.EffKind
effKind = (A.EKStar <$ star
        P.<|> P.try (A.EKFunc <$> parens (P.sepBy kind comma) <* arrow <*> effKind))
        <*> getPos
       P.<|> parens effKind

effType :: Parser A.EffectType
effType = parens effType
          P.<|> (ekann <$>
           (((P.try $ A.EffApp <$> namePath <* less <*> (P.many1 type_) <* greater)
           P.<|> (A.EffList <$ less <*> (P.sepBy effType comma) <* greater)
           P.<|> (A.EffVar <$> ident)) <*> getPos)
             <*> (P.optionMaybe $ colon *> effKind) <*> getPos)
  where ekann t ek pos = case ek of
          Just ek' -> A.EffAnn t ek' pos
          _ -> t

funcArgs :: Parser [(String, Maybe A.Type)]
funcArgs = P.sepBy ((,) <$> ident <*> (P.optionMaybe $ colon *> type_)) comma

funcProto = f <$> getPos <*> boundTVars
         <*> parens funcArgs
         <*> (P.optionMaybe $ colon *> resultType)
  where f pos bound args resultT = case resultT of
           Just (effT, resT) -> (pos, bound, args, (effT, Just resT))
           _ -> (pos, bound, args, (Nothing, Nothing))

funcDef = (\f e -> (f, Just e)) <$> funcProto <*> braces expr

expr :: Parser A.Expr
expr = eapp <$> (parens expr
         P.<|> ((((\((pos, bound, args, (effT, resT)), e) -> A.ELam bound args effT resT e)
                   <$ kFn <*> funcDef)
                  P.<|> A.EVar <$> namePath) <*> getPos)) 
        <*> (P.optionMaybe $ parens $ P.sepBy expr comma) <*> getPos
  where eapp e args pos = case args of
                       Just args' -> A.EApp e args' pos
                       _ -> e

typeArgs :: Parser [(A.TVar, Maybe A.Kind)]
typeArgs = less *>
            (P.sepBy ((,) <$> (s2n <$> ident) <*> (P.optionMaybe $ colon *> kind)) comma) 
            <* greater

typeCon :: Parser A.TypeCon
typeCon = A.TypeCon <$> ident <*> 
            (parens (P.sepBy1 type_ comma)
             P.<|> return []) <*> getPos

typeDef :: Parser A.TypeDef
typeDef = A.TypeDef <$ kType <*> ident <*> boundTVars <*> typeArgs
    <*> braces (P.sepBy1 typeCon $ P.try $ semi <* P.notFollowedBy rBrace) <*> getPos

funcIntf :: Parser A.FuncIntf
funcIntf = A.FuncIntf <$ kFunc <*> ident <*> boundTVars <*>
      parens (P.sepBy type_ comma) <* colon <*> type_ <*> getPos

effectDef :: Parser A.EffectDef
effectDef = A.EffectDef <$ kEffect <*> ident <*> boundTVars <*> typeArgs
    <*> braces (P.sepBy1 funcIntf $ 
                P.try $ semi <* P.notFollowedBy rBrace) <*> getPos

func :: Parser A.FuncDef
func = f <$ kFunc <*> ident <*> funcDef
  where f n ((pos, bound, args, (effT, resT)), e) = A.FuncDef n bound args effT resT e pos

topStmt :: Parser A.TopStmt
topStmt = ((A.FDef <$> func)
           P.<|> A.TDef <$> typeDef
           P.<|> A.EDef <$> effectDef) <* semi

module_ :: Parser A.Module
module_ = f <$ kModule <*> namePath <*> getPos <* semi
            <*> imports
            <*> (P.many topStmt)
            <* P.eof
  where f n pos ims stmts = A.Module n [] [] ims stmts pos

parse :: String -> String -> Either P.ParseError A.Module
parse fn input
  = P.runParser module_ () fn (L.tokenize $ input ++ "\n")

