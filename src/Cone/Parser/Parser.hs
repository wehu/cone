{-# LANGUAGE LambdaCase #-}

module Cone.Parser.Parser (parse) where
import qualified Cone.Parser.AST as A
import qualified Cone.Parser.Lexer as L
import Data.Functor.Identity

import qualified Text.Parsec as P
import Text.Parsec.Pos (newPos)
import Data.List.Split

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

semi = symbol L.Semi
lParen = symbol L.LParen
rParen = symbol L.RParen
lBrace = symbol L.LBrace
rBrace = symbol L.RBrace
lBracket = symbol L.LBracket
rBracket = symbol L.RBracket
colon = symbol L.Colon
comma = symbol L.Comma

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

namePath :: String -> [String]
namePath = splitOn "\\"

imports :: Parser [A.ImportStmt]
imports = P.many $ 
    f <$ kImport <*> ident <*> getPos
      <*> (P.optionMaybe $ kAs *> ident)
      <* semi 
  where f n pos alias = A.ImportStmt (namePath n) alias [] pos

type_ :: Parser A.Type
type_ = A.TVar <$> ident <*> getPos

effType :: Parser A.EffectType
effType = A.EffVar <$> ident <*> getPos

funcArgs :: Parser [(String, A.Type)]
funcArgs = P.sepBy ((,) <$> ident <* colon <*> type_) comma

expr :: Parser A.Expr
expr = (\n p -> A.EVar (namePath n) p) <$> ident <*> getPos <* semi

func :: Parser A.FuncDef
func = f <$ kFunc <*> ident <*> getPos
         <* lParen <*> funcArgs <* rParen
         <* colon <*> (P.optionMaybe $ P.try $ effType <* P.lookAhead type_)
         <*> type_ <* lBrace <* semi <*> expr <* rBrace
  where f n pos args effT resT e = A.FuncDef n args effT resT e pos

topStmt :: Parser A.TopStmt
topStmt = ((A.FDef <$> func)) <* semi

module_ :: Parser A.Module
module_ = f <$ kModule <*> ident <*> getPos <* semi
            <*> imports
            <*> (P.many topStmt)
            <* P.eof
  where f n pos ims stmts = A.Module (namePath n) [] [] ims stmts pos

parse :: String -> String -> Either P.ParseError A.Module
parse fn input
  = P.runParser module_ () fn (L.tokenize $ input ++ "\n")

