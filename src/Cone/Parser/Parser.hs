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
token test getVal = P.tokenPrim showTok nextPos testTok
  where nextPos :: P.SourcePos -> L.Token -> [L.Token] -> P.SourcePos
        nextPos pos _ ((L.AlexPn _ l c, _) : _)
          = P.setSourceColumn (P.setSourceLine pos l) c
        nextPos pos _ [] = pos
        testTok (_, t) = if (test t) then Just (getVal t) else Nothing
        showTok (L.AlexPn _ l c, t) = show t

keyword :: L.Tok -> Parser L.Tok
keyword t = token (== t) (\ _ -> t)

symbol = keyword

kModule = keyword L.Module
kImport = keyword L.Import
kAs     = keyword L.As

semi = symbol L.Semi

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

m :: Parser A.Module
m = f <$ kModule <*> ident <*> getPos <* semi <*> imports <* P.eof
  where f n pos ims = A.Module (namePath n) [] [] ims [] pos

parse :: String -> String -> Either P.ParseError A.Module
parse fn input
  = P.runParser m () fn (L.tokenize $ input ++ "\n")

