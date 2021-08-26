{-# LANGUAGE LambdaCase #-}

module Cone.Parser.Parser (parse) where
import qualified Cone.Parser.AST as A
import qualified Cone.Parser.Lexer as L
import Data.Functor.Identity

import qualified Text.Parsec as P
import Text.Parsec.Pos (newPos)
import Data.List.Split

newtype Env = Env{sourceFile :: String}

type Parser a = P.ParsecT [L.Token] Env Identity a

token :: (L.Tok -> Bool) -> (L.Tok -> a) -> Parser a
token test getVal = P.tokenPrim show nextPos testTok
  where nextPos :: P.SourcePos -> L.Token -> [L.Token] -> P.SourcePos
        nextPos pos _ ((L.AlexPn _ l c, _) : _)
          = P.setSourceColumn (P.setSourceLine pos l) c
        nextPos pos _ [] = pos
        testTok (_, t) = if (test t) then Just (getVal t) else Nothing

keyword :: L.Tok -> Parser L.Tok
keyword t = token (== t) (\ _ -> t)

kmodule = keyword L.Module
semi = keyword L.Semi

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

m :: Parser A.Module
m = f <$ kmodule <*> ident <*> getPos <* (P.many semi) <* P.eof
  where f n pos = A.Module (splitOn "\\" n) [] [] [] [] pos

parse :: String -> String -> Either P.ParseError A.Module
parse fn input
  = P.runParser m Env{sourceFile = fn} fn (L.tokenize $ input ++ "\n")

