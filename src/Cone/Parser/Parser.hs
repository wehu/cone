{-# LANGUAGE LambdaCase #-}
module Cone.Parser.Parser(

) where

import qualified Text.Parsec as P
import Text.Parsec.Pos (newPos)
import qualified Cone.Parser.AST as A
import qualified Cone.Parser.Lexer as L
import Data.Functor.Identity

newtype Env = Env {sourceFile :: String}

type Parser a =  P.ParsecT [L.Token] Env Identity a

getSourceFile :: Parser String
getSourceFile = sourceFile <$> P.getState

setSourceFile :: String -> Parser ()
setSourceFile f = do
    env <- P.getState
    P.putState $ env{sourceFile=f}

token :: (L.Tok -> Bool) -> (L.Tok -> a) -> Parser a
token test getVal = P.tokenPrim show nextPos testTok
    where
        nextPos :: P.SourcePos -> L.Token -> [L.Token] -> P.SourcePos
        nextPos pos _ ((L.AlexPn _ l c, _):_) = P.setSourceColumn (P.setSourceLine pos l) c
        nextPos pos _ []                      = pos
        testTok (_, t) = if (test t) then Just (getVal t) else Nothing

m = token (== L.Module) (\_ -> L.Module)
ident = token (\case 
                  (L.Ident _) -> True
                  _ -> False) 
              (\(L.Ident n) -> n)

getPos :: Parser A.Location
getPos = do
    pos <- P.getPosition
    return $ A.Location (P.sourceName pos) (P.sourceLine pos) (P.sourceColumn pos)

top :: Parser A.Module
top = f <$ m <*> ident <*> getPos
    where
        f n pos = A.Module [n] [] [] [] pos

parse :: String -> IO (Either P.ParseError A.Module)
parse fn = do
    input <- readFile fn
    return $ P.runParser top Env{sourceFile=fn} fn (L.tokenize input)

