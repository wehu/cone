{
module Cone.Parser.Lexer (tokenize, Token(..), Tok(..), AlexPosn(..)) where
}

%wrapper "posn"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-
  ($white # [\n])+				;
  "--".*				          ;
  [\; \n]+                              { \p s -> (p, Semi) }
  module                                { \p s -> (p, Module) }
  import                                { \p s -> (p, Import) }
  fun                                   { \p s -> (p, Func) }
  as                                    { \p s -> (p, As) }
  let                                   { \p s -> (p, Let) }
  in                                    { \p s -> (p, In) }
  \(                                    { \p s -> (p, LParen) }
  \)                                    { \p s -> (p, RParen) }
  \{                                    { \p s -> (p, LBrace) }
  \}                                    { \p s -> (p, RBrace) }
  \[                                    { \p s -> (p, LBracket) }
  \]                                    { \p s -> (p, RBracket) }
  \:                                    { \p s -> (p, Colon) }
  \,                                    { \p s -> (p, Comma) }
  \<                                    { \p s -> (p, Less) }
  \>                                    { \p s -> (p, Greater) }
  \\                                    { \p s -> (p, Backslash) }
  "->"                                  { \p s -> (p, Arrow) }
  \*                                    { \p s -> (p, Star) }
  $digit+                               { \p s -> (p, Int (read s)) }
  $alpha [$alpha $digit \_ \- \']*      { \p s -> (p, Ident s) }

{
-- Each action has type :: String -> Token

-- The token type:
data Tok =
    Module          |
    Import          |
    Func            |
    As              |
    Let             |
    In              |
    Ident String    |
    Int Int         |
    Semi            |
    LParen          |
    RParen          |
    LBrace          |
    RBrace          |
    LBracket        |
    RBracket        |
    Colon           |
    Comma           |
    Less            |
    Greater         |
    Backslash       |
    Arrow           |
    Star
    deriving (Eq,Show)

type Token = (AlexPosn, Tok)

tokenize = alexScanTokens
}