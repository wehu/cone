{
module Cone.Parser.Lexer (tokenize, Token(..), Tok(..), AlexPosn(..)) where
}

%wrapper "posn"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-
  ($white # [\n])+				;
  "--".*				          ;
  [\; \n]                               { \p s -> (p, Semi) }
  module                                { \p s -> (p, Module) }
  import                                { \p s -> (p, Import) }
  func                                  { \p s -> (p, Func) }
  let                                   { \p s -> (p, Let) }
  in                                    { \p s -> (p, In) }
  $digit+                               { \p s -> (p, Int (read s)) }
  $alpha [$alpha $digit \_ \\ \']*      { \p s -> (p, Ident s) }

{
-- Each action has type :: String -> Token

-- The token type:
data Tok =
    Module          |
    Import          |
    Func            |
    Let             |
    In              |
    Ident String    |
    Int Int         |
    Semi
    deriving (Eq,Show)

type Token = (AlexPosn, Tok)

tokenize = alexScanTokens
}