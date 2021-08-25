{
module Cone.Parser.Lexer (tokenize, Token(..)) where
}

%wrapper "posn"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-
  $white+				;
  "--".*				;
  module                                { \p s -> Module p }
  import                                { \p s -> Import p }
  let                                   { \p s -> Let p }
  in                                    { \p s -> In p }
  $digit+                               { \p s -> Int (read s) p }
  $alpha [$alpha $digit \_ \\ \']*      { \p s -> Ident s p }

{
-- Each action has type :: String -> Token

-- The token type:
data Token =
    Module AlexPosn         |
    Import AlexPosn         |
    Let AlexPosn            |
    In AlexPosn             |
    Ident String AlexPosn   |
    Int Int AlexPosn
    deriving (Eq,Show)

tokenize = alexScanTokens
}