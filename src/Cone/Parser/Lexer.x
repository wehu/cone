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
  "i8"                                  { \p s -> (p, I8) }
  "i16"                                 { \p s -> (p, I16) }
  "i32"                                 { \p s -> (p, I32) }
  "i64"                                 { \p s -> (p, I64) }
  "u8"                                  { \p s -> (p, U8) }
  "u16"                                 { \p s -> (p, U16) }
  "u32"                                 { \p s -> (p, U32) }
  "u64"                                 { \p s -> (p, U64) }
  "f16"                                 { \p s -> (p, F16) }
  "f32"                                 { \p s -> (p, F32) }
  "f64"                                 { \p s -> (p, F64) }
  "bf16"                                { \p s -> (p, BF16) }
  "bool"                                { \p s -> (p, Pred) }
  $digit+                               { \p s -> (p, Int (read s)) }
  $alpha [$alpha $digit \_]*            { \p s -> (p, Ident s) }

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
    Star            |
    I8              |
    I16             |
    I32             |
    I64             |
    U8              |
    U16             |
    U32             |
    U64             |
    F16             |
    F32             |
    F64             |
    BF16            |
    Pred
    deriving (Eq,Show)

type Token = (AlexPosn, Tok)

tokenize = alexScanTokens
}