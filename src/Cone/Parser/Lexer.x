{
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}

module Cone.Parser.Lexer (tokenize, Token(..), Tok(..), AlexPosn(..)) where
import Data.Data
}

%wrapper "posn"

$alpha = [a-zA-Z]		-- alphabetic characters
$whitechar = [ \t\n\r\f\v]

$special   = [\(\)\,\;\[\]\`\{\}]

$ascdigit  = 0-9
$unidigit  = [] -- TODO
$digit     = [$ascdigit $unidigit]

$ascsymbol = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~]
$unisymbol = [] -- TODO
$symbol    = [$ascsymbol $unisymbol] # [$special \_\:\"\']
$large     = [A-Z \xc0-\xd6 \xd8-\xde]
$small     = [a-z \xdf-\xf6 \xf8-\xff \_]
$graphic   = [$small $large $symbol $digit $special \:\"\']
$octit	   = 0-7
$hexit     = [0-9 A-F a-f]
@decimal     = $digit+
@octal       = $octit+
@hexadecimal = $hexit+
@exponent    = [eE] [\-\+] @decimal
$cntrl   = [$large \@\[\\\]\^\_]
@ascii   = \^ $cntrl | NUL | SOH | STX | ETX | EOT | ENQ | ACK
	 | BEL | BS | HT | LF | VT | FF | CR | SO | SI | DLE
	 | DC1 | DC2 | DC3 | DC4 | NAK | SYN | ETB | CAN | EM
	 | SUB | ESC | FS | GS | RS | US | SP | DEL
$charesc = [abfnrtv\\\"\'\&]
@escape  = \\ ($charesc | @ascii | @decimal | o @octal | x @hexadecimal)
@gap     = \\ $whitechar+ \\
@string  = $graphic # [\"\\] | " " | @escape | @gap

tokens :-
  ($white # [\n])+				;
  \\\n                    ;
  "//"[^\n]*              ;
  [\; \n]+                              { \p s -> (p, Semi) }
  module                                { \p s -> (p, Module) }
  import                                { \p s -> (p, Import) }
  fun                                   { \p s -> (p, Func) }
  fn                                    { \p s -> (p, Fn) }
  as                                    { \p s -> (p, As) }
  var                                   { \p s -> (p, Let) }
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
  "<="                                  { \p s -> (p, Le) }
  ">="                                  { \p s -> (p, Ge) }
  \!                                    { \p s -> (p, Not) }
  "=="                                  { \p s -> (p, Eq) }
  "!="                                  { \p s -> (p, Ne) }
  "&&"                                  { \p s -> (p, And) }
  "||"                                  { \p s -> (p, Or) }
  \|                                    { \p s -> (p, Pipe) }
  "="                                   { \p s -> (p, Assign) }
  "+"                                   { \p s -> (p, Add) }
  "-"                                   { \p s -> (p, Sub) }
  "/"                                   { \p s -> (p, Div) }
  "%"                                   { \p s -> (p, Mod) }
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
  "str"                                 { \p s -> (p, Str) }
  "char"                                { \p s -> (p, Char) }
  "type"                                { \p s -> (p, Type) }
  "effect"                              { \p s -> (p, Effect) }
  "case"                                { \p s -> (p, Case) }
  "of"                                  { \p s -> (p, Of) }
  "if"                                  { \p s -> (p, If) }
  "else"                                { \p s -> (p, Else) }
  "while"                               { \p s -> (p, While) }
  @decimal 
    | 0[oO] @octal
    | 0[xX] @hexadecimal		            { \p s -> (p, LInt s) }
  @decimal \. @decimal @exponent?
    | @decimal @exponent	            	{ \p s -> (p, LFloat s) }
  \' ($graphic # [\'\\] | " " | @escape) \'
				                                { \p s -> (p, LChar s) }
  \" @string* \"	                    	{ \p s -> (p, LStr s) }
  $alpha [$alpha $digit \_]*            { \p s -> (p, Ident s) }

{
-- Each action has type :: String -> Token

-- The token type:
data Tok =
    Module          |
    Import          |
    Func            |
    Fn              |
    As              |
    Let             |
    Ident String    |
    LInt String     |
    LFloat String   | 
    LStr String     |
    LChar String    |
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
    Le              |
    Ge              |
    Eq              |
    Ne              |
    Not             |
    And             |
    Or              |
    Assign          |
    Add             |
    Sub             |
    Div             |
    Mod             |
    Pipe            |
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
    Pred            |
    Str             |
    Char            |
    Type            |
    Effect          |
    Case            |
    Of              |
    If              |
    Else            |
    While           |
    Unknown
  deriving (Eq, Ord, Show, Read, Data, Typeable)

type Token = (AlexPosn, Tok)

tokenize = alexScanTokens
}