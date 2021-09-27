{
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}

module Cone.Parser.Lexer (tokenize, Token(..), Tok(..), AlexPosn(..)) where
import Data.Data
import Debug.Trace
}

%wrapper "monad"

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
@comment = . | $white | \n

tokens :-
  ($white # [\n])+				;
  \\\n                    ;
  "//"[^\n]*              ;
  [\; \n]+                              { mkL Semi }
  module                                { mkL Module }
  import                                { mkL Import }
  fun                                   { mkL Func }
  fn                                    { mkL Fn }
  as                                    { mkL As }
  var                                   { mkL Var }
  val                                   { mkL Val }
  \(                                    { mkL LParen }
  \)                                    { mkL RParen }
  \{                                    { mkL LBrace }
  \}                                    { mkL RBrace }
  \[                                    { mkL LBracket }
  \]                                    { mkL RBracket }
  \:                                    { mkL Colon }
  \,                                    { mkL Comma }
  \<                                    { mkL Less }
  \>                                    { mkL Greater }
  "<="                                  { mkL Le }
  ">="                                  { mkL Ge }
  \!                                    { mkL Not }
  "=="                                  { mkL Eq }
  "!="                                  { mkL Ne }
  "&&"                                  { mkL And }
  "||"                                  { mkL Or }
  \|                                    { mkL Pipe }
  "="                                   { mkL Assign }
  "+="                                  { mkL AddAssign }
  "-="                                  { mkL SubAssign }
  "*="                                  { mkL MulAssign }
  "/="                                  { mkL DivAssign }
  "%="                                  { mkL ModAssign }
  "+"                                   { mkL Add }
  "-"                                   { mkL Sub }
  "/"                                   { mkL Div }
  "%"                                   { mkL Mod }
  "#"                                   { mkL Sharp }
  \\                                    { mkL Backslash }
  "->"                                  { mkL Arrow }
  \*                                    { mkL Star }
  \?                                    { mkL Question }
  \@                                    { mkL At }
  "i8"                                  { mkL I8 }
  "i16"                                 { mkL I16 }
  "i32"                                 { mkL I32 }
  "i64"                                 { mkL I64 }
  "u8"                                  { mkL U8 }
  "u16"                                 { mkL U16 }
  "u32"                                 { mkL U32 }
  "u64"                                 { mkL U64 }
  "f16"                                 { mkL F16 }
  "f32"                                 { mkL F32 }
  "f64"                                 { mkL F64 }
  "bf16"                                { mkL BF16 }
  "bool"                                { mkL Pred }
  "str"                                 { mkL Str }
  "char"                                { mkL Char }
  "type"                                { mkL Type }
  "effect"                              { mkL Effect }
  "case"                                { mkL Case }
  "of"                                  { mkL Of }
  "if"                                  { mkL If }
  "else"                                { mkL Else }
  "while"                               { mkL While }
  "num"                                 { mkL Num }
  "unit"                                { mkL Unit }
  "true"                                { mkL True_ }
  "false"                               { mkL False_ }
  "handle"                              { mkL Handle }
  "with"                                { mkL With }
  "impl"                                { mkL Impl }
  @decimal 
    | 0[oO] @octal
    | 0[xX] @hexadecimal		            { mkL LInt }
  @decimal \. @decimal @exponent?
    | @decimal @exponent	            	{ mkL LFloat }
  \' ($graphic # [\'\\] | " " | @escape) \'
				                                { mkL LChar }
  \" @string* \"	                    	{ mkL LStr }
  [$alpha \_] [$alpha $digit \_]*       { mkL Ident }

{
-- Each action has type :: String -> Token

-- The token type:
data Tok =
    Module          |
    Import          |
    Func            |
    Fn              |
    As              |
    Var             |
    Val             |
    Ident           |
    LInt            |
    LFloat          | 
    LStr            |
    LChar           |
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
    At              |
    Sharp           |
    Assign          |
    AddAssign       |
    SubAssign       |
    MulAssign       |
    DivAssign       |
    ModAssign       |
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
    Unit            |
    True_           |
    False_          |
    Handle          |
    With            |
    Impl            |
    Num             |
    Question        |
    EOF             |
    Unknown
  deriving (Eq, Ord, Show, Read, Data, Typeable)

type Token = (AlexPosn, Tok, String)

mkL :: Tok -> AlexInput -> Int -> Alex Token
mkL tok (p,_,_,str) len = return (p, tok, (take len str))

lexError s = do
  (p,c,_,input) <- alexGetInput
  alexError (showPosn p ++ ": " ++ s ++ 
       (if (not (null input))
         then " before " ++ show (head input)
         else " at end of file"))

scanner str = runAlex str $ do
  let loop i = do tok@(p, t, str) <- alexMonadScan
                  if t == EOF
                  then return []
                  else do rest <- loop $! (i+1)
                          return $ tok : rest
  loop 0

alexEOF = return (AlexPn 0 0 0, EOF, "")

showPosn (AlexPn _ line col) = show line ++ ':': show col

tokenize str = case scanner str of
   Left err -> error err
   Right tokens -> tokens
}