{
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}

module Cone.Parser.Lexer (tokenize, Token(..), Tok(..), AlexPosn(..)) where
import Data.Data
import Data.Char (chr)
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
  <0> ($white # [\n])+				;
  <0> \\\n                    ;
  <0> "//"[^\n]*              ;
  <0> "/*"                                  { nestedComments }
  <0> [\; \n]+                              { mkL Semi }
  <0> module                                { mkL Module }
  <0> import                                { mkL Import }
  <0> fun                                   { mkL Func }
  <0> fn                                    { mkL Fn }
  <0> as                                    { mkL As }
  <0> var                                   { mkL Var }
  <0> val                                   { mkL Val }
  <0> \(                                    { mkL LParen }
  <0> \)                                    { mkL RParen }
  <0> \{                                    { mkL LBrace }
  <0> \}                                    { mkL RBrace }
  <0> \[                                    { mkL LBracket }
  <0> \]                                    { mkL RBracket }
  <0> \:                                    { mkL Colon }
  <0> \,$white*                             { mkL Comma }
  <0> \<                                    { mkL Less }
  <0> \>                                    { mkL Greater }
  <0> "<="                                  { mkL Le }
  <0> ">="                                  { mkL Ge }
  <0> \!                                    { mkL Not }
  <0> "=="                                  { mkL Eq }
  <0> "!="                                  { mkL Ne }
  <0> "&&"                                  { mkL And }
  <0> "||"                                  { mkL Or }
  <0> \|                                    { mkL Pipe }
  <0> "="$white*                            { mkL Assign }
  <0> "+="                                  { mkL AddAssign }
  <0> "-="                                  { mkL SubAssign }
  <0> "*="                                  { mkL MulAssign }
  <0> "/="                                  { mkL DivAssign }
  <0> "%="                                  { mkL ModAssign }
  <0> "+"                                   { mkL Add }
  <0> "-"                                   { mkL Sub }
  <0> "/"                                   { mkL Div }
  <0> "%"                                   { mkL Mod }
  <0> "#"                                   { mkL Sharp }
  <0> \\                                    { mkL Backslash }
  <0> "->"                                  { mkL Arrow }
  <0> \*                                    { mkL Star }
  <0> \?                                    { mkL Question }
  <0> \@                                    { mkL At }
  <0> \.                                    { mkL Dot }
  <0> "i8"                                  { mkL I8 }
  <0> "i16"                                 { mkL I16 }
  <0> "i32"                                 { mkL I32 }
  <0> "i64"                                 { mkL I64 }
  <0> "u8"                                  { mkL U8 }
  <0> "u16"                                 { mkL U16 }
  <0> "u32"                                 { mkL U32 }
  <0> "u64"                                 { mkL U64 }
  <0> "f16"                                 { mkL F16 }
  <0> "f32"                                 { mkL F32 }
  <0> "f64"                                 { mkL F64 }
  <0> "bf16"                                { mkL BF16 }
  <0> "bool"                                { mkL Pred }
  <0> "str"                                 { mkL Str }
  <0> "char"                                { mkL Char }
  <0> "type"                                { mkL Type }
  <0> "effect"                              { mkL Effect }
  <0> "case"                                { mkL Case }
  <0> "of"                                  { mkL Of }
  <0> "if"                                  { mkL If }
  <0> "else"                                { mkL Else }
  <0> "while"                               { mkL While }
  <0> "num"                                 { mkL Num }
  <0> "unit"                                { mkL Unit }
  <0> "true"                                { mkL True_ }
  <0> "false"                               { mkL False_ }
  <0> "handle"                              { mkL Handle }
  <0> "with"                                { mkL With }
  <0> "impl"                                { mkL Impl }
  <0> "alias"                               { mkL Alias }
  <0> "diff"                                { mkL Diff }
  <0> "wrt"                                 { mkL WRT }
  <0> "auto"                                { mkL Auto }
  <0> "interface"                           { mkL Interface }
  <0> @decimal 
        | 0[oO] @octal
        | 0[xX] @hexadecimal		            { mkL LInt }
  <0> @decimal \. @decimal @exponent?
        | @decimal @exponent	            	{ mkL LFloat }
      \' ($graphic # [\'\\] | " " | @escape) \'
          	                                { mkL LChar }
  <0> \"\"\"                                { multilineString }
  <0> \" @string* \"	                    	{ mkL LStr }
  <0> [$alpha \_] [$alpha $digit \_]*       { mkL Ident }

{

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
    Dot             |
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
    Alias           |
    Diff            |
    WRT             |
    Auto            |
    Num             |
    Question        |
    Interface       |
    EOF             |
    Unknown
  deriving (Eq, Ord, Show, Read, Data, Typeable)

type Token = (AlexPosn, Tok, String)

mkL :: Tok -> AlexInput -> Int -> Alex Token
mkL tok (p,_,_,str) len = return (p, tok, (take len str))

nestedComments :: AlexInput -> Int -> Alex Token
nestedComments (p,_,_,str) len = do 
  input <- alexGetInput
  go 1 input
  where go 0 input = do alexSetInput input; alexMonadScan
        go n input = do
          let slashN = fromIntegral (ord '/')
              starN  = fromIntegral (ord '*')
          case alexGetByte input of
            Nothing  -> err input
            Just (c,input) -> do
              case chr (fromIntegral c) of
                '*' -> do
                  let temp = input
                  case alexGetByte input of
                    Nothing  -> err input
                    Just (c,input) | c == slashN -> go (n-1) input
                    Just (c,input) | c == starN -> go n temp
                    Just (c,input)   -> go n input
                '/' -> do
                  case alexGetByte input of
                    Nothing  -> err input
                    Just (c,input) | c == starN -> go (n+1) input
                    Just (c,input)   -> go n input
                c -> go n input
        err input = do alexSetInput input; lexError "error in nested comments"  

multilineString :: AlexInput -> Int -> Alex Token
multilineString (p,_,_,str) len = do 
  input <- alexGetInput
  rlen <- go 1 input 0
  return (p, LStr, "R\"cone(" ++ (drop 3 (take (len+rlen-3) str)) ++ ")cone\"")
  where go 0 input len = do alexSetInput input; return len
        go n input len = do
          let strQN = fromIntegral (ord '"')
          case alexGetByte input of
            Nothing  -> err input
            Just (c,input) -> do
              case chr (fromIntegral c) of
                '"' -> do
                  case alexGetByte input of
                    Nothing -> err input
                    Just (c,input) | c == strQN -> do
                      case alexGetByte input of
                        Nothing -> err input
                        Just (c,input) | c == strQN -> go (n-1) input (len+3)
                        Just (c,input) -> go n input (len+3)
                    Just (c,input) -> go n input (len+2)
                c -> go n input (len+1)
        err input = do alexSetInput input; lexError "error in multiline string"

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