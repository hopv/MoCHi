(*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *
 *  Copyright (C) 2007-2008  Dirk Beyer and Damien Zufferey.
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CSIsat web page:
 *    http://www.cs.sfu.ca/~dbeyer/CSIsat/
 *)
{
  open CsisatInfixParse
}

let white = [' ' '\t' '\n']

let digit = ['0'-'9']
let num = '-'? digit+
let real = '-'? digit+ '.' digit*

let word = ['a'-'z' 'A'-'Z' '_' '@' ':']+
let ident = word (word | digit)*
let ident2 = ''' [^'\n' ''']+ '''

rule token = parse
  | "="             { EQ }
  | "<="            { LEQ }
  | '<'             { LT }
  | ">="            { GEQ }
  | '>'             { GT }
  | "->"            { IMPLIES }
  | "<->"           { IFF }
  | "not"           { NOT }
  | "!"             { NOT }
  | '&'             { AND }
  | '|'             { OR }
  | '+'             { PLUS }
  | '*'             { TIMES }
  | '/'             { SLASH }
  | real            { FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
  | num             { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | '-'             { MINUS }
  | ';'             { SEMICOLON }
  | ','             { COMMA }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | "true"          { TRUE }
  | "false"         { FALSE }
  | ident           { IDENT (Lexing.lexeme lexbuf) }
  | ident2          { IDENT (Lexing.lexeme lexbuf) }
  | white+          { token lexbuf } (* skip blanks *)
  | eof             { EOF }
