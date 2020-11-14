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
  open CsisatDimacsParse
}

let word = ['a'-'z' 'A'-'Z']+
let digit = ['0'-'9']
let num = '-'? ['1'-'9'] digit*
let white = [' ' '\t' '\n']
let zero = '0'

rule token = parse
  | 'p' white+ (word as form)           { P form }     (* skip header *)
  | num                                 { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | zero                                { ZERO }
  | white+                              { token lexbuf }     (* skip blanks *)
  | 'c' [^'\n']* '\n'                   { token lexbuf }     (* skip comments *)
  | eof                                 { EOF }
