/*
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
 */
%token <int> NUM
%token <string> P
%token ZERO
%token EOF
%token EOL
%{
  module Ast = CsisatAst
%}
%start main             /* the entry point */
%type <string * int * int * (CsisatAst.predicate list list)> main
%%
main:
    P NUM NUM clauses       { ($1, $2, $3, $4) }
;
clauses:
    EOF                     { [] }
  | clause clauses          { $1 :: $2 }
;
clause:
    ZERO                    { [] }
  | NUM clause              { (if $1 < 0 then
                                Ast.Not (Ast.Atom (Ast.External (string_of_int (-$1))))
                               else
                                Ast.Atom (Ast.External (string_of_int $1))
                              ):: $2
                            }
;
