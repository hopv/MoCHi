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
%token <float> FLOAT
%token <string> IDENT
%token LBRACK
%token RBRACK
%token LPAREN
%token RPAREN
%{
  module Ast = CsisatAst
  let ref_table = Hashtbl.create 10
%}

%token SEMICOLON
%token PLUS
%token TIMES
%token IMPLIES
%token SLASH
%token AND
%token OR
%token EQ
%token NOT
%token LEQ
%token LT
%token TRUE
%token FALSE
%token EOF
%token SHARP
%token AT

%start main             /* the entry point */
%type <CsisatAst.predicate list> main
%%

main:
    formula                 { [$1] }
  | formula SEMICOLON main  { $1 :: $3 }
  | EOF                     { [] }
;

term_lst:
    term term_lst           { $1 :: $2 }
  | /*empty*/               { [] }
;

opt_ratio:
    SLASH NUM               { $2 }
  | /*empty*/               { 1 }
;

number:
    FLOAT                   { $1 }
  | NUM opt_ratio           { (float_of_int $1) /. (float_of_int $2) }
;

opt_apply:
    LBRACK term_lst RBRACK  { Some $2 }
  | /*empty*/               { None }
;

term:
  | LPAREN term RPAREN              { $2 }
  | PLUS LBRACK term_lst RBRACK     { Ast.Sum $3 }
  | TIMES number term               { Ast.Coeff ($2, $3) }
  | IDENT opt_apply                 { match $2 with None -> Ast.Variable $1 | Some lst -> Ast.Application ($1, lst)}
  | SHARP NUM term                  { Hashtbl.add ref_table $2 $3; $3}
  | AT NUM                          { Hashtbl.find ref_table $2 }
  | number                          { Ast.Constant $1 }
;

formula:
    LPAREN formula RPAREN           { $2 }
  | EQ term term                    { Ast.Eq ($2, $3) }
  | LEQ term term                   { Ast.Leq ($2, $3) }
  | LT term term                    { Ast.Lt ($2, $3) }
  | AND LBRACK formula_lst RBRACK   { Ast.And $3 }
  | OR  LBRACK formula_lst RBRACK   { Ast.Or $3 }
  | IMPLIES formula formula         { Ast.Or [Ast.Not $2; $3]}
  | NOT formula                     { Ast.Not $2}
  | TRUE                            { Ast.True }
  | FALSE                           { Ast.False }
  | IDENT                           { Ast.Atom (Ast.External $1)}
;

formula_lst:
    formula formula_lst             { $1::$2 }
  | /*empty*/                       { [] }
;
