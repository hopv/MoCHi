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
%token LPAREN RPAREN
%token SEMICOLON COMMA
%token PLUS MINUS TIMES
%token SLASH
%token AND OR NOT
%token IMPLIES IFF
%token EQ LEQ LT GEQ GT
%token TRUE FALSE
%token EOF
%left IMPLIES IFF
%left AND OR
%nonassoc NOT
%left PLUS MINUS
%left TIMES
%nonassoc UMINUS
%{
  module Ast = CsisatAst
%}
%start main             /* the entry point */
%type <CsisatAst.predicate list> main
%%

main:
    formula                 { [$1] }
  | formula SEMICOLON main  { $1 :: $3 }
  | EOF                     { [] }
;

term_lst:
    term COMMA term_lst     { $1 :: $3 }
  | term                    { [$1] }
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
    LPAREN term_lst RPAREN  { Some $2 }
  | /*empty*/               { None }
;

term:
  | LPAREN term RPAREN              { $2 }
  | term PLUS term                  { Ast.Sum [$1; $3] }
  | term MINUS term                 { Ast.Sum [$1; Ast.Coeff (-1., $3)] }
  | term TIMES term                 { match ($1, $3) with
                                      | (Ast.Constant c1, Ast.Constant c2) -> Ast.Constant (c1 *. c2)
                                      | (Ast.Constant c, other)
                                      | (other, Ast.Constant c) -> Ast.Coeff (c, other)
                                      | _ -> raise Parsing.Parse_error
                                    }
  | number                          { Ast.Constant $1 }
  | MINUS term  %prec UMINUS        { Ast.Coeff (-1., $2) }
  | IDENT opt_apply                 { match $2 with None -> Ast.Variable $1 | Some lst -> Ast.Application ($1, lst)}
;

formula:
    LPAREN formula RPAREN           { $2 }
  | formula IMPLIES formula         { Ast.Or [Ast.Not $1; $3] }
  | formula IFF formula             { Ast.Or [Ast.And [$1; $3]; Ast.And [Ast.Not $1; Ast.Not $3]] }
  | formula AND formula             { Ast.And [$1; $3] }
  | formula OR  formula             { Ast.Or  [$1; $3] }
  | NOT formula                     { Ast.Not $2 }
  | term EQ term                    { Ast.Eq ($1, $3) }
  | term LEQ term                   { Ast.Leq ($1, $3) }
  | term LT term                    { Ast.Lt ($1, $3) }
  | term GEQ term                   { Ast.Leq ($3, $1) }
  | term GT term                    { Ast.Lt ($3, $1) }
  | TRUE                            { Ast.True }
  | FALSE                           { Ast.False }
/*| IDENT                           { Ast.Atom (*TODO convert to index*)}*/
;
