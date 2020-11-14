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

(** configuration variables *)

(** Syntax for I/O*)
type syntax_t =
  | SyntaxFoci
  | SyntaxInfix
  | SyntaxDimacs (* to use with '-sat' *)
  | SyntaxUnk

(**check the interpolant*)
let check = ref false
(** check the satisfiability, do not compute interpolant*)
let sat_only = ref false
(** round coefficient of the interpolant to get integers (!!limited precision)*)
let round = ref false
(** x < y  ~>  x+1 <= y *)
let integer_heuristics = ref false
(** Syntax: foci or infix *)
let syntax = ref SyntaxUnk
(** disable runtime asserts *)
let assert_disable = ref false
let is_off_assert () = !assert_disable
