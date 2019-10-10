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

(*TODO
 * keep Lt xor Leq
 * a <= b  <-> b ~< a
 *)

(** The AST (very simple).
 * It is inspired from the FOCI AST.
 * This makes the tool substitution easier.
 *)

type theory =
  | EUF (** equality with uninterpreted function symbols (also referred as UIF)*)
  | LA  (** linear arithmetic (also referred as LI)*)
  | EUF_LA

(** variable or uninterpreted fct*)
type symbol = string

type expression =
  | Constant of float
  | Variable of symbol
  | Application of symbol * expression list
  | Sum of expression list
  | Coeff of float * expression

(** External atoms are given in the input, Internal ones are for equisatisfiable transformation *)
type atom_type =
  | External of string
  | Internal of int

type predicate =
  | True
  | False
  | And of predicate list
  | Or of predicate list
  | Not of predicate
  | Eq of expression * expression
  | Lt of expression * expression
  | Leq of expression * expression
  | Atom of atom_type

(*is it a propositional AST ?*)
let rec is_sat_ast p = match p with
  | True | False | Atom _ -> true
  | Not p -> is_sat_ast p
  | Eq _ | Lt _ | Leq _ -> false
  | And lst | Or lst -> List.for_all is_sat_ast lst

(*only Eqalities, nothing else*)
let is_expr_EQ expr = match expr with
  | Variable _ -> true
  | Constant _ | Application _ | Sum _ | Coeff _ -> false
let is_pred_EQ pred = match pred with
  | Not (Eq _) | Eq _  -> true (*assume the pred to be in normal form*)
  | True | False | And _ | Or _ | Atom _  | Lt _ | Leq _ | Not _ -> false
let rec is_theory_EQ formula = match formula with
  | And lst | Or lst -> List.for_all is_theory_EQ lst
  | Not (Eq (e1,e2)) | Eq (e1,e2)  -> (is_expr_EQ e1) && (is_expr_EQ e2)
  | _ -> false

(** is the root symbol in LI*)
let is_expr_LI expr = match expr with
  | Constant _ | Variable _ | Sum _ | Coeff _ -> true
  | Application _ -> false
(** is the root symbol in LI only*)
let is_expr_LI_only expr = match expr with
  | Constant _ | Variable _ | Application _ -> false
  | Sum _ | Coeff _ -> true
let is_pred_LI pred = match pred with
  | True | False | And _ | Or _ | Atom _ | Not (Eq _) -> false
  | Not _ | Eq _ | Lt _ | Leq _ -> true (*assume the pred to be in normal form*)
(** is one symbol in LI only (deep)*)
let rec has_LI_only_term expr = match expr with
  | Variable _ -> false
  | Constant _ |Sum _ | Coeff _ -> true
  | Application (_,lst) -> List.exists has_LI_only_term lst
(** is one symbol in LI only (deep)*)
let rec has_LI_only pred = match pred with
  | True | False | Atom _ -> false
  | Lt _ | Leq _  -> true
  | And lst | Or lst -> List.exists has_LI_only lst
  | Eq (e1, e2) -> (has_LI_only_term e1) || (has_LI_only_term e2)
  | Not e -> has_LI_only e

(** is the root symbol in UIF*)
let is_expr_UIF expr = match expr with
  | Variable _ | Application _ -> true
  | Sum _ | Coeff _ | Constant _ -> false
(** is the root symbol in UIF only*)
let is_expr_UIF_only expr = match expr with
  | Application _ -> true
  | Constant _ | Variable _ | Sum _ | Coeff _ -> false
(** is the root symbol in UIF only*)
let is_pred_UIF pred = match pred with
  | Not (Eq _) | Eq _  -> true
  | True | False | And _ | Or _ | Atom _ | Lt _ | Leq _ | Not _-> false
(** is one symbol in UIF only (deep)*)
let rec has_UIF_only_term expr = match expr with
  | Constant _ | Variable _ -> false
  | Application _ -> true
  | Sum lst -> List.exists has_UIF_only_term lst
  | Coeff (_,e) -> has_UIF_only_term e
(** is one symbol in UIF only (deep)*)
let rec has_UIF_only pred = match pred with
  | Not (Eq _)  -> true
  | True | False | Atom _ -> false
  | And lst | Or lst -> List.exists has_UIF_only lst
  | Eq (e1, e2) | Lt (e1,e2) | Leq (e1,e2)  -> (has_UIF_only_term e1) || (has_UIF_only_term e2)
  | Not e -> has_UIF_only e

let theory_of formula =
   match (has_LI_only formula, has_UIF_only formula) with
   | (true,true) -> EUF_LA
   | (false,true) -> EUF
   | (true,false) -> LA
   | (false,false) -> EUF

(* exceptions common the many part*)
exception SAT
exception SAT_FORMULA of predicate
