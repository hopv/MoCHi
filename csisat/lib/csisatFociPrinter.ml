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

(** *)

open   CsisatAst
(**/**)
module Utils   = CsisatUtils
(**/**)

(*****************************************************************************)
(*************************        PRINTER         ****************************)
(*****************************************************************************)

let rec print_foci_expression exp = match exp with
    Constant cst -> (Utils.my_string_of_float cst) ^ " "
  | Variable var -> var ^ " "
  | Application (f, args) ->
    begin
      let args_string = List.fold_left (fun acc x -> acc ^ (print_foci_expression x) ) "" args
      in f ^ " [ " ^ args_string ^ "] "
    end
  | Sum elements ->
    begin
      let el_string = List.fold_left (fun acc x -> acc ^ (print_foci_expression x) ) "" elements
      in "+ [ " ^ el_string ^ "] "
    end
  | Coeff (cst, expr) ->
    begin
      "* " ^ (Utils.my_string_of_float cst) ^ " " ^ (print_foci_expression expr)
    end

let rec print_foci_predicate pred = match pred with
    True  -> "true "
  | False -> "false "
  | And pred_lst ->
    let preds_string = List.fold_left (fun acc x -> acc ^ (print_foci_predicate x) ) "" pred_lst
    in "& [ " ^ preds_string ^ "] "
  | Or pred_lst ->
    let preds_string = List.fold_left (fun acc x -> acc ^ (print_foci_predicate x) ) "" pred_lst
    in "| [ " ^ preds_string ^ "] "
  | Not pred1 -> "~ " ^ (print_foci_predicate pred1)
  | Eq (exp1, exp2) -> "= " ^ (print_foci_expression exp1) ^ (print_foci_expression exp2)
  | Lt (exp1, exp2) -> "~<= " ^ (print_foci_expression exp2) ^ (print_foci_expression exp1)
  | Leq (exp1, exp2) -> "<= " ^ (print_foci_expression exp1) ^ (print_foci_expression exp2)
  | Atom (External str) -> str^" "
  | Atom (Internal i) -> "atom"^(string_of_int i)^" "

let rec print_foci pred_lst =
  let buffer = Buffer.create 0 in
    List.iter
      (fun x ->
        Buffer.add_string buffer ((print_foci_predicate x) ^ "; " )
      ) pred_lst;
    (*remove the trailling "; "*)
    Buffer.sub buffer 0 ((Buffer.length buffer) -3)

