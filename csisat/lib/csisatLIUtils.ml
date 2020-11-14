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

(** Methods related to LInear arithmetic. *)

open   CsisatAst
open   CsisatAstUtil
(**/**)
module Message = CsisatMessage
module Utils   = CsisatUtils
module OrdSet  = CsisatOrdSet
(**/**)

exception LP_SOLVER_FAILURE

(** Solver abstraction.
 * Only about solving, the problem specification uses GLPK as usual.
 *)
type li_solver = {
    solver_error: float;
    has_basis   : bool; 
    solve       : Camlglpk.t -> bool; 
    obj_val     : Camlglpk.t -> float;
    row_stat    : Camlglpk.t -> int -> int;
    is_row_basic: Camlglpk.t -> int -> bool;
    col_stat    : Camlglpk.t -> int -> int;
    is_col_basic: Camlglpk.t -> int -> bool;
    row_primal  : Camlglpk.t -> int -> float;
    rows_primal : Camlglpk.t -> int -> float array -> unit;
    row_dual    : Camlglpk.t -> int -> float;
    rows_dual   : Camlglpk.t -> int -> float array -> unit;
    col_primal  : Camlglpk.t -> int -> float;
    cols_primal : Camlglpk.t -> int -> float array -> unit;
    col_dual    : Camlglpk.t -> int -> float;
    cols_dual   : Camlglpk.t -> int -> float array -> unit
}

let simplex: li_solver = {
    solver_error= 1.e-10;
    has_basis   = true; 
    solve       = (fun x -> Camlglpk.simplex x true);
    obj_val     = Camlglpk.get_obj_val;
    row_stat    = Camlglpk.get_row_stat;
    is_row_basic= Camlglpk.is_row_basic;
    col_stat    = Camlglpk.get_col_stat;
    is_col_basic= Camlglpk.is_col_basic;
    row_primal  = Camlglpk.get_row_primal;
    rows_primal = Camlglpk.get_rows_primal;
    row_dual    = Camlglpk.get_row_dual;
    rows_dual   = Camlglpk.get_rows_dual;
    col_primal  = Camlglpk.get_col_primal;
    cols_primal = Camlglpk.get_cols_primal;
    col_dual    = Camlglpk.get_col_dual;
    cols_dual   = Camlglpk.get_cols_dual
}

let simplex_wo_presolve: li_solver = {
    solver_error= 1.e-10;
    has_basis   = true; 
    solve       = (fun x -> Camlglpk.simplex x false);
    obj_val     = Camlglpk.get_obj_val;
    row_stat    = Camlglpk.get_row_stat;
    is_row_basic= Camlglpk.is_row_basic;
    col_stat    = Camlglpk.get_col_stat;
    is_col_basic= Camlglpk.is_col_basic;
    row_primal  = Camlglpk.get_row_primal;
    rows_primal = Camlglpk.get_rows_primal;
    row_dual    = Camlglpk.get_row_dual;
    rows_dual   = Camlglpk.get_rows_dual;
    col_primal  = Camlglpk.get_col_primal;
    cols_primal = Camlglpk.get_cols_primal;
    col_dual    = Camlglpk.get_col_dual;
    cols_dual   = Camlglpk.get_cols_dual
}

let simplex_exact: li_solver = {
    solver_error= 1.0e-15;
    has_basis   = true; 
    solve       = Camlglpk.simplex_exact;
    obj_val     = Camlglpk.get_obj_val;
    row_stat    = Camlglpk.get_row_stat;
    is_row_basic= Camlglpk.is_row_basic;
    col_stat    = Camlglpk.get_col_stat;
    is_col_basic= Camlglpk.is_col_basic;
    row_primal  = Camlglpk.get_row_primal;
    rows_primal = Camlglpk.get_rows_primal;
    row_dual    = Camlglpk.get_row_dual;
    rows_dual   = Camlglpk.get_rows_dual;
    col_primal  = Camlglpk.get_col_primal;
    cols_primal = Camlglpk.get_cols_primal;
    col_dual    = Camlglpk.get_col_dual;
    cols_dual   = Camlglpk.get_cols_dual
}

let interior: li_solver = {
    solver_error= 1.e-10;
    has_basis   = false; 
    solve       = Camlglpk.interior;
    obj_val     = Camlglpk.ipt_obj_val;
    row_stat    = (fun _ _ -> failwith "row_stat not implemented for interior point solver");
    is_col_basic= (fun _ _ -> failwith "is_col_basic not implemented for interior point solver");
    col_stat    = (fun _ _ -> failwith "col_stat not implemented for interior point solver");
    is_row_basic= (fun _ _ -> failwith "is_row_basic not implemented for interior point solver");
    row_primal  = Camlglpk.ipt_row_primal;
    rows_primal = Camlglpk.ipt_rows_primal;
    row_dual    = Camlglpk.ipt_row_dual;
    rows_dual   = Camlglpk.ipt_rows_dual;
    col_primal  = Camlglpk.ipt_col_primal;
    cols_primal = Camlglpk.ipt_cols_primal;
    col_dual    = Camlglpk.ipt_col_dual;
    cols_dual   = Camlglpk.ipt_cols_dual
}

let solver = ref simplex_wo_presolve

let set_solver str = match str with
  | "simplex" -> solver := simplex
  | "simplex_wo_presolve" -> solver := simplex_wo_presolve
  | "interior" -> solver := interior
  | "exact" -> solver := simplex_exact
  | s -> failwith (s^" is not a known LI solver")

(** Not a=b  -> Or( a < b, b < a) *)
let rec split_neq pred = match pred with
  | And lst -> And (List.map split_neq lst)
  | Not (Eq(e1, e2)) -> Or [Lt(e1,e2); Lt(e2,e1)]
  | Leq _ | Lt _ | Eq _ as e -> e
  | Or _ -> failwith "split_neq: does not support 'Or'"
  | Atom _ -> failwith "split_neq: does not support 'Atom'"
  | True -> Leq(Constant 0.0, Constant 1.0)
  | False -> Leq(Constant 1.0, Constant 0.0)
  | Not _ -> failwith "split_neq: 'Not' supported onyl with 'Eq'"
  
(** Extracts the constant from e1 and e2.
 *  @return (nonCst_e1 - non_Cst_e2, Cst_e2 - Cst_e1)
 *)
let extract_constant e1 e2 =
  let rec split (accCst,accRest) expr = match expr with
    | Constant cst -> (accCst +. cst, accRest)
    | Variable _ as v -> (accCst, v::accRest)
    | Application _ as appl ->  (accCst, appl::accRest)
    | Sum lst -> List.fold_left (split) (accCst,accRest) lst
    | Coeff _ as co -> (accCst, co::accRest)
  in
  let rec negate expr = match expr with
    | Constant cst -> Constant (-. cst)
    | Variable _ as v -> Coeff(-1.0, v)
    | Application _ as appl -> Coeff(-1.0, appl)
    | Sum lst -> Sum (List.map negate lst)
    | Coeff (c, e) -> Coeff(-. c, e)
  in
    let (c1,e1) = split (0.0, []) e1 in
    let (c2,e2) = split (0.0, []) e2 in
      (simplify_expr (Sum(e1 @ (List.map negate e2))), Constant ( c2 -. c1))


(** Transforms the constraint into LI normal form:
 *  a_1 * x_1 + a_2 * x_2 + ... </<=/= constant
 *)
let rec to_normal_li_constraints pred = match pred with 
  | Lt (e1, e2)  -> let (s,c) = extract_constant e1 e2 in Lt(s, c)
  | Leq (e1, e2) -> let (s,c) = extract_constant e1 e2 in Leq(s, c)
  | Eq (e1, e2)  -> let (s,c) = extract_constant e1 e2 in Eq(s, c)
  (*| And lst -> And (List.map to_normal_li_constraints lst)*)
  | And _ -> failwith "to_normal_li_constraints: does not support 'And'"
  | Or _ -> failwith "to_normal_li_constraints: does not support 'Or'"
  | Atom _ -> failwith "to_normal_li_constraints: does not support 'Atom'"
  | True -> failwith "to_normal_li_constraints: does not support 'True'"
  | False -> failwith "to_normal_li_constraints: does not support 'False'"
  | Not _ -> failwith "to_normal_li_constraints: does not support 'Not'"

(** Performs some coefficient 'rounding'.
 *  WARNING: this method is NOT exact,
 *           the arbitrary precision solver (coming ...)
 *           would solve this problem.
 *)
let rounding_bound = 1000
let rounding_precision = 1.e-5
let round_coeff li_cstr =
  (* return a denom that seems to works well*)
  let best_denom coeff =
    let is_close_to_int n =
      if n = 0. then true
      else
        begin
          let frac = abs_float((Utils.round n) -. n) in
            Message.print Message.Debug (lazy("LIUtils, best_denom: rest is " ^ (string_of_float frac)));
            (frac /. n) <= rounding_precision
        end
    in
    let frac = (abs_float coeff) -. (floor (abs_float coeff)) in
    let rec test_denom i =
      if i < rounding_bound then
        begin
          if is_close_to_int (frac *. (float_of_int i)) then i
          else test_denom (i + 1)
        end
      else 1 (*did no t found anything*)
    in
      let res = test_denom 1 in
        Message.print Message.Debug (lazy("LIUtils, best_denom: denom of " ^ (string_of_float coeff) ^ " is " ^ (string_of_int res)));
        res
  in
  (* get all the coeffs/csts that appears in the predicate *)
  (*TODO move this part in AstUtil*)
  let fetch_coeffs pred =
    let rec process_expr expr = match expr with
      | Constant c -> [c]
      | Variable _ -> []
      | Application (_, lst) -> []
      | Sum lst -> [] (* elements of sum are fetched by "get_expr_deep" *)
      | Coeff (c,e) -> [c]
    in
    let exprs = get_expr_deep pred in
      OrdSet.list_to_ordSet (List.fold_left (fun acc x -> (process_expr x) @ acc) [] exprs)
      
  in
  (* merge the prime decomposition to find the lcm *)
  let result = Array.make (rounding_bound + 1) 0 in
  let rec merge_prime_decomp value counter lst = match lst with
    | x::xs ->
      begin
        if x = value then
          merge_prime_decomp value (counter + 1) xs
        else
          begin
            result.(value) <- max result.(value) counter;
            merge_prime_decomp x 1 xs
          end
      end
    | [] -> result.(value) <- max result.(value) counter
  in
  (* scale and round the predicate float values *)
  let scale_and_round lcm pred =
    let rec process_expr expr = match expr with
      | Constant c -> Constant (Utils.round (lcm *. c))
      | Variable _ as v -> Coeff (lcm, v)
      | Application (f, lst) -> Application (f, List.map process_expr lst)
      | Sum lst -> Sum (List.map process_expr lst)
      | Coeff (c,e) -> Coeff(Utils.round (lcm *. c), e)
    in
    let rec process_pred pred = match pred with
      | False -> False
      | True -> True
      | And lst -> And (List.map process_pred lst)
      | Or lst -> Or (List.map process_pred lst)
      | Not p -> Not (process_pred p)
      | Eq (e1,e2) -> order_eq (Eq(process_expr e1, process_expr e2))
      | Lt (e1,e2) -> Lt (process_expr e1, process_expr e2)
      | Leq (e1,e2) -> Leq (process_expr e1, process_expr e2)
      | Atom _ as a -> a
    in
      process_pred pred
  in
  (*begins here*)
  let denoms = List.map best_denom (fetch_coeffs li_cstr) in
  let decomp = List.map Utils.factorise denoms in
    List.iter (fun lst -> merge_prime_decomp (List.hd lst) 1 (List.tl lst)) decomp;
    (*builds the final number*)
    let lcm = ref 1 in
      Array.iteri (fun i n -> lcm := !lcm * (Utils.power i n)) result;
      Message.print Message.Debug (lazy("LIUtils, round_coefffor: lcm is " ^ (string_of_int !lcm)));
      scale_and_round (float_of_int !lcm) li_cstr

  


(** transform a conjunction of formulae into a matrix 'A' and a vector 'a'
 *  such that A*vars </<=/= a is equivalent to the input formulae
 *)
let conj_to_matrix pred_lst vars =
  Message.print Message.Debug (lazy("conj_to_matrix for: " ^ (Utils.string_list_cat ", " (List.map print pred_lst))));
  Message.print Message.Debug (lazy("vars are: " ^ (Utils.string_list_cat ", " (List.map print_expr vars))));
  let length =  List.length pred_lst in
  let matrixA = Array.make_matrix length (List.length vars) 0.0 in
  let vectorB = Array.make length 0.0 in
  let (_, var_to_index) = List.fold_left (fun (i,xs) x -> (i+1,(x,i)::xs)) (0,[]) vars in
  let rec fill_coeff row lst = match lst with
    | x::xs ->
      begin
        let _ = match x with
          | Variable _ as v ->
            let index = List.assoc v var_to_index in
              matrixA.(row).(index) <- 1.0
          | Application _ as a -> 
            (
            try
            let index = List.assoc a var_to_index in
              matrixA.(row).(index) <- 1.0
            with Not_found -> failwith ((print_expr a)^" not in assoc")
            )
          | Coeff (co, expr) ->
            let index = List.assoc expr var_to_index in
              matrixA.(row).(index) <- co
          | Constant 0.0 -> () (*when empty...*)
          | e -> failwith ("fill_coeff: 'Sum' and 'Constant' not supported: "^(print_expr e))
        in
          fill_coeff row xs
      end
    | [] -> ()
  in
  let rec fill_constraints row lst = match lst with
    | x::xs ->
      begin
        let cstr = to_normal_li_constraints x in
        let _ = match cstr with
          | Leq (Sum lst, Constant c) ->
            fill_coeff row lst;
            vectorB.(row) <- c
          | Leq (e , Constant c) ->
            fill_coeff row [e];
            vectorB.(row) <- c
          | Lt (Sum lst, Constant c) -> 
            fill_coeff row lst;
            vectorB.(row) <- c
          | Lt (e , Constant c) -> 
            fill_coeff row [e];
            vectorB.(row) <- c
          | Eq (Sum lst, Constant c) -> 
            fill_coeff row lst;
            vectorB.(row) <- c
          | Eq (e, Constant c) -> 
            fill_coeff row [e];
            vectorB.(row) <- c
          | p -> failwith ("fill_constraints: error -> " ^ (print p))
        in
          fill_constraints (row + 1) xs
      end
    | [] -> ()
  in
    fill_constraints 0 pred_lst;
    (matrixA,vectorB)


(** collect the terms that are "variable" for clp-algo (i.e. var + appl) *)
let collect_li_vars pred = 
  let rec process expr = match expr with
    | Constant _ -> []
    | Variable _ as v -> [v]
    | Application _ as a -> [a]
    | Sum lst -> List.fold_left (fun acc x -> (process x) @ acc ) [] lst
    | Coeff (co, expr) -> process expr
  in
  let rec process_pred pred = match pred with
    | And lst | Or lst -> List.fold_left (fun acc x -> (process_pred x) @ acc ) [] lst
    | Not pred -> process_pred pred
    | Eq(e1, e2) | Lt(e1, e2) | Leq(e1, e2) -> (process e1) @ (process e2)
    | _ -> []
  in
    OrdSet.list_to_ordSet (process_pred pred)

