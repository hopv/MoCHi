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

(** Satisfiability for LA. (LI stands for LInear arithmetic)*)

open   CsisatAst
open   CsisatAstUtil
open   CsisatLIUtils
(**/**)
module Global  = CsisatGlobal
module Message = CsisatMessage
module Utils   = CsisatUtils
module Matrix  = CsisatMatrix
module ClpLI   = CsisatClpLI
(**/**)

let is_li_sat pred =
  Message.print Message.Debug (lazy("testing LA sat of "^(print pred)));
  let pred_lst = match pred with
    | Eq _ as eq -> [eq]
    | Lt _ as lt -> [lt]
    | Leq _ as leq -> [leq]
    | And lst -> lst
    | e -> failwith ("SatLI: expected And [...], =, <, <=,  found: " ^ (print e))
  in
  let vars_set = List.fold_left (fun acc x -> ExprSet.add x acc) ExprSet.empty (List.flatten (List.map collect_li_vars pred_lst)) in
  let vars = ExprSet.fold (fun x acc -> x::acc) vars_set [] in
  let nb_vars = List.length vars in
    Message.print Message.Debug (lazy("Variables are: " ^ (Utils.string_list_cat ", " (List.map print_expr vars))));
    if nb_vars <= 0 then
      (*simple case when formula contains only constant terms*)
      let simple = simplify pred in
        match simple with
        | True -> true
        | False -> false
        | e -> failwith ("is_li_sat, simple case first element: match error "^(print e))
    else
      let (matrixA,vectorB) = conj_to_matrix pred_lst vars in
      (*assume lp problem has enough col and row*)
      let rec fill_glpk_problem lp index lst = match lst with
        | (Eq _)::xs ->
          begin
            Camlglpk.set_mat_row lp index nb_vars matrixA.(index);
            Camlglpk.set_row_bnd_fixed lp index vectorB.(index);
            fill_glpk_problem lp (index +1) xs
          end
        | (Leq _)::xs ->
          begin
            Camlglpk.set_mat_row lp index nb_vars matrixA.(index);
            Camlglpk.set_row_bnd_upper lp index vectorB.(index);
            fill_glpk_problem lp (index +1) xs
          end
        | (Lt _)::xs ->
          begin
            Camlglpk.set_mat_row lp index (nb_vars + 1) (Array.append matrixA.(index) (Array.make 1 1.0));
            Camlglpk.set_row_bnd_upper lp index vectorB.(index);
            fill_glpk_problem lp (index +1) xs
          end
        | [] -> ()
        | e::xs -> failwith ("SatLI, fill_glpk_problem: found "^(print e))
      in
        
      let lp = Camlglpk.create () in
        Camlglpk.add_col lp (nb_vars + 1);
        Camlglpk.add_row lp (List.length pred_lst);
        fill_glpk_problem lp 0 pred_lst;
        for i = 0 to nb_vars -1 do
          Camlglpk.set_col_bnd_free lp i;
        done;
        Camlglpk.set_col_bnd_double lp nb_vars 0.0 10.0;(*put an upper bound to avoid unbounded problem*)
        Camlglpk.set_obj_coef lp nb_vars 1.0;
        Camlglpk.set_maximize lp;
        if !solver.solve lp then
          let ans = !solver.obj_val lp in
            Camlglpk.delete lp;
            Message.print Message.Debug (lazy("LI returned "^(string_of_float ans)));
            ans > !solver.solver_error
            (*ans > 0.0*)
        else
          begin
            Camlglpk.delete lp;
            Message.print Message.Debug (lazy "LI UNSAT");
            false
          end

(** Assumes that formula is SAT.
 *  Assumes the vars in eq are inside the formula.
 *
 * TODO incremental version (i.e. add the constraints (solve), add, solve, change, solve)
 *)
let is_eq_implied pred eq =
  (* incremental version ?same result?
  Message.print Message.Debug ("testing LI implied "^(print eq)^" by "^(print pred));
  let pred_lst = match pred with
    | And lst -> lst
    | _ -> failwith "SatLI: expected And [...]"
  in
  let vars_set = List.fold_left (fun acc x -> ExprSet.add x acc) ExprSet.empty (List.flatten (List.map collect_li_vars pred_lst)) in
  let vars = ExprSet.fold (fun x acc -> x::acc) vars_set [] in
  let nb_vars = List.length vars in
    Message.print Message.Debug ("Variables are: " ^ (Utils.string_list_cat ", " (List.map print_expr vars)));
    if nb_vars <= 0 then
        failwith ("is_eq_implied: no variables... ")
    else
      let (e1,e2) = match eq with 
        | Eq (e1,e2) -> (e1,e2)
        | e -> failwith ("satLI, is_eq_implied: expected Eq, found"^(print e))
      in
      let (matrixA,vectorB) = conj_to_matrix (pred_lst @ [Lt (e1,e2);Lt (e2,e1)]) vars in
      (*assume lp problem has enough col and row*)
      let rec fill_glpk_problem lp index lst = match lst with
        | (Eq _)::xs ->
          begin
            Camlglpk.set_mat_row lp index nb_vars matrixA.(index);
            Camlglpk.set_row_bnd_fixed lp index vectorB.(index);
            fill_glpk_problem lp (index +1) xs
          end
        | (Leq _)::xs ->
          begin
            Camlglpk.set_mat_row lp index nb_vars matrixA.(index);
            Camlglpk.set_row_bnd_upper lp index vectorB.(index);
            fill_glpk_problem lp (index +1) xs
          end
        | (Lt _)::xs ->
          begin
            Camlglpk.set_mat_row lp index (nb_vars + 1) (Array.append matrixA.(index) (Array.make 1 1.0));
            Camlglpk.set_row_bnd_upper lp index vectorB.(index);
            fill_glpk_problem lp (index +1) xs
          end
        | [] -> ()
        | e::xs -> failwith ("SatLI, fill_glpk_problem: found "^(print e))
      in
      
      let nb_cstr = List.length pred_lst in
      let lp = Camlglpk.create () in
        Camlglpk.add_col lp (nb_vars + 1);
        Camlglpk.add_row lp (nb_cstr + 1);
        fill_glpk_problem lp 0 pred_lst;
        for i = 0 to nb_vars -1 do
          Camlglpk.set_col_bnd_free lp i;
        done;
        Camlglpk.set_col_bnd_double lp nb_vars 0.0 10.0;(*put an upper bound to avoid unbounded problem*)
        Camlglpk.set_obj_coef lp nb_vars 1.0;
        Camlglpk.set_maximize lp;
        let is_sat () =
          let ans = Camlglpk.get_obj_val lp in
            ans > 0.0 
        in
          (*one direction*)
          Camlglpk.set_mat_row lp nb_cstr (nb_vars + 1) (Array.append matrixA.(nb_cstr) (Array.make 1 1.0));
          Camlglpk.set_row_bnd_upper lp nb_cstr vectorB.(nb_cstr);
          if (Camlglpk.simplex lp false) && is_sat () then
            begin
              Camlglpk.delete lp;
              false
            end
          else
            begin
              Camlglpk.set_mat_row lp nb_cstr (nb_vars + 1) (Array.append matrixA.(nb_cstr + 1) (Array.make 1 1.0));
              Camlglpk.set_row_bnd_upper lp nb_cstr vectorB.(nb_cstr + 1);
              if (Camlglpk.simplex lp false) && is_sat () then
                begin
                  Camlglpk.delete lp;
                  false
                end
              else
                begin
                  Camlglpk.delete lp;
                  true
                end
            end
   *)
  let lst = match pred with
    | And lst -> lst
    | e -> failwith ("satLI, is_eq_implied: expected And, found"^(print e))
  in
  let (e1,e2) = match eq with 
    | Eq (e1,e2) -> (e1,e2)
    | e -> failwith ("satLI, is_eq_implied: expected Eq, found"^(print e))
  in
    if is_li_sat (And (Lt(e1,e2)::lst)) || is_li_sat (And (Lt(e2,e1)::lst))
      then false
      else true

(** Finds an expression (= source_expr) on the common terms.
 *
 * Assumes the given system is sat.
 * Strict < are removed (unsat -> sat).
 *)
let find_common_expr pred source_expr common_var common_sym =
  Message.print Message.Debug (lazy("find_common_expr for "^(print_expr source_expr)));
  let pred_lst = match pred with
    | Eq _ as eq -> [eq]
    | And lst -> List.filter (fun x -> match x with | Not _ | Lt _ -> false | _ -> true) lst
    | e -> failwith ("SatLI: expected And [...], =  found" ^ (print e))
  in
  let vars_set = List.fold_left (fun acc x -> ExprSet.add x acc) ExprSet.empty (List.flatten (List.map collect_li_vars pred_lst)) in
  let vars = ExprSet.fold (fun x acc -> x::acc) vars_set [] in
  let common_vars = List.filter (fun x -> only_vars_and_symbols common_var common_sym (Eq(x,Constant 0.0))) vars in
  let nb_vars = List.length vars in
    Message.print Message.Debug (lazy("Variables are: " ^ (Utils.string_list_cat ", " (List.map print_expr vars))));
    Message.print Message.Debug (lazy("Common Variables are: " ^ (Utils.string_list_cat ", " (List.map print_expr common_vars))));
    if nb_vars <= 0 then
      failwith ("SatLI, find_common_expr: expected variables")
    else
      begin
        let (target_row,target_val) = conj_to_matrix [Eq (Constant 0.0, source_expr)] vars in
        let (matrixA,vectorB) = conj_to_matrix pred_lst vars in
      
        (*assume lp problem has enough col and row*)
        let rec fill_glpk_problem lp index lst = match lst with
          (*!! at this point the transposition of the matrix is implicit (by filling row->col)!!*)
          | (Eq _)::xs ->
            begin
              Camlglpk.set_mat_col lp index (nb_vars + 1) (Array.append matrixA.(index) (Array.make 1 (vectorB.(index))));
              Camlglpk.set_col_bnd_free lp index; (*EQ => free*)
              fill_glpk_problem lp (index +1) xs
            end
          | (Leq _)::xs ->
            begin
              Camlglpk.set_mat_col lp index (nb_vars + 1) (Array.append matrixA.(index) (Array.make 1 (vectorB.(index))));
              Camlglpk.set_col_bnd_lower lp index 0.0; (*LEQ => (>= 0)*)
              fill_glpk_problem lp (index +1) xs
            end
          | (Lt _)::xs ->
            begin
              failwith "SatLI, find_common_expr: found an LT";
            end
          | [] -> ()
          | e::xs -> failwith ("SatLI, fill_glpk_problem: found "^(print e))
        in
        let fill_row_bounds lp row =
          Array.iteri
            (fun i x ->
              let v = List.nth vars i in
                if not (List.mem v common_vars) then
                  Camlglpk.set_row_bnd_fixed lp i x
                  (*else the value is free*)
            ) row
        in
        
        let get_answer lp l_size =
          let lambdas = Array.make l_size 0.0 in
            !solver.cols_primal lp l_size lambdas;
            lambdas
        in

        (*BEGINS HERE*)
        let l_size =  (List.length pred_lst) in
        let lp = Camlglpk.create () in
          Camlglpk.add_row lp (nb_vars + 1); (*+1 for the result vector*)
          Camlglpk.add_col lp l_size;(*#constraints*)
          fill_glpk_problem lp 0 pred_lst;
          fill_row_bounds lp (target_row.(0));
          if !solver.solve lp then
            begin
              let lambdas = get_answer lp l_size in
              let vars_coeff = Matrix.vector_times_matrix lambdas matrixA in
              let offset = Matrix.row_vect_times_col_vect lambdas vectorB in
              
              let target_coeff = Matrix.vector_substract vars_coeff (target_row.(0)) in
              let target_offset = (target_val.(0)) -. offset in

              let target_expr = simplify_expr (Sum [Constant target_offset;Matrix.symbolic_vector_multiplication target_coeff vars]) in
                Camlglpk.delete lp;
                target_expr
            end
          else
            begin
              Camlglpk.delete lp;
              failwith "SatLI: unable to build middle term"
            end
      end

(** Returns the unsat core for a formula using a solver not based on basis (i.e. interior).
 *  Assume the formula is unsat.
 *)
let unsat_core_no_basis formula =
  let lst = match formula with
    | And lst -> lst
    | True -> raise SAT
    | Or _ -> failwith "unsat_core: only for the conjunctiv fragment"
    | Atom _ -> failwith "unsat_core: atom only for sat solver, PL is not convex."
    | el -> [el]
  in

  let unsat_core = ref [] in
  let rec divide_and_try fixed lst =
    Message.print Message.Debug (lazy "divide_and_try called: ");
    Message.print Message.Debug (lazy ("    with           "^(Utils.string_list_cat ", " (List.map print lst))));
    Message.print Message.Debug (lazy ("    fixed is       "^(Utils.string_list_cat ", " (List.map print fixed))));
    Message.print Message.Debug (lazy ("    unsat_core is  "^(Utils.string_list_cat ", " (List.map print !unsat_core))));
    (* assume query_fct (And (lst @ fixed @ !unsat_core)) is unsat *)
    let n = List.length lst in
      if n = 1 then
        begin (*one element and unsat -> in unsat core*)
          unsat_core := (List.hd lst) :: !unsat_core
        end
      else
        begin
          let (head, tail) = Utils.split_list (n/2) lst in
          (** the next line removes the part if there is no element of the unsat core in it*)
          let to_try =
            if not (is_li_sat (And (head @ !unsat_core @ fixed))) then
              [head]
            else if not (is_li_sat (And (tail @ !unsat_core @ fixed))) then
              [tail]
            else
              [head;tail]
          in
          let rec search lst = match lst with
            | x::[] -> divide_and_try fixed x
            | x::xs ->
              divide_and_try ((List.flatten xs) @ fixed) x;
              search xs
            | [] -> failwith "SatLI, unsat_core_no_basis: non convex theory ??"
          in
            search to_try
        end
   in 
     divide_and_try [] lst;
     Message.print Message.Debug (lazy("UNSAT core is: "^(print (And !unsat_core))));
     And !unsat_core
      
(** Returns an over-approximation of the unsat core for a formula.
 *  This method is based on Motzkin's transposition Theorem.
 *  Assume the formula is unsat.
 *)
let unsat_core formula =
  match formula with
  | And lst ->
    begin
      let core = And (ClpLI.unsat_core lst) in
        assert (Global.is_off_assert() || not (is_li_sat core));
        core
    end
  | Eq _ | Leq _ | Lt _ as e ->
    begin
      match simplify e with
      | False -> e
      | _ -> raise SAT
    end
  | e -> failwith ("SatLI, unsat_core: expected And, found "^(print e))

(*
(** Returns the unsat core for a formula.
 *
 * WARNING: expensive ...
 * TODO faster over-approximation.
 * @raise SAT if the formula is not unsat.
 *)
let unsat_core formula =
  if is_li_sat formula then
    raise (SAT_FORMULA formula)
  else
    unsat_core_no_basis formula
*)
