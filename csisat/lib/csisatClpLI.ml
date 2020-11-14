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

(** This file is based on Rybalchenko et al. "Constraint Solving for Interpolation".
 * http://www.mpi-sws.mpg.de/~rybal/papers/vmcai07-constraints-for-interpolation.pdf
 *)

open   CsisatAst
open   CsisatAstUtil
open   CsisatLIUtils
(**/**)
module Global  = CsisatGlobal
module Message = CsisatMessage
module Utils   = CsisatUtils
module Matrix  = CsisatMatrix
(**/**)

(** Kind of lambda *)
type l_type = LT | LEQ | EQ

(** L and T correspond to additional constraints used to remove the case split of the algorithm. *)
type l_info = L of int (** index *)
            | T of int (** index *)
            | Lambda of int * int * l_type (** index, block (i.e position in the input list), type *)

let index_of info = match info with
  | L i | T i | Lambda (i,_,_) -> i

let print_lambda lambda = match lambda with 
  | L i ->             Message.print Message.Debug (lazy("L has index "^(string_of_int i)))
  | T i ->             Message.print Message.Debug (lazy("T has index "^(string_of_int i)))
  | Lambda(i,b,LT) ->  Message.print Message.Debug (lazy("L"^(string_of_int i)^" of block "^(string_of_int b)^" with <"))
  | Lambda(i,b,LEQ) -> Message.print Message.Debug (lazy("L"^(string_of_int i)^" of block "^(string_of_int b)^" with <="))
  | Lambda(i,b,EQ) ->  Message.print Message.Debug (lazy("L"^(string_of_int i)^" of block "^(string_of_int b)^" with ="))
let print_lambdas lambdas = List.iter print_lambda lambdas


(** Separates strict, non-strict, and equlity constraints
 *)
let split_eq_lt pred =
  let rec process (accLt, accLeq, accEq) pred = match pred with
    | And [] -> (accLt, (Leq(Constant 0.0, Constant 1.0))::accLeq, accEq)
    | And lst -> List.fold_left process (accLt, accLeq, accEq) lst
    | Leq _ as leq -> (accLt, leq::accLeq, accEq)
    | Lt  _ as lt  -> (lt::accLt, accLeq, accEq)
    | Eq _ as eq -> (accLt, accLeq, eq::accEq)
    | True -> (accLt, (Leq(Constant 0.0, Constant 1.0))::accLeq, accEq)
    | False -> (accLt, (Leq(Constant 1.0, Constant 0.0))::accLeq, accEq)
    | _ -> failwith "split_eq_lt: supports only And,Lt,Leq,Eq"
  in
    process ([],[],[]) pred


(** Extracts the answer.
 *  Assumes that the lambda's are sorted from smaller to bigger.
 *  @return a list of arrays (L_i) with strict/non-strict indication (blocks in increasing order)
 *)
let extract_answer lp lambdas =
  let rec count_non_strict results lambdas = match lambdas with
    | (Lambda (index,block,LT))::xs -> if results.(index) > !solver.solver_error then block else count_non_strict results xs
    | (Lambda (_,_,_))::xs -> count_non_strict results xs
    | x::xs -> failwith "extract_answer: expect only lambda's"
    | [] -> failwith "extract_answer: reached the end before a non-0 \\^lt"
  in
  let value = !solver.obj_val lp in
    if value >= (2.0 -. !solver.solver_error) then raise SAT
    else
      begin
        let last_lambda_index = List.length lambdas in
        let result = Array.make last_lambda_index 0.0 in
          !solver.cols_primal lp last_lambda_index result;
          (*the solver precision is 10e-7 => filter all term that are less than !solver.solver_error*)
          Array.iteri (fun i x -> if (abs_float x) < !solver.solver_error then result.(i) <- 0.0) result;
          Message.print Message.Debug (lazy("lambdas are: "^(Utils.string_list_cat ", " (Array.to_list (Array.map string_of_float result)))));
          Message.print Message.Debug (lazy ("solver returned: "^(string_of_float value)));
          let count = (*count is the number of non-strict interpolant*)
            if value < (1.0 -. !solver.solver_error) then
              begin
                Message.print Message.Debug (lazy "Non strict case");
                last_lambda_index (*is bigger than the number of interpolant, but not important*)
              end
            else
              begin
                let c = count_non_strict result lambdas in
                  Message.print Message.Debug (lazy ("The first "^(string_of_int c)^" are non strict."));
                  c
              end
          in
          let rec split_lambdas cur_block start len acc lambdas = match lambdas with
            | (Lambda (index,block,_))::xs ->
              begin
                if block <> cur_block then
                  begin
                    split_lambdas block (start+len) 0 ((cur_block < count, (Array.sub result start len))::acc) xs
                  end
                else split_lambdas cur_block start (len+1) acc xs
              end
            | x::xs -> failwith "extract_answer: expect only lambda's"
            | [] -> List.rev acc (*this does not return the last \'s (they are not needed)*)
          in
            split_lambdas 0 0 0 [] lambdas
      end

(** compute i = \*A and d = \*a
 *)
let compute_interpolant vars_size blocks results =
  let i_acc = Array.make vars_size 0.0 in
  let d_acc = ref 0.0 in
  let rec process blocks results acc = match (blocks,results) with
    | ((size_lt,size_leq,size_eq,mat,vect)::bs,(nonstrict,result)::rs) ->
      begin
        let i = Matrix.vector_times_matrix result mat in
        let i = Array.map (fun x -> if (abs_float x) < !solver.solver_error then 0.0 else x) i in
          for k = 0 to vars_size -1 do
            i_acc.(k) <- i_acc.(k) +. i.(k)
          done;
          Message.print Message.Debug (lazy("I: "^(Utils.string_list_cat ", " (Array.to_list (Array.map string_of_float i_acc)))));
          let d = Matrix.row_vect_times_col_vect result vect in
          let d = if (abs_float d) < !solver.solver_error then 0.0 else d in
            d_acc := d +. !d_acc;
            let strictness = if nonstrict then LEQ else LT in
              process bs rs ((Array.copy i_acc, strictness, !d_acc)::acc)
      end
    | (_,[]) -> List.rev acc
    | _ -> failwith "compute_interpolant: match error/too much result"
  in
    process blocks results [] 

(** Fills the Main matrix with the different sub-matrixes.
 *  Assume the GLPK problem is big enough.
 *  Implicitely preform the problem transposition.
 *)
let rec fill_glpk_problem lp nb_vars block index acc lst = match lst with
  | (size_lt,size_leq,size_eq,mat,_)::xs ->
    begin
      Message.print Message.Debug (lazy("\nMatrix of block "^(string_of_int block)^" :\n"^(Matrix.string_of_matrix mat)));
      let new_acc = ref acc in
      let new_index = ref index in
        (*!! at this point the transposition of the matrix is implicit (by filling row->col)!!*)
        Camlglpk.add_col lp (Array.length mat);
        for i = 0 to  size_lt - 1 do
          Camlglpk.set_mat_col lp !new_index nb_vars mat.(i);
          Camlglpk.set_col_bnd_lower lp !new_index 0.0; (*lambda >= 0*)
          new_acc := (Lambda (!new_index, block, LT))::(!new_acc);
          new_index := !new_index + 1
        done;
        for i = size_lt to  size_lt + size_leq - 1 do
          Camlglpk.set_mat_col lp !new_index nb_vars mat.(i);
          Camlglpk.set_col_bnd_lower lp !new_index 0.0; (*lambda >= 0*)
          new_acc := (Lambda (!new_index, block, LEQ))::(!new_acc);
          new_index := !new_index + 1
        done;
        for i = size_lt + size_leq to  size_lt + size_leq + size_eq - 1 do
          Camlglpk.set_mat_col lp !new_index nb_vars mat.(i);
          Camlglpk.set_col_bnd_free lp !new_index;
          new_acc := (Lambda (!new_index, block, EQ))::(!new_acc);
          new_index := !new_index + 1
        done;
        fill_glpk_problem lp nb_vars (block + 1) !new_index !new_acc xs
    end
  | [] -> acc
    

(** Prepare the constraints ->  split eq/leq/lt and creates a matrix/vector. *)
let prepare vars cnf =
  let (lt,leq,eq) = split_eq_lt cnf in
  let size_lt = List.length lt in
  let size_leq = List.length leq in
  let size_eq = List.length eq in
  let (mat,vect) = conj_to_matrix (lt @ leq @ eq) vars in
    (size_lt,size_leq,size_eq,mat,vect)

(** Collects the a's for minimization constraints*)
let rec get_all_as index target_array lst = match lst with
  | (_,_,_,_,vect)::xs ->
    begin
      let size = Array.length vect in
        Array.blit vect 0 target_array index size;
        get_all_as (index + size) target_array xs
    end
  | [] -> ()

(** For the 'strictness' constraint*)
let rec get_lt_lambdas target_array lambdas = match lambdas with
  | (Lambda (i,_,LT))::xs ->
      target_array.(i) <- (-1.0);
      get_lt_lambdas target_array xs
  | _::xs -> get_lt_lambdas target_array xs
  | [] -> ()
    

(** compute a series of |lst| -1 (inductive) interpolant
 *)
let interpolate_clp lst =
  Message.print Message.Debug (lazy("interpolate_clp called: " ^ (Utils.string_list_cat ", " (List.map print lst))));
  let vars_set = List.fold_left (fun acc x -> ExprSet.add x acc) ExprSet.empty (List.flatten (List.map collect_li_vars lst)) in
  let vars = exprSet_to_ordSet vars_set in
  let nb_vars = List.length vars in
    Message.print Message.Debug (lazy("Variables are: " ^ (Utils.string_list_cat ", " (List.map print_expr vars))));
    if nb_vars <= 0 then
      (*simple case when formula contains only constant terms*)
      let simple = List.map simplify lst in
        let rec check_simple acc t lst = match lst with
          | True::xs when t ->  check_simple (True::acc) true xs
          | True::xs -> check_simple (False::acc) false xs
          | False::xs when t -> check_simple (True::acc) false xs
          | False::xs -> check_simple (False::acc) false xs
          | e::_ -> failwith ("check_simple: match error"^(print e))
          | [] -> List.rev acc
        in
        let f = match List.hd simple with
          | True -> true
          | False -> false
          | e -> failwith ("check_simple first element: match error "^(print e))
        in
          check_simple [] f (List.tl simple)
    else

      (*BEGIN HERE*)
      let prepared = List.map (prepare vars) lst in
      let lp = Camlglpk.create () in
        Camlglpk.add_row lp nb_vars;
        for i = 0 to nb_vars -1 do (*Sum l*A = 0*)
          Camlglpk.set_row_bnd_fixed lp i 0.0
        done;
        let lambda1 = fill_glpk_problem lp nb_vars 0 0 [] prepared in
        let last_lambda_index = index_of (List.hd lambda1) in
        let l_index = last_lambda_index + 1 in
        let t_index = last_lambda_index + 2 in
        let lambda2 = (L l_index)::lambda1 in
        let lambdas = (T t_index)::lambda2 in
          print_lambdas lambdas;
          Camlglpk.add_col lp 2;(* for L and T *)
          Camlglpk.set_col_bnd_upper lp l_index 1.0; (*L <= 1*)
          Camlglpk.set_col_bnd_lower lp t_index 0.0; (*T >= 0*)
          Camlglpk.add_row lp 2;(* min cstr *)
          let all_as = Array.make (last_lambda_index + 3) 0.0 in
            get_all_as 0 all_as prepared;
            all_as.(l_index) <- (-1.0);
            all_as.(t_index) <- (-1.0);
            Camlglpk.set_mat_row lp  nb_vars  (Array.length all_as) all_as;
            Camlglpk.set_row_bnd_upper lp nb_vars (-2.0);
            Array.fill all_as 0 (Array.length all_as) 0.0;
            get_lt_lambdas all_as lambdas;
            all_as.(l_index) <- 1.0;
            Camlglpk.set_mat_row lp (nb_vars + 1) (Array.length all_as) all_as;
            Camlglpk.set_row_bnd_upper lp (nb_vars + 1) (0.0);
            (*objective function*)
            Camlglpk.set_minimize lp;
            Camlglpk.set_obj_coef lp t_index 1.0;
            if !solver.solve lp then
              begin
                let results = extract_answer lp (List.rev lambda1) in
                let is_ds = compute_interpolant nb_vars prepared results in
                let res = List.map (fun (i,strictness,d) ->
                      begin
                        let expr = Matrix.symbolic_vector_multiplication i vars in
                          Message.print Message.Debug (lazy("left part is: "^(print_expr expr)));
                        let full_ans = match strictness with
                          | LT -> Lt (expr, Constant d)
                          | LEQ -> Leq(expr, Constant d)
                          | EQ -> failwith "interpolate_clp: invalide strictness -> EQ"
                        in
                          simplify full_ans
                      end
                      ) is_ds
                 in
                   Camlglpk.delete lp;
                   res
              end
            else
              begin 
                Camlglpk.dump_problem lp;
                Camlglpk.delete lp;
                raise LP_SOLVER_FAILURE
              end
        

(** Returns an over-approximation of the unsat core for a formula.
 *  This method is based on Motzkin's transposition Theorem.
 *  Assume the formula is unsat.
 *)
let unsat_core lst =
  Message.print Message.Debug (lazy("unsat_core_clp called: " ^ (Utils.string_list_cat ", " (List.map print lst))));
  let vars_set = List.fold_left (fun acc x -> ExprSet.add x acc) ExprSet.empty (List.flatten (List.map collect_li_vars lst)) in
  let vars = exprSet_to_ordSet vars_set in
  let nb_vars = List.length vars in
    Message.print Message.Debug (lazy("Variables are: " ^ (Utils.string_list_cat ", " (List.map print_expr vars))));
    assert (Global.is_off_assert() || nb_vars > 0 );

      (*Warning: the next line works with the assumption that each element of lst is atomic*)
      let prepared = List.map (prepare vars) lst in
      let lp = Camlglpk.create () in
        Camlglpk.add_row lp nb_vars;
        for i = 0 to nb_vars -1 do (*Sum l*A = 0*)
          Camlglpk.set_row_bnd_fixed lp i 0.0
        done;
        let lambda1 = fill_glpk_problem lp nb_vars 0 0 [] prepared in
        let last_lambda_index = index_of (List.hd lambda1) in
        let l_index = last_lambda_index + 1 in
        let t_index = last_lambda_index + 2 in
        let lambda2 = (L l_index)::lambda1 in
        let lambdas = (T t_index)::lambda2 in
          print_lambdas lambdas;
          Camlglpk.add_col lp 2;(* for L and T *)
          Camlglpk.set_col_bnd_upper lp l_index 1.0; (*L <= 1*)
          Camlglpk.set_col_bnd_lower lp t_index 0.0; (*T >= 0*)
          Camlglpk.add_row lp 2;(* min cstr *)
          let all_as = Array.make (last_lambda_index + 3) 0.0 in
            get_all_as 0 all_as prepared;
            all_as.(l_index) <- (-1.0);
            all_as.(t_index) <- (-1.0);
            Camlglpk.set_mat_row lp  nb_vars  (Array.length all_as) all_as;
            Camlglpk.set_row_bnd_upper lp nb_vars (-2.0);
            Array.fill all_as 0 (Array.length all_as) 0.0;
            get_lt_lambdas all_as lambdas;
            all_as.(l_index) <- 1.0;
            Camlglpk.set_mat_row lp (nb_vars + 1) (Array.length all_as) all_as;
            Camlglpk.set_row_bnd_upper lp (nb_vars + 1) (0.0);
            (*objective function*)
            Camlglpk.set_minimize lp;
            Camlglpk.set_obj_coef lp t_index 1.0;
            if !solver.solve lp then
              begin
                let value = !solver.obj_val lp in
                  if value >= (2.0 -. !solver.solver_error) then raise SAT
                  else
                    begin
                      (*check which constraints are basic*)
                      let (_,core) =
                        List.fold_left
                          (fun (i,acc) el ->
                            if !solver.is_col_basic lp i then (i+1, el::acc)
                            else (i+1, acc)
                          )
                          (0,[]) lst
                      in
                        Camlglpk.delete lp;
                        core
                    end
              end
            else
              begin 
                Camlglpk.dump_problem lp;
                Camlglpk.delete lp;
                raise LP_SOLVER_FAILURE
              end


(** this is the DNF way*)
let interpolate lst =
  (*TODO: generalize*)
  if (List.length lst) <> 2 then failwith "no path interpolation for the moment" else ();

  let fdnf = List.map (fun x -> dnf (simplify (split_neq (simplify x)))) lst in

  (*takes care of the disj*)
  let lazy_map_all_pairs f xs ys =
    let rec lazy_map_ys acc x ys =
      match ys with
      | y::yss ->
        let it = List.hd (f [x;y]) in
          if it = False then False (*useless without simplification*)
          else lazy_map_ys (it::acc) x yss
      | [] -> 
        begin
         if List.length acc = 1 then List.hd acc
         else And acc
        end
    in
    let rec lazy_map_xs acc xs =
      match xs with
      | x::xss ->
        let it = lazy_map_ys [] x ys in
          if it = True then True (*useless without simplification*)
          else lazy_map_xs (it::acc) xss
      | [] ->
        begin
         if List.length acc = 1 then List.hd acc
         else Or acc
        end
    in
    lazy_map_xs [] xs
  in
    match fdnf with
    | (Or a)::(Or b)::[] -> lazy_map_all_pairs interpolate_clp a b
    | _ -> failwith "interpolate: match error"


