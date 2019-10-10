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

(** General methods that operate on the AST.
 *)

open   CsisatAst
(**/**)
module Message = CsisatMessage
module Utils   = CsisatUtils
module OrdSet  = CsisatOrdSet
(**/**)

let rec print_expr expr = match expr with
  | Constant cst -> Utils.my_string_of_float cst
  | Variable v -> v
  | Application (sym, lst) -> sym ^ "(" ^ (Utils.string_list_cat ", " (List.map print_expr lst)) ^")"
  | Sum lst ->  "(" ^ (Utils.string_list_cat " + " (List.map print_expr lst)) ^")"
  | Coeff (co, expr) -> (Utils.my_string_of_float co) ^ "*" ^ (print_expr expr)

let rec print_pred p =
  match p with
  | False -> "false"
  | True -> "true"
  | And lst -> "(" ^ (Utils.string_list_cat " & " (List.map print_pred lst)) ^")"
  | Or lst -> "(" ^ (Utils.string_list_cat " | " (List.map print_pred lst)) ^")"
  | Not p -> "not " ^ print_pred p
  | Eq (e1,e2) -> (print_expr e1) ^ " = " ^ (print_expr e2)
  | Lt (e1,e2) -> (print_expr e1) ^ " < " ^ (print_expr e2)
  | Leq (e1,e2) -> (print_expr e1) ^ " <= " ^ (print_expr e2)
  | Atom (External str) -> str
  | Atom (Internal i) -> "atom"^(string_of_int i)

let print p = print_pred p
 
let rec print_infix pred_lst =
  let buffer = Buffer.create 0 in
    List.iter
      (fun x ->
        Buffer.add_string buffer ((print_pred x) ^ "; " )
      ) pred_lst;
    (*remove the trailling "; "*)
    Buffer.sub buffer 0 ((Buffer.length buffer) -2)

(** convert to NNF.
 * @param negate true means that an odd number of Not were found
 * @param pred the predicate to convert
 *)
let rec push_negation negate pred = match pred with
  | True when negate -> False
  | True -> True
  | False when negate -> True
  | False -> False
  | Not pred -> push_negation (not negate) pred
  | And lst when negate -> Or (List.map (push_negation negate) lst) 
  | And lst -> And (List.map (push_negation negate) lst) 
  | Or lst when negate -> And (List.map (push_negation negate) lst) 
  | Or lst -> Or (List.map (push_negation negate) lst) 
  | Lt (e1,e2) when negate -> Leq (e2, e1)
  | Leq (e1,e2) when negate -> Lt (e2, e1)
  | p when negate -> Not p
  | p -> p

(** convert to NNF. *)
let nnf = push_negation false

(** Simplifies an expression, work as follows:
    distribute_coeff,
    flatten Sum,
    merge coeff + sort,
    delete uneeded term,
    remove uneeded coeff.
*)
let rec simplify_expr expr = 
  let rec distribute_coeff coeff expr =
    match expr with
    | Constant c1 -> Constant (coeff *. c1)
    | Variable _ as v -> Coeff (coeff, v)
    | Application (sym, lst) -> Coeff(coeff, Application(sym, List.map (distribute_coeff 1.0) lst))
    | Sum lst -> Sum (List.map (distribute_coeff coeff) lst)
    | Coeff (c,e) -> distribute_coeff (coeff *. c) e
  in
  let rec flatten expr = 
    match expr with
    | Constant _ as c -> c
    | Variable _ as e -> e
    | Application (sym, lst) -> Application(sym, List.map flatten lst)
    | Sum lst -> Sum (List.fold_left ( fun acc x -> match x with
        | Sum lst -> lst @ acc
        | _ as exp -> exp::acc ) [] (List.map flatten lst))
    | Coeff (c,e) -> Coeff(c, flatten e)
  in
  let rec merge_cst expr = match expr with
    | Constant _ as c -> c
    | Variable _ as v -> v
    | Application (sym, lst) -> Application(sym, List.map merge_cst lst)
    | Sum lst ->
      let res = List.fold_left (fun (cst,lst) x -> match x with
        | Constant c -> (cst +. c, lst)
        | Variable _ as v -> (cst, v::lst)
        | Application (sym, flst) -> (cst, Application(sym, List.map merge_cst flst)::lst)
        | Sum lst -> failwith "Sum should be flattenend"
        | Coeff (c, Application(sym, flst)) -> (cst, Coeff(c, Application(sym, List.map merge_cst flst))::lst)
        | Coeff (c, Variable _) as co -> (cst, co::lst)
        | Coeff (_, Constant _) | Coeff(_, Sum _) | Coeff(_, Coeff _)-> failwith "merge_cst: arg not normalized"
        ) (0.0, []) lst
      in Sum((Constant (fst res))::(snd res))
    | Coeff (c, Application(sym, flst)) -> Coeff(c, Application(sym, List.map merge_cst flst))
    | Coeff _ as co -> co
  in
  let rec get_var expr =
    match expr with
    | Constant _ -> []
    | Variable _ as v -> [v]
    | Application (sym, lst) -> List.fold_left (fun acc x -> OrdSet.union (get_var x) acc) [] lst
    | Sum lst -> List.fold_left (fun acc x -> OrdSet.union (get_var x) acc) [] lst
    | Coeff (c,e) -> get_var e
  in
  let rec merge_var var expr = match expr with
    | Constant _ as c -> c
    | Variable _ as v -> v
    | Application (sym, flst) -> Application(sym, List.map (merge_var var) flst)
    | Sum lst ->
      let res = List.fold_left (fun (v,lst) x -> match x with
        | Constant _ as cst -> (v, cst::lst)
        | Variable _ as var2 -> if var = var2 then(v +. 1.0 , lst) else (v, var2::lst)
        | Application (sym, flst) -> (v, Application(sym, List.map (merge_var var) flst)::lst)
        | Sum lst -> failwith "Sum should be flattenend"
        | Coeff (c, Application(sym, flst)) -> (v, Coeff(c, Application(sym, List.map (merge_var var) flst))::lst)
        | Coeff (c, Variable var2) as co -> if var = Variable var2 then (v +. c , lst) else (v, co::lst)
        | Coeff (_, Constant _) | Coeff(_, Sum _) | Coeff(_, Coeff _) -> failwith "merge_var: arg not normalized"
        ) (0.0, []) lst
      in Sum((Coeff (fst res, var))::(snd res))
    | Coeff (c, Application(sym, flst)) -> Coeff(c, Application(sym, List.map (merge_var var) flst))
    | Coeff _ as co -> co
  in
  let rec get_appl expr =
    match expr with
    | Constant _ -> []
    | Variable _ -> []
    | Application (sym, lst) as a -> List.fold_left (fun acc x -> OrdSet.union (get_appl x) acc) [a] lst
      (*a::(List.flatten (List.map get_appl lst))*)
    | Sum lst -> List.fold_left (fun acc x -> OrdSet.union (get_appl x) acc) [] lst
      (*List.flatten (List.map get_appl lst)*)
    | Coeff (c,e) -> get_appl e
  in
  let rec merge_appl appl expr = match expr with
    | Constant _ as c -> c
    | Variable _ as v -> v
    | Application (sym, lst) -> Application(sym, List.map (merge_appl appl) lst)
    | Sum lst ->
      let res = List.fold_left (fun (a,lst) x -> match x with
        | Constant _ as cst -> (a, cst::lst)
        | Variable _ as var -> (a, var::lst)
        | Application (sym, flst) ->
            let a2 = Application(sym, List.map (merge_appl appl) flst) in
              if a2 = appl then (a +. 1.0, lst) else (a, a2::lst)
        | Sum lst -> failwith "Sum should be flattenend"
        | Coeff (c, Application(sym, flst)) ->
            let a2 = Application(sym, List.map (merge_appl appl) flst) in
              if a2 = appl then (a +. c, lst) else (a, (Coeff(c,a2))::lst)
        | Coeff (c, Variable _) as co -> (a, co::lst)
        | Coeff (_, Constant _) | Coeff(_, Sum _) | Coeff(_, Coeff _)-> failwith "merge_var: arg not normalized"
        ) (0.0, []) lst
      in Sum((Coeff (fst res, appl))::(snd res))
    | Coeff (c, Application(sym, flst)) -> Coeff(c, Application(sym, List.map (merge_appl appl) flst))
    | Coeff _ as co -> co
  in
  let is_sum_relevant expr = match expr with
    | Constant 0.0 -> false
    | Coeff(0.0, _) -> false
    | _ -> true
  in
  let rec prune expr =
    match expr with
    | Constant _ as c -> c
    | Variable _ as v -> v
    | Application (sym, lst) -> Application(sym, List.map prune lst)
    | Sum lst ->
      begin
        let lst2 = List.filter is_sum_relevant lst in
        let lst3 = List.map prune lst2 in
          match List.length lst3 with
            | 0 -> Constant 0.0
            | 1 -> List.hd lst3
            | _ -> Sum (List.sort compare lst3)
      end
    | Coeff (c,e) ->
        if c = 0.0 then Constant 0.0
        else if c = 1.0 then prune e
        else Coeff(c, prune e)
  in
  let distr = distribute_coeff 1.0 expr in
  let flat = flatten distr in
  let cst = merge_cst flat in
  let vars = get_var cst in
  let merged_var = List.fold_left (fun acc x -> merge_var x acc) cst vars in
  let pruned = prune merged_var in
  let apps = get_appl pruned in
  let merged_app =  List.fold_left (fun acc x -> merge_appl x acc) pruned apps in (*BUGGY: apps are not normalized ...*)
  let pruned2 = prune merged_app in
    (*Message.print Message.Debug (lazy("  original:    " ^ (print_expr expr)));*)
    (*Message.print Message.Debug (lazy("  distributed: " ^ (print_expr distr)));*)
    (*Message.print Message.Debug (lazy("  flat:        " ^ (print_expr flat)));*)
    (*Message.print Message.Debug (lazy("  merge cst:   " ^ (print_expr cst)));*)
    (*Message.print Message.Debug (lazy("  merge var:   " ^ (print_expr merged_var)));*)
    (*Message.print Message.Debug (lazy("  prune:       " ^ (print_expr pruned)));*)
    (*Message.print Message.Debug (lazy("  merge app:   " ^ (print_expr merged_app)));*)
    (*Message.print Message.Debug (lazy("  simple:      " ^ (print_expr pruned2)));*)
    pruned2

(** Basic simplification steps for literals: constant inequalities, ...
 * known BUG: loop forever when a float value is NAN.
 *)
let rec simplify_literals tree = match tree with
  | Eq (Constant c1, Constant c2) -> if c1 = c2 then True else False
  | Eq (e1, e2) ->
    let (se1,se2) = (simplify_expr e1, simplify_expr e2) in 
    let c = compare se1 se2 in
    let res = if c = 0 then True
              else if c <= 0 then Eq(se1, se2)
              else Eq (se2, se1)
    in
      if res <> tree then simplify_literals res
      else res
  | Lt (Constant c1, Constant c2) ->
    if c1 < c2 then True else False
  | Lt (e1, e2) ->
    let (se1,se2) = (simplify_expr e1, simplify_expr e2) in 
    let res = Lt(se1,se2) in
      if res <> tree then simplify_literals res
      else res
  | Leq (Constant c1, Constant c2) ->
    if c1 <= c2 then True else False
  | Leq (e1, e2) ->
    let (se1,se2) = (simplify_expr e1, simplify_expr e2) in 
    let res = Leq(se1,se2) in
      if res <> tree then simplify_literals res
      else res
  | p -> p


(** Checks that the formula contains no And or Or. *)
let rec is_atomic formula = match formula with
  | False | True -> true
  | Eq _ | Lt _ | Leq _ | Atom _ -> true
  | And _ | Or _ -> false
  | Not p -> is_atomic p

(** returns the negation of a, assuming a is a proposition.
 * If a is not a proposition, then the returned value is not normalized
 *)
let contra x = match x with
  | True -> False
  | False -> True
  | Lt (e1, e2) -> Leq(e2, e1)
  | Leq (e1, e2) -> Lt(e2, e1)
  | Not e -> e
  | _ as n -> Not n

(** normalisation of formula.
 * @param proposition_simplification the function called to normalize literals
 * @param tree the formula to normalize
 *)
let rec normalize_common proposition_simplification tree =
  match tree with
  | And ilst ->
    let new_lst =
      OrdSet.list_to_ordSet (
      List.filter (fun x -> x <> True) (
      List.fold_left
      ( fun acc x -> 
        match x with
        | And lst -> lst @ acc
        | _ -> x::acc
      )
      [] (List.map (normalize_common proposition_simplification) ilst)))
    in
      if List.exists (fun x -> x = False) new_lst then
        False
      else
        begin
          match new_lst with
          | x::[] -> x
          | [] -> True
          | lst -> And lst
        end
  | Or ilst ->
    let new_lst =
      OrdSet.list_to_ordSet (
      List.fold_left
      ( fun acc x -> 
        match x with
        | Or lst -> lst @ acc
        | _ -> x::acc
      )
      [] (List.map (normalize_common proposition_simplification) ilst))
    in 
      if List.exists (fun x -> x = True) new_lst then
        True
      else
        begin
          match (List.filter (fun x -> x <> False) new_lst) with
          | x::[] -> x
          | [] -> if new_lst = [] then True else False
          | lst -> Or lst
        end
  | Not i -> let n = normalize_common proposition_simplification i in contra n
  | p -> proposition_simplification p

let normalize tree = normalize_common simplify_literals tree
let normalize_only tree = normalize_common (fun x -> x) tree

(** Checks that x and ¬x does not appears in a And/Or.
 * Assumes the formula was normalized before
 *)
let rec remove_lit_clash tree =
  let check lst =
    let seen = Hashtbl.create 20 in
    let rec chk_insert lst = match lst with
      | x::xs ->
        begin
          if is_atomic x then
            begin
              let c = contra x in
                if not (Hashtbl.mem seen c) then
                  begin
                    Hashtbl.add seen x ();
                    chk_insert xs
                  end
                else true
            end
          else chk_insert xs
        end
      | [] -> false
    in
      chk_insert lst  
  in
    match tree with
    | And lst ->
      begin
        let lst = List.map remove_lit_clash lst in
          if check lst then False
          else And lst
      end
    | Or lst ->
      begin
        let lst = List.map remove_lit_clash lst in
          if check lst then True
          else Or lst
      end
    | t -> t


(** Orders equalities, normalisation of equalities. *)
let rec order_eq eq = match eq with
  | And ilst -> And (List.map order_eq ilst)
  | Or ilst -> Or (List.map order_eq ilst)
  | Not i -> Not (order_eq i)
  | Eq (e1, e2) as eq ->
    let c = compare e1 e2 in
      if c = 0 then eq
      else if c <= 0 then Eq(e1, e2)
      else Eq (e2, e1)
  | p -> p

(** Checks that the formula is conjunctive.
 * Assumes NNF.
 *)
let is_conj_only p =
  let no_disj e = match e with
    | Or _ -> false
    | _ -> true
  in
    match p with
    | And lst -> List.for_all no_disj lst
    | Eq _ | Not _ | Lt _ | Leq _ | Atom _ | True | False -> true
    | _ -> false


(** Checks that the formula is CNF.
 * Assumes NNF.
 *)
let is_cnf formula =
  let rec contains_no_sub f = match f with
    | And _ | Or _ -> false
    | Not i -> contains_no_sub i
    | Eq _ | Leq _ | Lt _ | Atom _ | True | False -> true
  in
  let contains_or_no_sub f = match f with
    | And _ -> false
    | Or lst  -> List.for_all contains_no_sub lst
    | Not i -> contains_no_sub i
    | Eq _ | Leq _ | Lt _ | Atom _ | True | False -> true
  in
    match formula with
    | Or lst -> List.for_all contains_no_sub lst
    | And lst -> List.for_all contains_or_no_sub lst
    | _ -> true

(** cnf strict enforces 'a' as And '[ Or [ a ] ]' *)
let is_cnf_strict f = match f with
  | And lst ->
    List.for_all (fun x -> match x with 
      | Or lst ->
        List.for_all ( fun x -> match x with
          | And _ | Or _ | Not (And _) | Not (Or _) -> false
          | _ -> true
        ) lst
      | _ -> false
    ) lst
  | _ -> false

(** convert a formula to CNF.
 * Expensive (exponential).
 * Assume NNF.
 *)
let cnf tree =
  Message.print Message.Debug (lazy("convertinf to CNF:  " ^ (print_pred tree)));
  let rec process t = match t with
    | And lst -> Utils.rev_flatten (List.rev_map process lst)
    | Or lst ->
      let merge cnf1 cnf2 =
        Utils.rev_flatten (List.rev_map (fun x -> List.rev_map (fun y -> x @ y) cnf2) cnf1)
      in
      let rec iterate acc l (*: list list list == disj of conj of disj *) =
        match l with
        | x :: xs -> iterate (merge x acc) xs
        | [] -> acc
      in
      let sub_cnf = List.rev_map process lst in
        iterate [[]] sub_cnf
    | _ as t -> [[t]]
  in
    And (List.map (fun x -> Or x) (process tree))

(** convert a formula to DNF.
 * Expensive (exponential).
 * Assumes NNF.
 *)
let dnf tree =
  let rec process t = match t with
    | Or lst -> Utils.rev_flatten (List.rev_map process lst)
    | And lst ->
      let merge dnf1 dnf2 =
        Utils.rev_flatten (List.rev_map (fun x -> List.rev_map (fun y -> x @ y) dnf2) dnf1)
      in
      let rec iterate acc l (*: list list list == conj of disj of conj *) =
        match l with
        | x :: xs -> iterate (merge x acc) xs
        | [] -> acc
      in
      let sub_dnf = List.rev_map process lst in
        iterate [[]] sub_dnf
    | _ as t -> [[t]]
  in
    Or (List.map (fun x -> And x) (process tree))


let simplify pred =  
  Message.print Message.Debug (lazy("  simplifing:  " ^ (print_pred pred)));
  let p = nnf pred in
    Message.print Message.Debug (lazy("  push:        " ^ (print_pred p)));
    let n = normalize p in
      Message.print Message.Debug (lazy("  normalize:   " ^ (print_pred n)));
      n

(**************************************)
module Expr =
  struct
    type t = expression
    let compare = compare
  end
module ExprSet = Set.Make(Expr)

module Pred =
  struct
    type t = predicate
    let compare = compare
  end
module PredSet = Set.Make(Pred)

let exprSet_to_ordSet set =
  OrdSet.list_to_ordSet (ExprSet.fold (fun x acc -> x::acc) set [])

let predSet_to_ordSet set =
  OrdSet.list_to_ordSet (PredSet.fold (fun x acc -> x::acc) set [])
(**************************************)

(** Returns the expressions of a predicate as a set.
 * Fetches only top-level expressions.
 *)
let get_expr_set pred =
  let rec process pred = match pred with
    | False -> ExprSet.empty
    | True ->  ExprSet.empty
    | And lst -> List.fold_left (fun acc x -> ExprSet.union acc x) ExprSet.empty (List.map process lst) 
    | Or lst -> List.fold_left (fun acc x -> ExprSet.union acc x) ExprSet.empty (List.map process lst) 
    | Not p -> process p
    | Eq (e1,e2) -> ExprSet.add e2 (ExprSet.singleton e1)
    | Lt (e1,e2) -> ExprSet.add e2 (ExprSet.singleton e1)
    | Leq (e1,e2) -> ExprSet.add e2 (ExprSet.singleton e1)
    | Atom _ -> ExprSet.empty
  in
    process pred

(** Returns the expressions of a predicate as a list
 * Fetches only top-level expressions.
 * @return an OrdSet.
 *)
let get_expr pred = exprSet_to_ordSet (get_expr_set pred)

(** Returns the expressions of a predicate as a set.
 * Also fetches subexpressions.
 * @return an OrdSet.
 *)
let get_expr_deep pred =
  let rec process_expr expr = match expr with
    | Constant _ as c -> ExprSet.singleton c
    | Variable _ as v -> ExprSet.singleton v
    | Application (_, lst) as appl -> ExprSet.add appl (List.fold_left (fun acc x ->ExprSet.union acc (process_expr x)) ExprSet.empty lst)
    | Sum lst as sum -> ExprSet.add sum (List.fold_left (fun acc x ->ExprSet.union acc (process_expr x)) ExprSet.empty lst)
    | Coeff (c,e) as co ->ExprSet.add co (process_expr e)
  in
  let rec process_pred pred = match pred with
    | False -> ExprSet.empty
    | True ->  ExprSet.empty
    | And lst -> List.fold_left (fun acc x -> ExprSet.union acc x) ExprSet.empty (List.map process_pred lst) 
    | Or lst -> List.fold_left (fun acc x -> ExprSet.union acc x) ExprSet.empty (List.map process_pred lst) 
    | Not p -> process_pred p
    | Eq (e1,e2) -> ExprSet.union (process_expr e1) (process_expr e2)
    | Lt (e1,e2) -> ExprSet.union (process_expr e1) (process_expr e2)
    | Leq (e1,e2) -> ExprSet.union (process_expr e1) (process_expr e2)
    | Atom _ -> ExprSet.empty
  in
    exprSet_to_ordSet (process_pred pred)
  

(** Gets all the sub-predicates.
 * @return a Set.
 *)
let get_subterm_set pred =
  let rec process pred = match pred with
    | False -> PredSet.empty
    | True -> PredSet.empty
    | And lst as an -> List.fold_left (fun acc x -> PredSet.union acc (process x)) (PredSet.singleton an) lst
    | Or lst as o -> List.fold_left (fun acc x -> PredSet.union acc (process x)) (PredSet.singleton o) lst
    | Not p as n -> PredSet.union (PredSet.singleton n) (process p)
    | Eq _ as eq -> PredSet.singleton eq
    | Lt _ as lt -> PredSet.singleton lt
    | Leq _ as leq -> PredSet.singleton leq
    | Atom _ as a -> PredSet.singleton a
  in
    process pred

(** Gets all the sub-predicates.
 * @return an OrdSet.
 *)
let get_subterm pred = predSet_to_ordSet (get_subterm_set pred)

(** get the sub-predicates but does not go inside literals
 * Assumes NNF.
 * @return an OrdSet.
 *)
let get_subterm_nnf pred =
  let rec process pred = match pred with
    | False -> []
    | True -> []
    | And lst as an -> List.fold_left (fun acc x -> OrdSet.union acc (process x)) [an] lst
    | Or lst as o -> List.fold_left (fun acc x -> OrdSet.union acc (process x)) [o] lst
    | Not _ as n -> [n] 
    | Eq _ as eq -> [eq]
    | Lt _ as lt -> [lt]
    | Leq _ as leq -> [leq]
    | Atom _ as a -> [a]
  in
    process pred

(** the proposition contained in a literal. *)
let proposition_of_lit x = match x with
  | Not (Eq _ as eq) -> eq
  | Eq _ as eq -> eq
  | Lt _ as lt -> lt
  | Leq (e1,e2) -> Lt(e2,e1)
  | Not (Atom _ as at) -> at
  | Atom _ as at -> at
  | err -> failwith ("AstUtil, proposition_of_lit: not a literal "^(print err))

(** Gets the propositions of a formula.
 * @return an OrdSet.
 *)
let get_proposition pred =
  let rec process pred = match pred with
    | False -> []
    | True -> []
    | And lst -> List.fold_left (fun acc x -> OrdSet.union acc (process x)) [] lst
    | Or lst -> List.fold_left (fun acc x -> OrdSet.union acc (process x)) [] lst
    | Not p -> process p
    | Eq _ as eq -> [eq]
    | Lt _ as lt -> [lt]
    | Leq (e1,e2)  -> [Lt(e2,e1)]
    | Atom _ as a -> [a]
  in
    process pred

(** Gets the propositions of a formula.
 * @return a Set.
 *)
let get_proposition_set pred =
  let rec process pred = match pred with
    | False -> PredSet.empty
    | True -> PredSet.empty
    | And lst -> List.fold_left (fun acc x -> PredSet.union acc (process x)) PredSet.empty lst
    | Or lst -> List.fold_left (fun acc x -> PredSet.union acc (process x)) PredSet.empty lst
    | Not p -> process p
    | Eq _ as eq -> PredSet.singleton eq
    | Lt _ as lt -> PredSet.singleton lt
    | Leq (e1,e2)  -> PredSet.singleton (Lt(e2,e1))
    | Atom _ as a -> PredSet.singleton a
  in
    process pred

(** Gets the propositional atoms of a formula.
 * @return an OrdSet.
 *)
let get_atoms pred =
  let rec process pred = match pred with
    | False -> []
    | True -> []
    | And lst -> List.fold_left (fun acc x -> OrdSet.union acc (process x)) [] lst
    | Or lst -> List.fold_left (fun acc x -> OrdSet.union acc (process x)) [] lst
    | Not p -> process p
    | Eq _  | Lt _ | Leq _ -> []
    | Atom _ as a -> [a]
  in
    process pred

(** Returns the variables of a predicate.
 * @return an OrdSet.
 *)
let get_var formula =
  let rec process_expr expr = match expr with
    | Constant _ -> []
    | Variable _ as v -> [v]
    | Application (_, lst) -> List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc) [] lst
    | Sum lst -> List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc) [] lst
    | Coeff (c,e) -> process_expr e
  in
  let expr = get_expr_deep formula in
    List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc) [] expr

(** Returns the uninterpreted function symbols of a predicate.
 * @return an OrdSet.
 *)
let get_fct_sym formula =
  let rec process_expr expr = match expr with
    | Constant _ -> []
    | Variable _ -> []
    | Application (f, lst) -> OrdSet.union [f] (List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc ) [] lst)
    | Sum lst -> List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc) [] lst
    | Coeff (c,e) -> process_expr e
  in
  let expr = get_expr_deep formula in
    List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc) [] expr

(** Does the formula contains only given variable + constant term (no functions) ?*)
let only_vars vars formula =
  let rec only_vars_expr expr = match expr with
    | Constant _ -> true
    | Variable _ as v -> List.mem v vars
    | Application (_, _) -> false
    | Sum lst -> List.for_all only_vars_expr lst
    | Coeff (c,e) -> only_vars_expr e
  in
  let rec only_vars_pred formula = match formula with
    | And lst | Or lst -> List.for_all only_vars_pred lst
    | Not p -> only_vars_pred p
    | Eq (e1,e2) | Lt (e1,e2) | Leq (e1,e2) -> (only_vars_expr e1) && (only_vars_expr e2)
    | Atom _ -> false
    | _ -> true
  in
   only_vars_pred formula

(** Does the formula contains only given variable, fct sym + constant term ? *)
let only_vars_and_symbols vars sym formula =
  let rec process_expr expr = match expr with
    | Constant _ -> true
    | Variable _ as v -> List.mem v vars
    | Application (f, lst) -> (List.mem f sym) && (List.for_all process_expr lst)
    | Sum lst -> List.for_all process_expr lst
    | Coeff (c,e) -> process_expr e
  in
  let rec process_pred formula = match formula with
    | And lst | Or lst -> List.for_all process_pred lst
    | Not p -> process_pred p
    | Eq (e1,e2) | Lt (e1,e2) | Leq (e1,e2) -> (process_expr e1) && (process_expr e2)
    | Atom _ -> false
    | _ -> true
  in
   process_pred formula

(** Does formula contains only expression contained in set expr ?*)
let only_expr expr formula =
  let rec process_pred formula = match formula with
    | And lst | Or lst -> List.for_all process_pred lst
    | Not p -> process_pred p
    | Eq (e1,e2) | Lt (e1,e2) | Leq (e1,e2) -> (List.mem e1 expr) && (List.mem e2 expr)
    | _ -> false
  in
   process_pred formula

(** transforms predicate 'origin' into '_new'.
 * @param origin the predicate to replace.
 * @param _new the replacement.
 * @param formula apply the transformation of this.
 *)
let alpha_convert_pred origin _new formula =
  let rec process f = match f with
    | f when f = origin -> _new
    | And lst -> And (List.map process lst)
    | Or lst -> Or (List.map process lst)
    | Not p -> Not (process p)
    | e -> e
  in
    process formula


(** Splits a formula into separate theories.
 *  This methods works only for the conjunctive fragment.
 * @return a formula in LI, in UIF, and a set of shared variable:
 *      list of uif_preds (without And),
 *      list of li_preds  (without And),
 *      list of shared variables,
 *      association list for the new variables: variable -> expression
 *)
let split_formula_LI_UIF pred =
  let counter = ref 0 in
  let expr_to_var = Hashtbl.create 13 in
  let defs = ref [] in
  let assoc = ref [] in
  (* allocate a new var if needed and the new definition*)
  let get_fresh_var expr = 
    try Hashtbl.find expr_to_var expr
    with Not_found ->
      begin
        counter := 1 + !counter;
        let v = Variable ("fresh_split_var"^(string_of_int !counter)) in
          Hashtbl.add expr_to_var expr v;
          defs := (order_eq (Eq(expr, v)))::!defs;
          assoc := (v,expr)::!assoc;
          v
      end
  in
  let rec process_e_li expr = match expr with
    | Constant _ as c -> c
    | Variable _ as v -> v
    | Application (sym, lst) -> (*UIF*)
      begin
        let uif_pure = Application (sym, List.map process_e_uif lst) in
          get_fresh_var uif_pure
      end
    | Sum lst -> Sum (List.map process_e_li lst)
    | Coeff (c,e) -> Coeff(c, process_e_li e)
  and process_e_uif expr = match expr with
    | Constant _ as c -> (*LI*) get_fresh_var c
    | Variable _ as v -> v
    | Application (sym, lst) -> Application(sym, List.map process_e_uif lst)
    | Sum lst -> (*LI*)
      begin
        let li_pure = Sum (List.map process_e_li lst) in
          get_fresh_var li_pure
      end
    | Coeff (c,e) -> (*LI*)
      begin
        let li_pure = Coeff (c, process_e_li e) in
          get_fresh_var li_pure
      end
  in
  let rec process_p pred = match pred with
    | And lst -> And (List.map process_p lst)
    | Not (Eq (e1,e2)) -> Not (Eq(process_e_uif e1, process_e_uif e2))(*UIF*)
    (*both side should have the same theory*)
    | Eq (e1,e2) ->
      begin
        let li = order_eq (Eq(process_e_li e1, process_e_li e2)) in
        let uif = order_eq (Eq(process_e_uif e1, process_e_uif e2)) in
          if li <> uif then defs := li::!defs;
          uif
      end
    | Lt (e1,e2) -> Lt(process_e_li e1, process_e_li e2)(*LI*)
    | Leq (e1,e2) -> Leq(process_e_li e1, process_e_li e2)(*LI*)
    | Atom _ -> failwith "separating theories: found Atom"
    | True -> (*True*) failwith "separating theories: found True"
    | False -> (*False*) failwith "separating theories: found False"
    | Or lst -> (*Or (List.map process_p lst)*) failwith "separating theories: found Or"
    | Not p -> failwith "separating theories: expect formula in NNF (Not)"
  in
  let keep_li pred = match pred with
    | And lst -> failwith "separating theories: found And"
    | Not (Eq _) -> false
    | Eq (e1,e2) ->(is_expr_LI e1) && (is_expr_LI e2)
    | Lt _ -> true
    | Leq _ -> true
    | Atom _ -> failwith "separating theories: found Atom"
    | True -> (*True*) failwith "separating theories: found True"
    | False -> (*False*) failwith "separating theories: found False"
    | Or lst -> (*Or (List.find query_fct lst)*) failwith "separating theories: found Or"
    | Not p -> failwith "separating theories: expect formula in NNF (Not)"
  in
  let keep_uif pred = match pred with
    | And lst -> failwith "separating theories: found And"
    | Not (Eq _) -> true
    | Eq (e1,e2) -> (is_expr_UIF e1) && (is_expr_UIF e2)
    | Lt _ -> false
    | Leq _ -> false
    | Atom _ -> failwith "separating theories: found Atom"
    | True -> (*True*) failwith "separating theories: found True"
    | False -> (*False*) failwith "separating theories: found False"
    | Or lst -> (*Or (List.find query_fct lst)*) failwith "separating theories: found Or"
    | Not p -> failwith "separating theories: expect formula in NNF (Not)"
  in
  (*Begin Here*)
  let p_lst = OrdSet.list_to_ordSet (match (process_p pred) with
    | And lst -> lst @ !defs
    | e -> e::!defs)
  in
  match (List.exists has_LI_only p_lst, List.exists has_UIF_only p_lst) with
  | (true, true) ->
    begin
      let uif_formula = List.filter keep_uif p_lst in
      let li_formula = List.filter keep_li p_lst in
      let var_uif = get_var (And uif_formula) in
      let var_li = get_var (And li_formula) in
      let shared_var = OrdSet.intersection var_uif var_li in
        (uif_formula, li_formula, shared_var, !assoc)
    end
  | (true, false) ->
    begin
      let lst = match pred with 
        | And lst -> lst
        | el -> [el] (*so few checks because process_pred already did them*)
      in
        ([], lst, [], [])
    end
  | (false, true) ->
    begin
      let lst = match pred with 
        | And lst -> lst
        | el -> [el] (*so few checks because process_pred already did them*)
      in
        (lst, [], [], [])
    end
  | (false, false) -> (*UIF arbirary choice*)
    begin
      let lst = match pred with 
        | And lst -> lst
        | el -> [el] (*so few checks because process_pred already did them*)
      in
        (lst, [], [], [])
    end

let counter_equisat = ref 0
(**return an equisatisfiable formula in CNF
 * and two hashtables for atoms <-> subterms.
 * Assumes NNF.
 * (TODO let leaves ...)
 *)
let equisatisfiable pred =
  let dico = Hashtbl.create 23 in
  let pred_to_atom = Hashtbl.create 23 in
  let get_rep p =
    try Hashtbl.find pred_to_atom p
    with Not_found ->
      begin
        counter_equisat := 1 + !counter_equisat;
        let atom = Atom (Internal !counter_equisat) in
          Hashtbl.replace dico atom p;
          Hashtbl.replace pred_to_atom p atom;
          atom
      end
  in
  let rep pred = match pred with
    | True -> True
    | False -> False
    | And _ as an -> get_rep an
    | Or _ as o -> get_rep o
    | Not _ as n -> n
    | Eq _ as eq -> eq
    | Lt _ as lt -> lt
    | Leq (e1,e2) -> (Not (Lt (e2, e1)))
    | Atom _ as a -> a
  in
  let enc pred = match pred with
    | False | True | Eq _ | Lt _ | Atom _ | Leq _ | Not _ -> True
    | And lst as pp ->
      begin
        let p = rep pp in
        let repr = List.map rep lst in
        let one_false = List.map (fun x -> Or [Not p; x]) repr in
        let neg =  List.map (fun x -> Not x) repr in
          And ((Or (p::neg))::one_false)
      end
    | Or lst as pp ->
      begin
        let p = rep pp in
        let repr = List.map rep lst in
        let one_true = List.map (fun x -> Or [Not x; p]) repr in
          And ((Or ((Not p)::repr))::one_true)
      end
  in
    let subterm = get_subterm_nnf pred in
      (dico, pred_to_atom, normalize_only (And ((rep pred)::(List.map enc subterm))))

(** Equisatisfiable CNF conversiont designed to work on fomula close to CNF.
  * Converts only the non-CNF parts.
  * Assumes the formula was simplified and in NNF. *)
let better_equisatisfiable pred =
  let dico = Hashtbl.create 23 in
  let pred_to_atom = Hashtbl.create 23 in
  let get_rep p =
    try Hashtbl.find pred_to_atom p
    with Not_found ->
      begin
        counter_equisat := 1 + !counter_equisat;
        let atom = Atom (Internal !counter_equisat) in
          Hashtbl.replace dico atom p;
          Hashtbl.replace pred_to_atom p atom;
          atom
      end
  in
  let defs = ref [] in
  let encoded = ref PredSet.empty in
  let rec rep pred = match pred with
    | And _ as an ->
      begin
        let repAnd = get_rep an in
          defs := (enc repAnd an) @ !defs;
          repAnd
      end
    | Or _ as o ->
      begin
        let repOr = get_rep o in
          defs := (enc repOr o) @ !defs;
          repOr
      end
    | Leq (e1,e2) -> (Not (Lt (e2, e1)))
    | ok -> ok
  and enc p pred = match pred with
    | And lst as pp when not (PredSet.mem pp !encoded) ->
      begin
        encoded := PredSet.add pp !encoded;
        let repr = List.map rep lst in
        let one_false = List.map (fun x -> Or [Not p; x]) repr in
        let neg =  List.map (fun x -> Not x) repr in
          (Or (p::neg)) :: one_false
      end
    | Or lst as pp when not (PredSet.mem pp !encoded) ->
      begin
        encoded := PredSet.add pp !encoded;
        let repr = List.map rep lst in
        let one_true = List.map (fun x -> Or [Not x; p]) repr in
          (Or ((Not p)::repr)) :: one_true
      end
    | _ -> []
  in
  let big_cunjunct = 
    (* check that the fisrt stage is a big conjunction. *)
    match pred with
    | And lst ->
      begin
        let clausify pred =
          (* clausify only when needed *)
          match pred with
          | Or lst -> Or (List.map rep lst)
          | atom when is_atomic atom -> Or [atom]
          | what -> failwith ("AstUtil, better_equisatisfiable: ??? " ^ (print_pred what))
        in
          And (!defs @ (List.map clausify lst))
      end
    (* trivial encoding *)
    | x when is_atomic x -> And [Or [x]]
    (* otherwise revert to normal CNF encoding. *)
    | otherwise -> 
      begin
        let (dico', pred_to_atom', formula) = equisatisfiable otherwise in
          Hashtbl.iter (fun k v -> Hashtbl.replace dico k v) dico';
          Hashtbl.iter (fun k v -> Hashtbl.replace pred_to_atom k v) pred_to_atom';
          formula
      end 
  in
    (dico, pred_to_atom, normalize_only (remove_lit_clash big_cunjunct))
(** Replaces the atoms by the part they represent.*)
let unabstract_equisat dico formula =
  let rec process formula = match formula with
    | And lst -> And (List.map process lst)
    | Or lst -> Or (List.map process lst)
    | Not p -> Not (process p)
    | Eq _ as eq -> eq
    | Lt _ as lt ->  lt
    | Leq(e1,e2) -> (Not (Lt(e2,e1)))
    | Atom (External _) as a -> a
    | Atom (Internal _) as a -> process (Hashtbl.find dico a)
    | True -> True
    | False -> False
  in
    normalize_only (process formula)

(** Formula is an equisatisfiable formula (assignment returned by the satsolver),
 * it removes the atoms, keeps only the theory literals.
 * Assumes NNF.
 *)
let remove_equisat_atoms formula =
  let rec process formula = match formula with
    | Atom (Internal _)  -> True
    | Not (Atom (Internal _)) -> True
    | Atom (External _) as a -> a
    | And lst -> And (List.map process lst)
    | Or lst -> Or (List.map process lst)
    | Not _ as np -> np
    | Eq _ as eq -> eq
    | Lt _ as lt ->  lt
    | Leq(e1,e2) -> (Not (Lt(e2,e1)))
    | True -> True
    | False -> False
  in
    normalize_only (process formula)

(** Returns the 'external' atoms (with negation).
 *  Assume NNF.
 *)
let get_external_atoms formula =
  let rec process formula = match formula with
    | Atom (External _) as a -> [a]
    | Not (Atom (External _)) as na -> [na]
    | And lst | Or lst -> OrdSet.list_to_ordSet (List.flatten (List.map process lst))
    | Not _ | Eq _ | Lt _ | Leq _ | Atom (Internal _)-> []
    | True  | False -> []
  in
    process formula

(** Formula is an assignment returned by the satsolver,
 * it removes the atoms, keeps only the theory literals.
 * Assumes NNF.
 *)
let remove_atoms formula =
  let rec process formula = match formula with
    | Atom _  -> True
    | Not (Atom _)  -> True
    | And lst -> And (List.map process lst)
    | Or lst -> Or (List.map process lst)
    | Not _ as np -> np
    | Eq _ as eq -> eq
    | Lt _ as lt ->  lt
    | Leq(e1,e2) -> (Not (Lt(e2,e1)))
    | True -> True
    | False -> False
  in
    normalize_only (process formula)

(** Simple trick to replace x > y by x>= y+1.
 * Helps in many integer problems,
 * but is not sound, neither complete.
 * When having only integers value as constant,
 * this is only incomplete.
 *)
let rec integer_heuristic p =
  let p' = 
    match p with 
    | True | False -> p
    | And plist -> And (List.map integer_heuristic plist)
    | Or plist-> Or (List.map integer_heuristic plist)
    | Not np -> 
      let p' = push_negation false p in
        if p = p' then p else integer_heuristic p'
    | Lt (e1, e2) -> Leq(Sum [Constant 1.0; e1], e2)
    | Eq _ | Leq _ | Atom _ -> p 
  in
    p'


(**********)
let print_hol_cst flt =
  let (f,i) = modf flt in
    if f = 0.0 then
      begin
        let i = (int_of_float i) in
        let prefix = if i < 0 then "-- &" else "&" in
          prefix ^ (string_of_int (abs i))
      end
    else failwith "print_hol_cst"

let rec print_hol_expr expr = match expr with
  | Constant cst -> print_hol_cst cst
  | Variable v -> v
  | Application (sym, lst) -> sym ^ "(" ^ (Utils.string_list_cat ", " (List.map print_hol_expr lst)) ^")"
  | Sum lst ->  "(" ^ (Utils.string_list_cat " + " (List.map print_hol_expr lst)) ^")"
  | Coeff (co, expr) -> (print_hol_cst co) ^ " * " ^ (print_hol_expr expr)

let rec print_hol p =
  match p with
  | False -> "F"
  | True -> "T"
  | And lst -> "(" ^ (Utils.string_list_cat " /\\ " (List.map print_hol lst)) ^")"
  | Or lst -> "(" ^ (Utils.string_list_cat " \\/ " (List.map print_hol lst)) ^")"
  | Not p -> "( ~ " ^ print_hol p ^ ")"
  | Eq (e1,e2) -> "(" ^ (print_hol_expr e1) ^ " = " ^ (print_hol_expr e2) ^ ")"
  | Lt (e1,e2) -> "(" ^ (print_hol_expr e1) ^ " < " ^ (print_hol_expr e2) ^ ")"
  | Leq (e1,e2) -> "(" ^ (print_hol_expr e1) ^ " <= " ^ (print_hol_expr e2) ^ ")"
  | Atom (External str) -> str
  | Atom (Internal i) -> "atom"^(string_of_int i)

let print_hol_full var_type p =
  let variables = get_var p in
  let vars_del = String.concat " " (List.map (fun v -> (print_hol_expr v) ^ ":" ^ var_type) variables) in
  let atoms = get_atoms p in
  let atoms_decl = String.concat " " (List.map (fun v -> (print_hol v) ^ ":bool") atoms) in
  let prefix = "? "^ atoms_decl ^ " " ^ vars_del ^". " in
    "`" ^ prefix  ^ (print_hol p) ^ "`"
