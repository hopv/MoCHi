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

(** The part responsible for putting theory specific and partial interpolants together.
 * This file is mostly based on Yorsh et al.
 * "A Combination Method for Generating Interpolants" (CADE05)
 * and Rybalchenko et al. "Constraint Solving for Interpolation".
 *)
open   CsisatAst
open   CsisatAstUtil
(**/**)
module Global      = CsisatGlobal
module Message     = CsisatMessage
module Utils       = CsisatUtils
module OrdSet      = CsisatOrdSet
module SatLI       = CsisatSatLI
module SatPL       = CsisatSatPL
module ClpLI       = CsisatClpLI
module SatUIF      = CsisatSatUIF
module Dag         = CsisatDag
module NelsonOppen = CsisatNelsonOppen
module DpllProof   = CsisatDpllProof
(**/**)

type side_t = A | B | Mixed

let side_to_string s = match s with
  | A -> "A"
  | B -> "B"
  | Mixed -> "Mixed"

let splitN_unsat_cores terms_lst mixed =
  let terms = Array.of_list terms_lst in
  let parts = Array.make (Array.length terms) [] in
  let rec process x =
    Array.iteri
      (fun i term ->
        if OrdSet.mem x term then parts.(i) <- x::(parts.(i));
      ) terms
  in
    List.iter process mixed;
    Array.to_list parts

(* this should be used only when boolean contradicion are not important (i.e. sat solver took care of them)
 * The blocking clauses can intorduce equalities that are not part of A or B
 *)
let splitN_unsat_cores_set proposition_lst mixed =
  let props = Array.of_list proposition_lst in
  let parts = Array.make (Array.length props) [] in
  let rec process x =
    let assigned = ref false in
      (*new lit introduced by blocking clause, put it in the leftmost or rightmostpart*)
      Array.iteri
        (fun i term ->
          if not !assigned && PredSet.mem (proposition_of_lit x) term then 
            begin
              parts.(i) <- x::(parts.(i));
              assigned := true
            end
        ) props;
  in
    List.iter process mixed;
    Array.to_list parts

(** LA and EUF are equalities interpolating theories.
 *  Thus it is possible the mkae terms local if an equality is not AB-pure.
 * @param th theory that deduced the equality
 * @param side is a function that maps an expr to its side: A/B/Mixed
 * @param common_var variables common to A and B
 * @param common_sym fct symbols common to A and B
 * @param a_eq EUF cstr from A
 * @param a_li LA cstr from A
 * @param b_eq EUF cstr from B
 * @param b_li LA cstr from B
 * @param eq the equality to 'localize'
 *)
let make_deduc_local th side common_var common_sym a_eq a_li b_eq b_li eq =
  Message.print Message.Debug (lazy("common var are: "^(Utils.string_list_cat ", "(List.map print_expr common_var))));
  Message.print Message.Debug (lazy("common sym are: "^(Utils.string_list_cat ", " common_sym)));
  Message.print Message.Debug (lazy("for "^(print eq)));
  let make_eq_local_LA ea eb =
    let m = SatLI.find_common_expr (And (a_li @ b_li)) ea common_var common_sym in
      Message.print Message.Debug (lazy("middle term is: "^(print_expr m)));
      let eq_a = order_eq (Eq(ea,m)) in
      let eq_b = order_eq (Eq(eb,m)) in
        [(A, eq_a);(B, eq_b)]
  in
  let make_eq_local_EUF ea eb =
    let a_eq = List.filter (fun x -> match x with Eq _ -> true | _ -> false) a_eq in 
    let b_eq = List.filter (fun x -> match x with Eq _ -> true | _ -> false) b_eq in 
    let m = SatUIF.find_common_expr (And a_eq) (And b_eq) ea eb common_var common_sym in
      Message.print Message.Debug (lazy("middle term is: "^(print_expr m)));
      let eq_a = order_eq (Eq(ea,m)) in
      let eq_b = order_eq (Eq(eb,m)) in
        [(A, eq_a);(B, eq_b)]
  in
    match eq with
    | Eq (e1,e2) as eq ->
      begin
        match (side e1, side e2) with
        | (A,A) | (A,Mixed) | (Mixed,A) -> [(A, eq)]
        | (B,B) | (Mixed,B) | (B,Mixed) | (Mixed,Mixed) -> [(B, eq)]
        | (A,B) ->
          begin
            match th with
            | NelsonOppen.LI -> make_eq_local_LA e1 e2
            | NelsonOppen.UIF -> make_eq_local_EUF e1 e2
            | _ -> failwith "Interpolate, make_deduc_local: theory(1)"
          end
        | (B,A) ->
          begin
            match th with
            | NelsonOppen.LI -> make_eq_local_LA e2 e1
            | NelsonOppen.UIF -> make_eq_local_EUF e2 e1
            | _ -> failwith "Interpolate, make_deduc_local: theory(2)"
          end
      end
    | _ -> failwith "Interpolate, make_deduc_local: expected EQ"

(** buids a partial interpolant from an unsat formula with Nelson Oppen style deduced equalities
 * @param a the A formmula
 * @param a_prop is the set of terms present in A
 * @param b the B formmula
 * @param b_prop is the set of terms present in B
 * @param core is the unsat formula
 * @param theory is the theory that find the contradiction
 * @param eq_deduced is a list is deduced equalities (from first to last) with the theory that leads to the deduction
 *)
let partial_interpolant a a_prop b b_prop (core, theory, eq_deduced) =
  Message.print Message.Debug (lazy("processing core: "^(print core)));
  let core_lst = match core with
    | And lst -> lst
    | _ -> failwith "Interpolate, process_core: expected And"
  in
  let (a_part, b_part) = match splitN_unsat_cores_set [a_prop;b_prop] core_lst with 
    | x::y::[] -> (x,y)
    | _ -> failwith "Interpolate, process_core: error in splitN"
  in
  Message.print Message.Debug (lazy("A part: "^(print (And a_part))));
  Message.print Message.Debug (lazy("B part: "^(print (And b_part))));
  let oa_part = OrdSet.list_to_ordSet a_part in
  let ob_part = OrdSet.list_to_ordSet b_part in
  let (a_part, b_part) = (OrdSet.subtract oa_part ob_part, ob_part) in (*follows the projection def of CADE05-interpolants*)

  let a_vars = get_var (And a_part) in
  let b_vars = get_var (And b_part) in
  let common_var = OrdSet.intersection a_vars b_vars in
  let a_sym = get_fct_sym (And a_part) in
  let b_sym = get_fct_sym (And b_part) in
  let common_sym = OrdSet.intersection a_sym b_sym in
    Message.print Message.Debug (lazy("common var are: "^(Utils.string_list_cat ", "(List.map print_expr common_var))));
    Message.print Message.Debug (lazy("common sym are: "^(Utils.string_list_cat ", " common_sym)));

  let side expr =
    match (only_vars_and_symbols a_vars a_sym (Eq (expr, Constant 0.0)),
           only_vars_and_symbols b_vars b_sym (Eq (expr, Constant 0.0))) with
    | (true, true) -> Mixed
    | (true, false) -> A
    | (false, true) -> B
    | (false, false) -> failwith ("Interpolate: "^(print_expr expr)^" belongs to no side.")
  in

  let a_part_eq = ref (List.filter (fun x -> match x with | Leq _ | Lt _ -> false | _ -> true) a_part) in
  let a_part_li = ref (List.filter (fun x -> match x with | Not _ -> false | _ -> true) a_part) in
  let b_part_eq = ref (List.filter (fun x -> match x with | Leq _ | Lt _ -> false | _ -> true) b_part) in
  let b_part_li = ref (List.filter (fun x -> match x with | Not _ -> false | _ -> true) b_part) in

  (* partial interplants for  A /\ B /\ ¬eq |- false *)
  let process_deduction (th, eq) =
    Message.print Message.Debug (lazy("process deduction: "^(print eq)));
    match eq with
    | Eq (e1,e2) as eq ->
      begin
        let queries = make_deduc_local th side common_var common_sym !a_part_eq !a_part_li !b_part_eq !b_part_li eq in
        let compute_it (s, eq) =
          Message.print Message.Debug (lazy("compute_it for : "^(print eq)));
          match th with
          | NelsonOppen.LI ->
          (*| LA ->*)
          (* for LA one of the two side only is non-trivial *)
            begin
              let (e1,e2) = match eq with
                | Eq(e1,e2) -> (e1,e2)
                | _ -> failwith "Interpolate, compute_it: not Eq !?"
              in
                if s = A then
                  begin
                    let lst1 = ClpLI.interpolate_clp [And(Lt(e1,e2)::!a_part_li); And !b_part_li] in
                    let lst2 = ClpLI.interpolate_clp [And(Lt(e2,e1)::!a_part_li); And !b_part_li] in
                    let it =  simplify  (Or [List.hd lst1; List.hd lst2]) in
                      (A, it)
                  end
                else if s = B then
                  begin
                    let lst1 = ClpLI.interpolate_clp [And !a_part_li; And (Lt(e1,e2)::!b_part_li)] in
                    let lst2 = ClpLI.interpolate_clp [And !a_part_li; And (Lt(e2,e1)::!b_part_li)] in
                    let it =  simplify  (And [List.hd lst1; List.hd lst2]) in
                      (B, it)
                  end
                else
                  begin
                    assert(false)
                  end
            end
          | NelsonOppen.UIF ->
          (*| EUF ->*)
            begin
              if s = A then
                (A, Or (SatUIF.interpolate_euf true eq (And !a_part_eq) (And !b_part_eq)))
              else
                (B, And (SatUIF.interpolate_euf false eq (And !a_part_eq) (And !b_part_eq)))
            end
          | _ -> failwith "Interpolate, partial_interpolant: theory ??"
        in
        let new_it = List.map compute_it queries in
          Message.print Message.Debug (lazy("deduction its: "^(Utils.string_list_cat ", "(List.map (fun (x,y) -> (side_to_string x)^" "^(print y)) new_it))));
          List.iter2
            (fun (s, eq) (_s, it) -> match s with
              | A -> ( a_part_eq := eq::!a_part_eq; a_part_li := eq::!a_part_li )
              | B -> ( b_part_eq := eq::!b_part_eq; b_part_li := eq::!b_part_li )
              | Mixed ->
                begin
                  assert(Global.is_off_assert() || s=_s);
                  assert(Global.is_off_assert() || th = NelsonOppen.LI);
                  match (eq,it) with
                  | (Eq(ea,eb),Lt(e1,e2)) ->
                    let eqa = order_eq (Eq(ea,e1)) in
                      (a_part_eq := eqa::!a_part_eq; a_part_li := eqa::!a_part_li);
                    let eqb = order_eq (Eq(eb,e1)) in
                    ( b_part_eq := eqb::!b_part_eq; b_part_li := eqb::!b_part_li )
                  | _ -> failwith "Interpolate, partial_interpolant: about LI middle term"
                end)
            queries new_it;
          (th, new_it)
      end
    | err -> failwith ("Interpolate, partial_interpolant: deduction is not an equality -> "^(print err))
  in
  let its = List.map process_deduction eq_deduced in
  let final_it = match theory with
    | NelsonOppen.UIF (*EUF*) -> Dag.interpolate_eq (And !a_part_eq) (And !b_part_eq)
    | NelsonOppen.LI (*LA*) ->  List.hd (ClpLI.interpolate_clp [And !a_part_li; And !b_part_li])
    | NelsonOppen.BOOL -> 
      (*!! this happens when bypassing SAT solver !!->*)
      begin
        let a_term = get_subterm_nnf a in
        let b_term = get_subterm_nnf b in
        let (a_part, _) = match splitN_unsat_cores [a_term;b_term] core_lst with 
          | x::y::[] -> (x,y)
          | _ -> failwith "Interpolate, process_core: error in splitN"
        in
          match a_part with
          | [] -> True
          | x::[] -> x
          | x::y::[] -> False
          | _ -> failwith "Interpolate: direct contradiction with more than two elements !?!"
      end
    | _ -> failwith "Interpolate, partial_interpolant: theory ?!?"
  in
    (*recompose using the inductive definition*)
  let split_side lst =
    List.fold_left
      (fun (accA,accB,accMixed) (s,it) -> match s with
        | A -> (it::accA, accB, accMixed)
        | B -> (accA, it::accB, accMixed)
        | Mixed -> (accA, accB, it::accMixed)
      )
      ([],[], []) lst
  in
  let it = List.fold_right
      (fun (th,lst) it ->
        let (a_its, b_its, mixed_its) = split_side lst in
          if th = NelsonOppen.UIF then
            begin
              assert(Global.is_off_assert() || mixed_its = []);
              And ((Or (it::a_its))::b_its)
            end
          else
            begin
              assert(Global.is_off_assert() || th=NelsonOppen.LI);
              match (a_its, b_its, mixed_its) with
              | (lst,[],[]) -> Or (it::lst)
              | ([],lst,[]) -> And (it::lst)
              | ([],[],[Lt(t_m, t_p)]) -> assert(false) (*Or [And [it;order_eq (Eq(t_p,t_m))]; Lt(t_m,t_p)]*)
              | (a,b,[]) ->
                begin
                  (*Mixed queries*)
                  (*TODO DZ: I'm not very comfortable with this part.
                   * It should be re-engineered.
                   *)
                  let relevant = List.filter(fun x -> match x with Lt(e1,e2) -> true | _ -> false) a in
                    Message.print Message.Debug (lazy("relevant is: "^(print (And relevant))));
                    match relevant with
                    | Lt(e1,e2)::_ -> Or [(And [it;order_eq (Eq(e1,e2))]); Lt(e1,e2)]
                    | [] -> And ((Or (it::a))::b)
                    | _ -> failwith "Interpolate, partial_interpolant: unreachable part!!"
                end
              | (a,b,c) ->
                failwith ("Interpolate, partial_interpolant: LA interpolants A: "
                  ^(Utils.string_list_cat ", "(List.map print a))
                  ^" B: "^(Utils.string_list_cat ", "(List.map print b))
                  ^" M: "^(Utils.string_list_cat ", "(List.map print c)))
            end
      )
      its final_it 
  in 
    simplify it

(****************************)
(***** experimental code ****)
(*TODO finish and test*)
(*
let partial_interpolant_lst lst_prop (core, theory, eq_deduced) =
  Message.print Message.Debug (lazy("processing core: "^(print core)));
  let core_lst = match core with
    | And lst -> lst
    | _ -> failwith "Interpolate, process_core: expected And"
  in
  let lst_part = splitN_unsat_cores_set lst_prop core_lst in
  
  let make_common lst =
    let a_side =
      let (lst,_) = List.fold_left
        (fun (res,acc) x -> let new_set = OrdSet.union x acc in (new_set::res, new_set) )
        ([], []) lst
      in
        List.rev (List.tl lst)
    in
    let b_side =
      let (lst,_) = List.fold_right
        (fun x (res,acc) -> let new_set = OrdSet.union x acc in (new_set::res, new_set) )
        lst ([], [])
      in
        List.tl lst
    in
      List.map2 (fun a b -> OrdSet.intersection a b) a_side b_side
  in
  let lst_vars = List.map (fun x -> get_var (And x)) lst_part in
  let common_var = make_common lst_vars in
  let lst_sym = List.map (fun x -> get_fct_sym (And x)) lst_part in
  let common_sym = make_common lst_sym in

  (* returns a pairs i,j where i is the leftmost part expr is in, and j the rightmost *)
  let side expr =
    let _min = ref 100000 in
    let _max = ref (-1) in
    let _ = List.fold_left2
        (fun i vars syms ->
          if only_vars_and_symbols vars syms (Eq (expr, Constant 0.0)) then
            begin
              _min := min !_min i;
              _max := max !_max i;
            end;
          i + 1
        ) 0 lst_vars lst_sym
    in
      assert(Global.is_off_assert() || !_min >= 0);
      assert(Global.is_off_assert() || !_max >= 0);
      assert(Global.is_off_assert() || !_max >= !_min);
      (!_min,!_max)
  in

  let part_eq = Array.of_list (List.map (fun part -> List.filter (fun x -> match x with | Leq _ | Lt _ -> false | _ -> true) part) lst_part) in
  let part_li = Array.of_list (List.map (fun part -> List.filter (fun x -> match x with | Not _ -> false | _ -> true) part) lst_part) in

  (*TODO*)
  (* partial interplants for  A /\ B /\ ¬eq |- false *)
  let process_deduction (th, eq) =
    Message.print Message.Debug (lazy("process deduction: "^(print eq)));
    match eq with
    | Eq (e1,e2) as eq ->
      begin
        let queries = make_deduc_local_lst th side common_var common_sym part_eq part_li eq in
        let compute_it (s, eq) =
          Message.print Message.Debug (lazy("compute_it for : "^(print eq)));
          match th with
          | NelsonOppen.LI ->
          (*| LA ->*)
          (* for LA one of the two side only is non-trivial *)
            begin
              let (e1,e2) = match eq with
                | Eq(e1,e2) -> (e1,e2)
                | _ -> failwith "Interpolate, compute_it: not Eq !?"
              in
                if s = A then
                  begin
                    let lst1 = ClpLI.interpolate_clp [And(Lt(e1,e2)::!a_part_li); And !b_part_li] in
                    let lst2 = ClpLI.interpolate_clp [And(Lt(e2,e1)::!a_part_li); And !b_part_li] in
                    let it =  simplify  (Or [List.hd lst1; List.hd lst2]) in
                      (A, it)
                  end
                else if s = B then
                  begin
                    let lst1 = ClpLI.interpolate_clp [And !a_part_li; And (Lt(e1,e2)::!b_part_li)] in
                    let lst2 = ClpLI.interpolate_clp [And !a_part_li; And (Lt(e2,e1)::!b_part_li)] in
                    let it =  simplify  (And [List.hd lst1; List.hd lst2]) in
                      (B, it)
                  end
                else
                  begin
                    assert(false)
                  end
            end
          | NelsonOppen.UIF ->
          (*| EUF ->*)
            begin
              if s = A then
                (A, Or (SatUIF.interpolate_euf true eq (And !a_part_eq) (And !b_part_eq)))
              else
                (B, And (SatUIF.interpolate_euf false eq (And !a_part_eq) (And !b_part_eq)))
            end
          | _ -> failwith "Interpolate, partial_interpolant: theory ??"
        in
        let new_it = List.map compute_it queries in
          Message.print Message.Debug (lazy("deduction its: "^(Utils.string_list_cat ", "(List.map (fun (x,y) -> (side_to_string x)^" "^(print y)) new_it))));
          List.iter2
            (fun (s, eq) (_s, it) -> match s with
              | A -> ( a_part_eq := eq::!a_part_eq; a_part_li := eq::!a_part_li )
              | B -> ( b_part_eq := eq::!b_part_eq; b_part_li := eq::!b_part_li )
              | Mixed ->
                begin
                  assert(Global.is_off_assert() || s=_s);
                  assert(Global.is_off_assert() || th = NelsonOppen.LI);
                  match (eq,it) with
                  | (Eq(ea,eb),Lt(e1,e2)) ->
                    let eqa = order_eq (Eq(ea,e1)) in
                      (a_part_eq := eqa::!a_part_eq; a_part_li := eqa::!a_part_li);
                    let eqb = order_eq (Eq(eb,e1)) in
                    ( b_part_eq := eqb::!b_part_eq; b_part_li := eqb::!b_part_li )
                  | _ -> failwith "Interpolate, partial_interpolant: about LI middle term"
                end)
            queries new_it;
          (th, new_it)
      end
    | err -> failwith ("Interpolate, partial_interpolant: deduction is not an equality -> "^(print err))
  in
  let its = List.map process_deduction eq_deduced in
  let final_it = match theory with
    | NelsonOppen.UIF (*EUF*) -> Dag.interpolate_eq common_var common_sym (to_list part_eq)
    | NelsonOppen.LI (*LA*) ->  ClpLI.interpolate_clp (Array.to_list part_li)
    | _ -> failwith "Interpolate, partial_interpolant: theory ?!?"
  in
    (*recompose using the inductive definition*)
  let split_side lst =
    List.fold_left
      (fun (accA,accB,accMixed) (s,it) -> match s with
        | A -> (it::accA, accB, accMixed)
        | B -> (accA, it::accB, accMixed)
        | Mixed -> (accA, accB, it::accMixed)
      )
      ([],[], []) lst
  in
  let it = List.fold_right
      (fun (th,lst) it ->
        let (a_its, b_its, mixed_its) = split_side lst in
          if th = NelsonOppen.UIF then
            begin
              assert(Global.is_off_assert() || mixed_its = []);
              And ((Or (it::a_its))::b_its)
            end
          else
            begin
              assert(Global.is_off_assert() || th=NelsonOppen.LI);
              match (a_its, b_its, mixed_its) with
              | (lst,[],[]) -> Or (it::lst)
              | ([],lst,[]) -> And (it::lst)
              | ([],[],[Lt(t_m, t_p)]) -> assert(false) (*Or [And [it;order_eq (Eq(t_p,t_m))]; Lt(t_m,t_p)]*)
              | (a,b,[]) ->
                begin
                  (*Mixed queries*)
                  let relevant = List.filter(fun x -> match x with Lt(e1,e2) -> true | _ -> false) a in
                    match relevant with
                    | Lt(e1,e2)::_ -> Or [(And [it;order_eq (Eq(e1,e2))]); Lt(e1,e2)]
                    | [] -> it
                    | _ -> failwith "Interpolate, partial_interpolant: unreachable part!!"
                end
              | (a,b,c) ->
                failwith ("Interpolate, partial_interpolant: LA interpolants A: "
                  ^(Utils.string_list_cat ", "(List.map print a))
                  ^" B: "^(Utils.string_list_cat ", "(List.map print b))
                  ^" M: "^(Utils.string_list_cat ", "(List.map print c)))
            end
      )
      its final_it 
  in 
    simplify it
*)

(*end of tree: what kind of clause*)
type eot_t = ACl (*A clause*)
           | BCl (*B clause*)
           | NCl of int (*# clause for path interpolation*)
           | ThCl of predicate * NelsonOppen.contradiction_in * ((NelsonOppen.contradiction_in * predicate) list)
           | NotCl (*Not a clause*)

(** build the interpolant by recurssing in the proof
 * @param a the A formula
 * @param b the B formula
 * @param proof a resolution proof, see dpllProof.ml
 * @param cores_with_info list of unsat cores + theory + eq deductions
 *)
let recurse_in_proof a b proof cores_with_info =
  let clause_to_side = Hashtbl.create 1000 in
  let add_disj_to_side disj side =
    let lits = 
      match disj with
      | Or lst -> OrdSet.list_to_ordSet lst
      | err -> failwith ("Interpolate, clause_to_side: core is not a disj (1) "^(print err))
    in
      Hashtbl.add clause_to_side lits side
  in
  let add_core (core,th,info) =
    let lits = 
      match SatPL.reverse core with
      | Or lst -> OrdSet.list_to_ordSet lst
      | err -> failwith ("Interpolate, clause_to_side: core is not a disj (2) "^(print err))
    in
      Hashtbl.add clause_to_side lits (ThCl (core,th,info))
  in
  let lookup_cl cl =
    try
      Hashtbl.find clause_to_side (predSet_to_ordSet cl)
    with Not_found -> NotCl
  in
  let _ = match a with
    | And lst -> List.iter (fun x -> add_disj_to_side x ACl) lst
    | _ -> failwith "Interpolate, build_trie: not in CNF (1)"
  in
  let _ = match b with
    | And lst -> List.iter (fun x -> add_disj_to_side x BCl) lst
    | _ -> failwith "Interpolate, build_trie: not in CNF (2)"
  in
  let _ = List.iter (fun x -> add_core x) cores_with_info in

  (*cache to replicate subproof*)
  let cache = Hashtbl.create 100 in

  let a_prop = get_proposition_set a in
  let b_prop = get_proposition_set b in
  let rec recurse prf = match prf with
    | DpllProof.RPNode (pivot, left, right, result) ->
      if Hashtbl.mem cache result then Hashtbl.find cache result
      else
        begin
          let left_it = recurse left in
          let right_it = recurse right in
          let it = match (PredSet.mem pivot a_prop, PredSet.mem pivot b_prop) with
            | (true, true) ->
              if PredSet.mem pivot (DpllProof.get_result left) then
                begin
                  assert (Global.is_off_assert() || PredSet.mem (contra pivot) (DpllProof.get_result right));
                  And [Or [pivot ;left_it]; Or [Not pivot ;right_it]]
                end
              else
                begin
                  assert (Global.is_off_assert() || PredSet.mem (contra pivot) (DpllProof.get_result left));
                  assert (Global.is_off_assert() || PredSet.mem pivot (DpllProof.get_result right));
                  And [Or [Not pivot ;left_it]; Or [pivot ;right_it]]
                end
            | (true, false) -> Or [left_it; right_it]
            | (false, true) -> And [left_it; right_it]
            | (false, false) -> failwith "Interpolate, recurse_in_proof: pivot does not belong to any side"
          in
            Hashtbl.add cache result it;
            it
        end
    | DpllProof.RPLeaf clause ->
      begin
        Message.print Message.Debug (lazy("proof leaf: "^(DpllProof.string_of_clause_t clause)));
        match lookup_cl clause with
        | ACl -> False
        | BCl -> True
        | NCl _ -> failwith "Interpolate, recurse_in_proof: NCl when not using path interpolation !!!"
        | ThCl (c,t,i) -> partial_interpolant a a_prop b b_prop (c,t,i)
        | NotCl -> failwith "Interpolate, recurse_in_proof: leaf of proof is not a clause !!!"
      end
  in
    recurse proof

let lazy_cnf formula =
  let (atom_to_pred, pred_to_atom, f) =
    (*if is already in cnf ...*)
    if is_cnf formula then
      begin
        Message.print Message.Debug (lazy("already in CNF"));
        (Hashtbl.create 0, Hashtbl.create 0, cnf formula)
      end
    else 
      begin
        Message.print Message.Debug (lazy("not CNF, using an equisatisfiable"));
        better_equisatisfiable formula
      end
  in
    (atom_to_pred, pred_to_atom, f)


let interpolate_with_proof a b =
  let (_,_,a) = lazy_cnf (simplify a) in
  let (_,_,b) = lazy_cnf (simplify b) in
  let a = normalize_only (remove_lit_clash a) in
  let b = normalize_only (remove_lit_clash b) in
  let a_cnf = cnf a in
  let b_cnf = cnf b in
    match (a,b) with
    | (True,_) ->
      begin
        if not (SatPL.is_sat b) then True
        else raise (SAT_FORMULA (remove_equisat_atoms b))
      end
    | (_,False) -> True
    | (False,_) -> False
    | (_,True) ->
      begin
        if not (SatPL.is_sat a) then False
        else raise (SAT_FORMULA (remove_equisat_atoms a))
      end
    | _->
      begin
        let it =
          if is_conj_only a && is_conj_only b then
            begin
              (*when conj only, bypass the get_unsat_core*)
              Message.print Message.Debug (lazy "Interpolate: formula is conj only");
              let core_with_info =
                NelsonOppen.unsat_LIUIF (normalize_only (And [a; b]))
              in
                let a_prop = get_proposition_set a in
                let b_prop = get_proposition_set b in
                  partial_interpolant a a_prop b b_prop core_with_info
            end
          else
            begin
              let ab = normalize_only (And [a_cnf; b_cnf]) in
                Message.print Message.Debug (lazy "Interpolate: using sat solver and proof");
              let (cores_with_info, proof) = 
                SatPL.unsat_cores_with_proof ab
              in
                recurse_in_proof a_cnf b_cnf proof cores_with_info
            end
        in
          (*as the introduced atoms are local to each side,
            they should not apprears in the interpolant*)
          simplify it
      end

let interpolate_with_one_proof lst =
  let lst = List.map (fun x -> let (_,_,f) = lazy_cnf (simplify x) in f) lst in
  let norms = List.map (fun x -> normalize_only (remove_lit_clash x)) lst in
  let all = normalize_only (And norms) in

  let rec mk_queries acc_q acc_a lst = match lst with
    | [x] -> List.rev acc_q
    | [] -> failwith "Interpolate: building queries"
    | x::xs ->
      begin
        let acc_a = normalize_only (And [x;acc_a]) in
        let b =  normalize_only (And xs) in
          mk_queries ((acc_a,b)::acc_q) acc_a xs
      end
  in
  let queries = mk_queries [] True norms in
    if all == False then
      begin
        (*find the fist occurence of false*)
        let already = ref false in
        let scan =
          List.fold_left (fun acc x ->
            if !already then False::acc
            else if x = False then
              begin
                already := true;
                False::acc
              end
            else True::acc)
          [] norms
        in
        let scan = List.rev (List.tl scan) in
          assert(Global.is_off_assert() || List.exists (fun x -> x == False) scan);
          scan
      end
    else if is_conj_only all then
      begin
        Message.print Message.Debug (lazy "Interpolate: formula is conj only");
        let core_with_info =
          NelsonOppen.unsat_LIUIF (normalize_only all)
        in
          List.map (fun (a,b) ->
              let a_prop = get_proposition_set a in
              let b_prop = get_proposition_set b in
                partial_interpolant a a_prop b b_prop core_with_info
              (* build_interpolant a b [core_with_info] *)
            ) queries
      end
    else
      begin
        let cnfs = List.map cnf norms in
        let all = normalize_only (And cnfs) in
          Message.print Message.Debug (lazy "Interpolate: using sat solver and proof");
        let (cores_with_info, proof) = 
          SatPL.unsat_cores_with_proof all
        in
          List.map ( fun (a,b) ->
            let it = recurse_in_proof (cnf a) (cnf b) proof cores_with_info in
              simplify it
            ) queries
      end

(*******************)
(*experimental code*)
(*TODO finish and test*)
(*
let recurse_in_proof_lst lst proof cores_with_info =
  let clause_to_side = Hashtbl.create 1000 in
  let add_disj_to_side disj side =
    let lits = 
      match disj with
      | Or lst -> OrdSet.list_to_ordSet lst
      | err -> failwith ("Interpolate, clause_to_side: core is not a disj (1) "^(print err))
    in
      Hashtbl.add clause_to_side lits side
  in
  let add_core (core,th,info) =
    let lits = 
      match SatPL.reverse core with
      | Or lst -> OrdSet.list_to_ordSet lst
      | err -> failwith ("Interpolate, clause_to_side: core is not a disj (2) "^(print err))
    in
      Hashtbl.add clause_to_side lits (ThCl (core,th,info))
  in
  let lookup_cl cl =
    try
      Hashtbl.find clause_to_side (cl#literals)
    with Not_found -> NotCl
  in
  let _ = List.fold_left
    (fun i x ->
      let _ = match x with
        | And lst -> List.iter (fun x -> add_disj_to_side x (NCl i)) lst
        | _ -> failwith "Interpolate, build_trie: not in CNF (1)"
      in
        i+1)
    0 lst
  in
  let _ = List.iter (fun x -> add_core x) cores_with_info in

  (*cache to replicate subproof*)
  let cache = Hashtbl.create 100 in

  (*list of pairs each element correspond to a possible cut in the input*)
  let lst_prop = List.map get_proposition_set lst in
  (*TODO assert length = |lst_prop| -1*)
  let ab_lst_prop =
    let a_side =
      let (lst,_) = List.fold_left
        (fun (res,acc) x -> let new_set = PredSet.union x acc in (new_set::res, new_set) )
        ([], PredSet.empty) lst_prop
      in
        List.rev (List.tl lst)
    in
    let b_side =
      let (lst,_) = List.fold_right
        (fun x (res,acc) -> let new_set = PredSet.union x acc in (new_set::res, new_set) )
        lst_prop ([], PredSet.empty)
      in
        List.tl lst
    in
      List.map2 (fun x y -> (x,y)) a_side b_side
  in

  (*recursively build the interpolant from the proof*)
  let rec recurse prf = match prf with
    | DpllProof.RPNode (pivot, left, right, result) ->
      if Hashtbl.mem cache result then Hashtbl.find cache result
      else
        begin
          let left_it = recurse left in
          let right_it = recurse right in
          let rec build_it_lst acc lit rit prop = match (lit,rit,prop) with
            | (left_it::ls, right_it::rs, (a_prop,b_prop)::ps) ->
              begin
                let it =
                  match (PredSet.mem pivot a_prop, PredSet.mem pivot b_prop) with
                  | (true, true) ->
                      if (DpllProof.get_result left)#has pivot then
                        begin
                          assert (Global.is_off_assert() || (DpllProof.get_result right)#has_not pivot);
                          And [Or [pivot ;left_it]; Or [Not pivot ;right_it]]
                        end
                      else
                        begin
                          assert (Global.is_off_assert() || (DpllProof.get_result left)#has_not pivot);
                          assert (Global.is_off_assert() || (DpllProof.get_result right)#has pivot);
                          And [Or [Not pivot ;left_it]; Or [pivot ;right_it]]
                        end
                  | (true, false) -> Or [left_it; right_it]
                  | (false, true) -> And [left_it; right_it]
                  | (false, false) -> failwith "Interpolate, recurse_in_proof: pivot does not belong to any side"
                in
                  build_it_lst (it::acc) ls rs ps
              end
            | ([],[],[]) -> List.rev acc
            | _ -> failwith "Interpolate, interpolate_with_proof_lst: match error (1)"
          in
          let it = build_it_lst [] left_it right_it ab_lst_prop
          in
            Hashtbl.add cache result it;
            it
        end
    | DpllProof.RPLeaf clause ->
      begin
        match lookup_cl clause with
        | NCl i ->
          List.rev (snd (
            List.fold_left
              (fun (n, acc) _ ->
                if i <= n then (n+1, False::acc) else (n+1, True::acc))
              (0,[]) lst_prop))
        | ThCl (c,t,i) -> partial_interpolant_lst lst_prop (c,t,i)
        | NotCl -> failwith "Interpolate, recurse_in_proof: leaf of proof in not a clause !!!"
      end
  in
    recurse proof
*)


(*
let interpolate_with_proof_lst lst =
  let lst = List.map (fun x ->  cnf (simplify x)) lst in
  let lst = List.map (fun x -> normalize_only (remove_lit_clash x)) lst in
  (*TODO trivial cases *)
    begin
      if List.for_all is_conj_only lst then
        begin
          (*when conj only, bypass the get_unsat_core*)
          Message.print Message.Debug (lazy "Interpolate: formula is conj only");
          let core_with_info =
            NelsonOppen.unsat_LIUIF (normalize_only (And lst))
          in
            (*build_interpolant_lst lst [core_with_info]*)
            partial_interpolant_lst lst core_with_info
        end
      else
        begin
          let lst_cnf = List.map cnf lst in
          let whole = normalize_only (And lst_cnf) in
            Message.print Message.Debug (lazy "Interpolate: using sat solver and proof");
          let (cores_with_info, proof) = 
            SatPL.unsat_cores_with_proof whole
          in
          let its = recurse_in_proof_lst lst_cnf proof cores_with_info in
            List.map simplify its
        end
    end
*)


let interpolate_propositional_only a b =
  let (_,_,a) = lazy_cnf (simplify a) in
  let (_,_,b) = lazy_cnf (simplify b) in
  let a = normalize_only (remove_lit_clash a) in
  let b = normalize_only (remove_lit_clash b) in
  let a_cnf = cnf a in
  let b_cnf = cnf b in
    match (a,b) with
    | (True,_) ->
      begin
        if not (SatPL.is_pl_sat b) then True
        else raise (SAT_FORMULA b)
      end
    | (_,False) -> True
    | (False,_) -> False
    | (_,True) ->
      begin
        if not (SatPL.is_pl_sat a) then False
        else raise (SAT_FORMULA a)
      end
    | _->
      begin
        let it =
          let ab = normalize_only (And [a_cnf; b_cnf]) in
            Message.print Message.Debug (lazy "Interpolate: using sat solver and proof");
            let proof = SatPL.make_proof_with_solver ab [] in
              recurse_in_proof a_cnf b_cnf proof []
        in
          simplify it
      end


