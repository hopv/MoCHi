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

(** Bool+T *)

open   CsisatAst
open   CsisatDpllCore
(**/**)
module Global      = CsisatGlobal
module AstUtil     = CsisatAstUtil
module PredSet     = CsisatAstUtil.PredSet
module Utils       = CsisatUtils
module NelsonOppen = CsisatNelsonOppen
module DpllClause  = CsisatDpllClause
module DpllProof   = CsisatDpllProof
(**/**)

let solver = ref "csi_dpll"

let get_solver prf = match !solver with
  | "csi_dpll" -> new csi_dpll prf
  | _ -> failwith "SatPL: unknown SAT solver"

(*TODO*)
(**
 * assume NNF
 *)
let to_atoms formula =
  let dico = Hashtbl.create 23 in
  let pred_to_atom = Hashtbl.create 23 in
  let counter = ref 0 in
  let get_rep p =
    try Hashtbl.find pred_to_atom p
    with Not_found ->
      begin
        counter := 1 + !counter;
        let atom = Atom (Internal !counter) in
          Hashtbl.replace dico atom p;
          Hashtbl.replace pred_to_atom p atom;
          atom
      end
  in
  let rec process formula = match formula with
    | And lst -> And (List.map process lst)
    | Or lst -> Or (List.map process lst)
    | Not p -> Not (process p)
    | Eq _ as eq -> get_rep eq
    | Lt _ as lt -> get_rep lt
    | Leq(e1,e2) -> process (Not (Lt(e2,e1)))
    | Atom (External _) as a -> get_rep a
    | Atom _ as a -> a
    | _ -> failwith "TRUE or FALSE found"
  in
    (dico, pred_to_atom, process formula)


(*assume NNF*)
let rec abstract dico formula = match formula with
  | And lst -> And (List.map (abstract dico) lst)
  | Or lst -> Or (List.map (abstract dico) lst)
  | Not p -> Not (abstract dico p)
  | Eq _ as eq -> Hashtbl.find dico eq
  | Lt _ as lt -> Hashtbl.find dico lt
  | Leq(e1,e2) -> abstract dico (Not (Lt(e2,e1)))
  | Atom (External _) as a -> Hashtbl.find dico a
  | Atom _ as a -> a
  | _ -> failwith "TRUE or FALSE found"

(** returns only the 'leaves'*)
let unabstract_bool dico assign =
  let lst = Utils.map_filter (
    fun (atom, value) ->
      match Hashtbl.find dico atom with
      | And _ -> None
      | Or _ -> None
      | Not _ -> None
      | Eq _ as eq -> 
        if value then Some eq
        else Some (Not eq)
      | Lt (e1,e2) as lt -> 
        if value then Some lt
        else Some (Leq(e2,e1))
      | Leq _ -> failwith "LEQ found !!"
      | Atom (Internal _) -> failwith "internal Atom found !!"
      | Atom (External _) as a ->
        if value then Some a
        else Some (Not a)
      | _ -> failwith "TRUE or FALSE found"
    ) assign
  in
    And lst

(** Conjunction to blocking clause *)
let reverse formula = match formula with
  | And lst -> Or (List.map AstUtil.contra lst)
  | Or lst -> failwith ("satPL: reverse expect a conj, found"^(AstUtil.print (Or lst)))
  | e -> Or [AstUtil.contra e] (*abstract can return atoms*)

(** Is the propositional formula satisfiable ? *)
let is_pl_sat formula =
  let f =
    if AstUtil.is_cnf formula then formula
    else match AstUtil.better_equisatisfiable formula with
      | (_,_,f) -> f
  in
  let f = AstUtil.cnf (AstUtil.simplify f) in
  let solver = get_solver false in
    solver#init f;
    solver#solve

let check_trivial_case f = match f with
  | True -> raise SAT
  | False -> failwith "SatPL, check_trivial_case: False"
  | _ -> ()

let is_sat formula =
  Message.print Message.Debug (lazy("is_sat for"^(AstUtil.print formula)));
  match formula with
  | True -> true
  | False -> false
  | formula ->
    begin
      let solver = get_solver false in
      (*let (atom_to_pred, pred_to_atom, f) =*)
      let (_, _, f) =
        (*if is already in cnf ...*)
        if AstUtil.is_cnf formula then
          begin
            Message.print Message.Debug (lazy("already in CNF"));
            (Hashtbl.create 0, Hashtbl.create 0, AstUtil.cnf formula)
          end
        else 
          begin
            Message.print Message.Debug (lazy("not CNF, using an equisatisfiable"));
            AstUtil.better_equisatisfiable formula
          end
      in
      let f = AstUtil.cnf (AstUtil.simplify f) in (*TODO is needed ??*)
        Message.print Message.Debug (lazy("abstracted formula is "^(AstUtil.print f)));
        solver#init f;
        let rec test_and_refine () =
          if solver#solve then
            begin
              Message.print Message.Debug (lazy "found potentially SAT assign");
              let solution = solver#get_solution in
              let externals = AstUtil.get_external_atoms (And solution) in
              let assign = AstUtil.remove_atoms (And solution) in
              try
                (*TODO config can force a theory*)
                check_trivial_case assign;
                let unsat_core = NelsonOppen.unsat_core assign in
                  Message.print Message.Debug (lazy("unsat core is: "^(AstUtil.print unsat_core)));
                let clause = unsat_core in
                let contra = reverse clause in
                  solver#add_clause contra;
                  test_and_refine ()
              with SAT | SAT_FORMULA _ ->
                begin 
                  Message.print Message.Debug (lazy("assignment is SAT: "^(AstUtil.print (AstUtil.normalize_only (And [assign; And externals])))));
                  true
                end
            end
          else
            begin
              false
            end
        in
          test_and_refine ()
        end

let unsat_cores_with_proof formula =
  let solver = get_solver true in
  let cores = ref [] in
  let f = AstUtil.cnf (AstUtil.simplify formula) in
    Message.print Message.Debug (lazy("cnf formula is "^(AstUtil.print f)));
    solver#init f;
    while solver#solve do
        Message.print Message.Debug (lazy "found potentially SAT assign");
        let solution =  solver#get_solution in
        let externals = AstUtil.get_external_atoms (And solution) in
        let assign = AstUtil.remove_atoms (And solution) in
        try
          check_trivial_case assign;
          let (unsat_core, _, _) as core_with_info = NelsonOppen.unsat_core_with_info assign in
            Message.print Message.Debug (lazy("unsat core is: "^(AstUtil.print unsat_core)));
            cores := core_with_info::!cores;
            let contra = reverse unsat_core in
              solver#add_clause contra
        with SAT | SAT_FORMULA _ ->
          Message.print Message.Debug (lazy("failed: "^(AstUtil.print (AstUtil.normalize_only (And [assign; And externals])))));
          raise (SAT_FORMULA (AstUtil.normalize_only (And [assign; And externals])))
    done;
    Message.print Message.Debug (lazy "No potentially SAT assign");
    (!cores, solver#get_proof)

let make_proof_with_solver formula cores =
  let solver = get_solver true in
  let f = AstUtil.cnf (AstUtil.simplify formula) in
    solver#init f;
    List.iter (fun x -> solver#add_clause (reverse x)) cores;
    if solver#solve then
      begin
        failwith "SatPL, make_proof: called with a sat formula"
      end
    else
      begin
        solver#get_proof
      end

(** assume the formula + cores is unsat
 * formula is a Conjunction
 *)
let make_proof_without_solver formula core =
  let to_resolv = match core with
    | And lst -> List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty lst
    | _ -> failwith "SatPL, make_proof_without_solver: core is not a conj"
  in
  let lst = match formula with 
    | And lst -> lst
    | _ -> failwith "SatPL, make_proof_without_solver: formula is not a conj"
  in
  let rec build_proof proof to_resolv lst = match lst with
    | x::xs ->
      begin
        if PredSet.mem x to_resolv then
          begin
            let clause = PredSet.singleton x in
            let to_resolv = PredSet.remove x to_resolv in
            let prf = DpllProof.RPNode (AstUtil.proposition_of_lit x, proof, DpllProof.RPLeaf clause, to_resolv) in
              if PredSet.is_empty to_resolv then
                prf
              else
                build_proof prf to_resolv xs
          end
        else
          begin
            build_proof proof to_resolv xs
          end
      end
    | [] ->
      begin
        assert(Global.is_off_assert() || PredSet.is_empty to_resolv);
        proof
      end
  in
    build_proof (DpllProof.RPLeaf to_resolv) to_resolv lst
