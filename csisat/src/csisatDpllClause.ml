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

(** Part of the DPLL: Clause *)

open   CsisatAst
open   CsisatAstUtil
open   CsisatUtils
(**/**)
module Global  = CsisatGlobal
(**/**)

(* TODO *)
(* as in DIMACS, variable index starts with 1.*)
let lFalse = -1
let lUnk = 0
let lTrue = 1
let lNot i = -i

let value_of_literal lit =
  if lit > 0 then lTrue
  else if lit < 0 then lFalse
  else lUnk

let index_of_literal = abs 

class int_clause =
  fun max_index int_lst (l:bool) ->
    let literal_array = Array.make (max_index + 1) lUnk in
    let _ = List.iter (fun x ->
          assert(Global.is_off_assert() ||  literal_array.(index_of_literal x) = lUnk );
          if x < 0 then literal_array.(-x) <- lFalse
          else literal_array.(x) <- lTrue
        ) int_lst
    in
  object (self)

    val mutable literals = literal_array

    (** changes the size of the array that stores the literals *)
    method resize max_index =
      let size = (Array.length literals) -1 in
      if max_index > size then
        begin
          let new_array = Array.make (max_index + 1) lUnk in
            Array.blit literals 1 new_array 1 size;
            literals <- new_array
        end
      else if max_index < Array.length literals then
        begin
          for i = max_index + 1 to Array.length literals -1 do
            assert (Global.is_off_assert() || literals.(i) = lUnk)
          done;
          let new_array = Array.make (max_index + 1) lUnk in
            Array.blit literals 1 new_array 1 max_index;
            literals <- new_array
        end

    val mutable satisfied = 0
    val mutable left = IntSet.empty (* TODO is the Set the best representation ?? *)

    initializer
      begin
        let set = ref IntSet.empty in
          Array.iter (fun x -> if self#has x then set := IntSet.add x !set) literals;
          left <- !set
      end

    method get_choices = left
    method get_choice = IntSet.choose left
    method is_sat = satisfied <> 0
    method contradiction = satisfied = 0 && IntSet.is_empty left
    method get_satisfied = satisfied

    (** has litteral ?*)
    method has lit = literal_array.(index_of_literal lit) = (value_of_literal lit)
    (** has (Not litteral) ?*)
    method has_not lit = literal_array.(index_of_literal lit) = lNot (value_of_literal lit)
    (** has (normal or negated) the underlying poropsition *)
    method has_prop lit = literal_array.(index_of_literal lit) <> lUnk
    
    (** a learned clause comes from the backtracking*)
    val learned = l
    method is_learned = learned

    method size = IntSet.cardinal left
    method full_size = Array.fold_left (fun acc x -> if x <> lUnk then acc + 1 else acc ) 0 literals

    method get_literals =
      let lit_set = ref IntSet.empty in
        Array.iter (fun x -> if x <> lUnk then lit_set := IntSet.add x !lit_set ) literal_array;
        !lit_set

    (* these are not dynamic !! *)
    val propositions = (*proposition in clause not literal*)
      lazy (
        let p_set = ref IntSet.empty in
          Array.iteri (fun i x -> if x <> lUnk then p_set := IntSet.add i !p_set ) literal_array;
          !p_set )
    method get_propositions = Lazy.force propositions
    
    val pos_props =
      lazy (
        let p_set = ref IntSet.empty in
          Array.iteri (fun i x -> if x = lTrue then p_set := IntSet.add i !p_set ) literal_array;
          !p_set )
    method get_pos_props = Lazy.force pos_props

    val neg_props =
      lazy (
        let p_set = ref IntSet.empty in
          Array.iteri (fun i x -> if x = lFalse then p_set := IntSet.add i !p_set ) literal_array;
          !p_set )
    method get_neg_props = Lazy.force neg_props

    method resolve pivot cl =
      let (pos,neg) = 
        if self#has pivot then (self,cl)
        else (cl,self)
      in
        assert(Global.is_off_assert() || pos#has pivot);
        assert(Global.is_off_assert() || neg#has_not pivot);
        let new_lit = ref [] in
        for i = 1 to Array.length literals do
          if i <> (index_of_literal pivot)then
            begin
              assert (Global.is_off_assert() || not (pos#has i && neg#has_not i));
              assert (Global.is_off_assert() || not (pos#has_not i && neg#has i));
              if pos#has i || neg#has i then
                new_lit := i :: !new_lit
              else if pos#has_not i || neg#has_not i then
                new_lit := (lNot i) :: !new_lit
            end
        done;
        (* resloved clauses are learned clauses *)
        new int_clause (Array.length literals) !new_lit true

    (* Remark: affect & forget assume that the decision level is managed as a stack *)

    (** decision for a variable*)
    method affect lit =
      if satisfied = 0 then (*change only when not sat*)
        begin
          if self#has lit then
            begin
              satisfied <- lit
            end;
          if self#has_not lit then
            left <- IntSet.remove (lNot lit) left
        end

    (** unassign a variable (during backtracking) *)
    method forget lit =
      if satisfied = lit then
        begin
          satisfied <- 0
        end;
      if self#has_not lit && (satisfied = 0) then
        left <- IntSet.add (lNot lit) left

    method to_string =
      (string_list_cat " "
        (Array.fold_right
          (fun x acc -> (string_of_int x)::acc)
          (Array.mapi (fun i x -> i * x ) literals) ["0"] ))

    method to_string_detailed =
      "clause: " ^ self#to_string ^ "\n" ^
      "satisfied is: " ^ (string_of_int satisfied) ^ "\n" ^
      "left is: " ^ (string_list_cat ", " (IntSet.fold (fun x acc -> (string_of_int x)::acc) left []))
  end
(********)

(** Clause: (disjunction of literals) for the sat solver.
 *  Literals are stored in sets (log lookup/insert/del).
 *)
class clause =
  fun disj (l:bool) ->
  object (self)
    val propositions = match disj with
      | Or lst -> List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty lst
      | _ -> failwith "DPLL: clause expect a disjunction"
    method get_propositions = propositions (*oups, means literals*)

    (*OrdSet*)
    method literals = predSet_to_ordSet propositions
    
    (** a learned clause comes from the backtracking*)
    val learned = l
    method is_learned = learned

    val mutable left = match disj with
      | Or lst -> List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty lst
      | _ -> failwith "DPLL: clause expect a disjunction"
    val mutable satisfied = PredSet.empty

    (** has litteral ?*)
    method has el = PredSet.mem el propositions
    (** has (Not litteral) ?*)
    method has_not el = PredSet.mem (contra el) propositions

    method props = (*proposition in clause not literal*)
      PredSet.fold
        (fun e acc -> let p = List.hd (get_proposition e) in PredSet.add p acc)
        propositions PredSet.empty
    method pos_props = PredSet.filter self#has     self#props
    method neg_props = PredSet.filter self#has_not self#props

    method get_choices = left
    method get_choice = PredSet.choose left
    method is_sat = not (PredSet.is_empty satisfied)
    method contradiction = (not self#is_sat) && PredSet.is_empty left

    method size = PredSet.cardinal left

    (** decision for a variable*)
    method affect atom =
      let contr = contra atom in
      if PredSet.mem atom propositions then
        begin
          satisfied <- PredSet.add atom satisfied;
          left <- PredSet.remove atom left
        end;
      if PredSet.mem contr propositions then
        left <- PredSet.remove contr left

    (** unassign a variable (during backtracking) *)
    method forget atom =
      let contr = contra atom in
      if PredSet.mem atom propositions then
        begin
          satisfied <- PredSet.remove atom satisfied;
          left <- PredSet.add atom left
        end;
      if PredSet.mem contr propositions then
        left <- PredSet.add contr left

    method get_satisfied = satisfied

    (* Exists x. x and ¬x in clause*)
    method has_el_and_contra =
      PredSet.exists (fun x -> PredSet.mem (contra x) propositions) propositions
    
    method to_string =
      (string_list_cat ", "
        (PredSet.fold (fun x acc -> (print x)::acc) propositions []))

    method to_string_dimacs atom_to_int =
      (string_list_cat " "
        (PredSet.fold
          (fun x acc -> (string_of_int (atom_to_int x))::acc)
          propositions ["0"]))
    
    method to_string_detailed =
      "clause: " ^
      (string_list_cat ", " (PredSet.fold (fun x acc -> (print x)::acc) propositions [])) ^ "\n" ^
      "satisfied is: " ^
      (string_list_cat ", " (PredSet.fold (fun x acc -> (print x)::acc) satisfied [])) ^ "\n" ^
      "left is: " ^
      (string_list_cat ", " (PredSet.fold (fun x acc -> (print x)::acc) left [])) ^ "\n"
  end
