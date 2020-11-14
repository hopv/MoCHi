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

(** Part of the DPLL: Core (decision policy,...) *)

open   CsisatAst
open   CsisatAstUtil
open   CsisatSatInterface
open   CsisatDpllClause
open   CsisatDpllProof
open   CsisatUtils
(**/**)
module Message = CsisatMessage
module OrdSet  = CsisatOrdSet
module Global  = CsisatGlobal
(**/**)

(*a simple dpll SAT solver*)
(*TODO improve:
 - drop predicate for integers only
 - put predicate to atom conversion in the wrapper.
*)

(** Resolution proof*)
type int_res_proof = IRPNode of int * int_res_proof * int_res_proof * int_clause (** pivot, left, right, result*)
                   | IRPLeaf of int_clause (** A leaf is simply a clause.*)
let int_get_result proof = match proof with
  | IRPNode (_,_,_,r) -> r
  | IRPLeaf r -> r

(** To store the decision level.
 *)
type var_assign = Open (** free choice (decision policy) *)
                | Implied of int_res_proof (** unit resolution*)
                | TImplied of int_res_proof (** implied by a theory (bool+T) TODO *)

class int_system =
  fun with_prf ->
  object (self)

    val keep_proof = with_prf
    val mutable possibly_sat = true
    val mutable resolution_proof = None
    
    val mutable clauses = Array.make 0 (new int_clause 1 [1] true )
    val mutable assignment = Array.make 2 lUnk
    val choices = Stack.create ()
    val mutable unsat_clauses = IntSet.empty
    val mutable prop_to_clauses = Array.make 2 (IntSet.empty, IntSet.empty)
    val mutable learning_level = 1
    val partial_proof = Hashtbl.create 1000

    method get_assigned_props =
      begin
        let affect = ref [] in
          Array.iteri (fun i x -> if x <> lUnk then affect := i :: !affect) assignment;
          !affect
      end
    method get_assign = List.map (fun i -> i * assignment.(i)) self#get_assigned_props

    (** 0-: no learning,
     *  1+: learn clause that are less or equal than value.
     * Default value is 3/2 * average size.
     * Warning: call this method after having called init.
     *)
    method set_learning_level l = learning_level <- l
    
    method private store_proof clause proof = Hashtbl.replace partial_proof clause proof
    method private get_partial_proof clause = Hashtbl.find partial_proof clause
    method private proof_for_clause clause =
      if clause#is_learned then self#get_partial_proof clause
      else IRPLeaf clause


    method resize max_index =
      let size = (Array.length assignment) -1 in
        Message.print Message.Debug
          (lazy("DPLL, resizing from "^(string_of_int size)^" to "^(string_of_int max_index)));
        if max_index <> size then
          begin
            if max_index < size then
              begin
                for i = max_index + 1 to size do
                  assert (Global.is_off_assert() || assignment.(i) = lUnk);
                  assert (Global.is_off_assert() || prop_to_clauses.(i) = (IntSet.empty, IntSet.empty))
                done
              end;
            Message.print Message.Debug (lazy("DPLL, resizing clauses"));
            Array.iter (fun x -> x#resize max_index) clauses;

            Message.print Message.Debug (lazy("DPLL, resizing assignment"));
            let new_array = Array.make (max_index + 1) lUnk in
              Array.blit assignment 1 new_array 1 (min max_index size);
              assignment <- new_array;
              
              Message.print Message.Debug (lazy("DPLL, resizing prop_to_clauses"));
              let new_prop_to_clause =  Array.make (max_index + 1) (IntSet.empty, IntSet.empty) in
                Array.blit prop_to_clauses 1 new_prop_to_clause 1 (min max_index size);
                prop_to_clauses <- new_prop_to_clause
          end
    
    method private add_to_prop_to_clause index cl =
      let pos = cl#get_pos_props in
      let neg = cl#get_neg_props in
        IntSet.iter (fun p ->
            let (old_p,old_n) = prop_to_clauses.(p) in
            let new_p = IntSet.add index old_p in
              prop_to_clauses.(p) <- (new_p,old_n)
          ) pos;
        IntSet.iter (fun n ->
            let (old_p,old_n) = prop_to_clauses.(n) in
            let new_n = IntSet.add index old_n in
              prop_to_clauses.(n) <- (old_p,new_n)
          ) neg

    method init (formula: int list list) =
      Message.print Message.Debug (lazy("DPLL, init"));
      (* clauses *)
      let size = (Array.length assignment -1) in
      Message.print Message.Debug (lazy("DPLL, create clauses"));
      let clauses_lst = List.map (fun x -> new int_clause size x false) formula in
        clauses <- Array.of_list clauses_lst;
      Message.print Message.Debug (lazy("DPLL, add_to_prop_to_clause"));
        Array.iteri (fun i c -> self#add_to_prop_to_clause i c) clauses;
        (* unsat_clauses *)
        let nb_clauses = Array.length clauses in
        let enum = ref IntSet.empty in
          for i = 0 to nb_clauses -1 do
            enum := IntSet.add i !enum
          done;
          unsat_clauses <- !enum;
          (* clause learning *)
          let cl_size = List.map List.length formula in
          let average_size = (List.fold_left (+) 0 cl_size) / nb_clauses in
            self#set_learning_level ((3 * average_size) / 2);
      Message.print Message.Debug (lazy("DPLL, initialized"))
    
    method reset =
      possibly_sat <- true;
      resolution_proof <- None;
      clauses <-  Array.make 0 (new int_clause 1 [1] true );
      assignment <- Array.make 1 lUnk;
      Stack.clear choices;
      learning_level <- 1;
      unsat_clauses <- IntSet.empty;
      prop_to_clauses <- Array.make 0 (IntSet.empty, IntSet.empty);
      Hashtbl.clear partial_proof

    (** insert a new clause
     * @return false if need to backtrack
     *)
    method private new_clause cl =
      List.iter (cl#affect) self#get_assign;
      clauses <- Array.append clauses (Array.make 1 cl);
      let last_index = (Array.length clauses) -1 in
        self#add_to_prop_to_clause last_index cl;
        if cl#is_sat then
          begin
            (*unstack to the first lit that satisfied the clause*)
            let rec insert sat_element =
              let (pivot,reason,clauses) as entry = Stack.pop choices in
                if pivot = sat_element then
                  begin
                    assert (Global.is_off_assert() || cl#has pivot);
                    Stack.push (pivot, reason, IntSet.add last_index clauses) choices
                  end
                else
                  begin
                    insert sat_element;
                    Stack.push entry choices
                  end
            in
              insert (cl#get_satisfied);
              true
          end
        else
          begin
            unsat_clauses <- IntSet.add last_index unsat_clauses;
            not (cl#contradiction)
          end

    method add_clause (lst: int list) =
      let size = Array.length assignment in
      let cl = new int_clause size lst false in
      let res = self#new_clause cl in
        if not res then self#backjump cl
    
    (*TODO
     * -is subset of an existing clause ?
     * -is stronger than an existing clause ?
     * => using some kind of tries ( O(#literals) )??
     *)
    method private choose_to_learn_clause cl prf =
      if cl#full_size <= learning_level then
        begin
          (* as learning is not only at the end, new_clause may return false *)
          ignore (self#new_clause cl);
          self#store_proof cl prf
        end

    (** Method to call at the end of the backtracking.
     *  It forces the learning of the given clause.
     *  The learned clause has to be in a not contradictory state.
     *)
    method private force_learning cl prf =
        assert (Global.is_off_assert() || self#new_clause cl);
        self#store_proof cl prf

    method affect p reason =
      Message.print Message.Debug (lazy("DPLL, affecting : "^(string_of_int p)));
      assert (Global.is_off_assert() || assignment.(index_of_literal p) = lUnk);
      assignment.(index_of_literal p) <- value_of_literal p;
      let (pos,neg) = prop_to_clauses.(index_of_literal p) in
      let (_true,_false) = if (value_of_literal p) = lTrue then (pos,neg) else (neg,pos)
      in
      let newly_sat = IntSet.filter (fun i -> not (clauses.(i))#is_sat) _true in
        IntSet.iter (fun i -> clauses.(i)#affect p) _false;
        IntSet.iter (fun i -> clauses.(i)#affect p) _true;
        unsat_clauses <- IntSet.diff unsat_clauses newly_sat;
        Stack.push (p,reason, newly_sat) choices

    method forget =
      let (pivot,how,satisfied) = Stack.pop choices in
      Message.print Message.Debug (lazy("DPLL, forgetting: "^(string_of_int pivot)));
      assert (Global.is_off_assert() || assignment.(index_of_literal pivot) = (value_of_literal pivot));
      assignment.(index_of_literal pivot) <- lUnk;
      let (pos,neg) = prop_to_clauses.(index_of_literal pivot) in
        IntSet.iter (fun i -> clauses.(i)#forget pivot) pos;
        IntSet.iter (fun i -> clauses.(i)#forget pivot) neg;
        unsat_clauses <- IntSet.union unsat_clauses satisfied;
        (pivot,how)

    (** Is there a contradiction (clause impossible to satisfy) ? *)
    method private has_contra =
      IntSet.exists (fun i -> clauses.(i)#contradiction) unsat_clauses

    (** Does the current assignment satisfy the system ? *)
    method private is_sat = IntSet.is_empty unsat_clauses

    (** Get one of the clause with contradiction (for backtracking)*)
    method private get_unsat_clause =
      let index = find_in_IntSet (fun i -> clauses.(i)#contradiction) unsat_clauses in
        clauses.(index)

    (* Variable choice heuristics *)

    (** Returns a variable that satisfies the maximum #clauses *)
    method find_max_degree =
      let max = ref 0 in
      let prop = ref None in
        Array.iteri
          (fun index (pos,neg) ->
            if assignment.(index) = lUnk then
              begin
                let res = ref 0 in
                  IntSet.iter (fun i -> if not clauses.(i)#is_sat then res := !res + 1) pos;
                  IntSet.iter (fun i -> if not clauses.(i)#is_sat then res := !res - 1) neg;
                  if abs !res > !max then
                    begin
                      max := abs !res;
                      if !res > 0  then prop := Some index
                      else prop := Some (lNot index)
                    end
              end
          ) prop_to_clauses;
        !prop

    (** Returns a variable that only satisfies clauses *)
    method find_max_unipolar_variable =
      let max = ref 0 in
      let prop = ref None in
        Array.iteri
          (fun pr (pos,neg) ->
            if assignment.(pr) = lUnk then
              begin
                let size_p = IntSet.fold (fun i counter -> if not clauses.(i)#is_sat then counter + 1 else counter) pos 0 in
                let size_n = IntSet.fold (fun i counter -> if not clauses.(i)#is_sat then counter + 1 else counter) neg 0 in
                  match (size_p > 0,size_n > 0) with
                  | (true,false) -> if size_p > !max then (prop := Some pr; max := size_p)
                  | (false,true) -> if size_n > !max then (prop := Some pr; max := size_n)
                  | _ -> ()
              end
          ) prop_to_clauses;
        !prop

    (** try to find a clause with only one literal left.
     * @return Some(literal,clause)
     *)
    method find_unit_propagation =
      try 
        let p = find_in_IntSet (fun i -> clauses.(i)#size = 1) unsat_clauses in
        let c = clauses.(p)#get_choice in
          Some (c,clauses.(p))
      with Not_found -> None

    (** Returns a literal that will make a clause sat*)
    method find_random =
      try Some clauses.(IntSet.choose unsat_clauses)#get_choice
      with Not_found -> None

    (*TODO T-propagation*)
    method decision_policy =
      match self#find_unit_propagation with
      | Some (lit,cl) ->
        begin
          let proof = 
            if cl#is_learned then
              self#get_partial_proof cl
            else
              IRPLeaf cl
          in
            self#affect (lit) (Implied proof)
        end
      | None ->
        begin
          match self#find_max_unipolar_variable with
          | Some lit  -> self#affect lit Open
          | None ->
            begin
              match self#find_max_degree with
              | Some lit  -> self#affect lit Open
              | None ->
                begin
                  match self#find_random with
                  | Some lit  -> self#affect lit Open
                  | None -> failwith "DPLL, decision_policy: no possible affectation"
                end
            end
        end

    (** to call when unsat + need a proof.
     * (as the learning last clause of not mandatory -> backjump has to make the first affect)
     *)
    method private backjump explanation =
      let rec build_proof prf =
        try 
          let (pivot, how) = self#forget in
            match how with
            | Open ->
              if (int_get_result prf)#has_prop pivot then
                self#force_learning (int_get_result prf) prf
              else
                build_proof prf
            | Implied proof ->
              if (int_get_result proof)#has_prop pivot then
                begin
                  let resolved_clause = (int_get_result prf)#resolve pivot (int_get_result proof) in
                  let new_prf =
                    if keep_proof then IRPNode (pivot, prf, proof, resolved_clause)
                    else IRPLeaf resolved_clause
                  in
                    self#choose_to_learn_clause resolved_clause new_prf;
                    build_proof new_prf
                end
              else
                build_proof prf
            | TImplied proof -> (*continue proof further*)
              failwith "DpllCore, backjump: theory deduction not supported for the moment."
        with Stack.Empty ->
          begin (*now we have a proof of unsat*)
            assert (Global.is_off_assert() || (int_get_result prf)#size = 0);
            resolution_proof <- Some prf;
            possibly_sat <- false
          end
      in
        build_proof (self#proof_for_clause explanation)

    method solve =
      if possibly_sat then
        begin
        Message.print Message.Debug (lazy("DPLL, system is possibly sat."));
          if self#is_sat then Some(self#get_assign)
          else if self#has_contra then
            begin
              let cl = self#get_unsat_clause in
                Message.print Message.Debug (lazy("DPLL, backtracking with: "^(cl#to_string)));
                self#backjump cl;
                self#solve
            end
          else
            begin
              Message.print Message.Debug (lazy("DPLL taking decision_policy branch"));
              self#decision_policy;
              self#solve
            end
        end
      else
        None

    method get_proof_of_unsat =
      match resolution_proof with
      | Some prf -> prf
      | None -> failwith "DPLL, no resolution proof"

  end

(*** Wrapper ***)
class int_csi_dpll =
  fun with_proof ->
  object (self)

    inherit sat_solver with_proof

    val sys = new int_system with_proof

    val mutable counter = 0
    method private get_fresh_index = counter <- counter + 1; counter
    val index_to_atom = Hashtbl.create 500
    val atom_to_index = Hashtbl.create 500

    method private get_index atom =
      let proposition = proposition_of_lit atom in
      let index =
        if Hashtbl.mem atom_to_index proposition then
          begin
            Hashtbl.find atom_to_index proposition
          end
        else
          begin
            let index = self#get_fresh_index in
              Hashtbl.add atom_to_index proposition index;
              Hashtbl.add index_to_atom index proposition;
              index
          end
      in
        if atom = proposition then index else -index

    method private get_atom index =
      let at = Hashtbl.find index_to_atom (abs index) in
        if (value_of_literal index) = lFalse then
          normalize_only (Not at)
        else
          at
    
    method private convert_clause formula = match formula with
      | Or lst -> List.map (fun x -> (self#get_index x)) lst;
      | err -> failwith ("DpllCore, convert_clause: expecting disjunction, given: "^ print err)

    method init formulae = match formulae with
      | And lst ->
        begin
          assert(Global.is_off_assert() || counter = 0);(* i.e. first time it is initialized *)
          let converted = List.map (fun x -> self#convert_clause x) lst in
            sys#resize counter;
            sys#init converted
        end
      | err -> failwith ("DpllCore, init: expecting CNF, given: "^ print err)
    
    method add_clause formula =
      let old_index = counter in
      let lst = self#convert_clause formula in
        if old_index < counter then sys#resize counter;
        sys#add_clause lst
    
    val mutable last_solution: predicate list option = None
    method solve = match sys#solve with
      | Some sol -> last_solution <- Some (List.map self#get_atom sol); true
      | None -> last_solution <- None; false

    method get_solution = match last_solution with
      | Some sol -> sol
      | None -> failwith "DpllCore: no solution for the moment"
    
    method get_proof =
      let partial_translation = Hashtbl.create 1000 in
      let transform_clause cl =
        let lits = cl#get_literals in
          IntSet.fold
            (fun i acc -> PredSet.add (self#get_atom i) acc)
            lits PredSet.empty
      in
      let rec transform proof =
        let cl = int_get_result proof in
          if Hashtbl.mem partial_translation cl then
            Hashtbl.find partial_translation cl
          else
            begin
              match proof with
              | IRPLeaf cl -> RPLeaf (transform_clause cl)
              | IRPNode (pivot, left, right, cl) ->
                begin
                  let transformed_pivot  = self#get_atom pivot in
                  let transformed_left   = transform left in
                  let transformed_right  = transform right in
                  let transformed_clause = transform_clause cl in
                    RPNode (transformed_pivot, transformed_left, transformed_right, transformed_clause)
                end
            end
      in
      let proof = sys#get_proof_of_unsat in 
      let transformed = transform proof in
        Message.print Message.Debug (lazy(tracecheck_of_proof transformed));
        transformed

  end

type old_var_assign = OOpen (** free choice (decision policy) *)
                    | OClosed of res_proof (** after backtracking *)
                    | OImplied of res_proof (** unit resolution*)
                    | OTImplied of res_proof (** implied by a theory (bool+T) TODO *)
(** DPLL system, mostly a list of clauses
 * if 'with_prf' then keep the resolution proof in memory
 * the constructor build an empty system, call the method 'init' with the CNF formula you want
 *)
class system =
  fun with_prf ->
  object (self)
    
    val mutable possibly_sat = true
    val mutable resolution_proof = None
    
    val mutable clauses = Array.make 0 (new clause (Or [Eq(Constant 1.0,Constant 1.0)]) true )
    val mutable props = PredSet.empty
    val mutable affected = PredSet.empty
    val choices = Stack.create ()

    val prop_to_clauses = Hashtbl.create 123
    
    val keep_proof = with_prf
    val mutable learning_level = 1
    (** -1: no learning,
     *  0: some learning,
     *  1+: learn clause that are less or equal than value.
     * Default value is 3/2 * average size.
     * Warning: call this method after having called init.
     *)
    method set_learning_level l = learning_level <- l

    (*is an OrdSet*)
    val mutable unsat_clauses = []

    method reset =
      clauses <- Array.make 0 (new clause (Or [Eq(Constant 1.0,Constant 1.0)]) true);
      unsat_clauses <- [];
      props <- PredSet.empty;
      affected <- PredSet.empty;
      Hashtbl.clear prop_to_clauses;
      Stack.clear choices

    method add_pos_clause_for_prop p cl =
      let (oldp, oldn) = try Hashtbl.find prop_to_clauses p with Not_found -> ([],[]) in
        Hashtbl.replace prop_to_clauses p (OrdSet.union [cl] oldp, oldn)
    method add_neg_clause_for_prop p cl =
      let (oldp, oldn) = try Hashtbl.find prop_to_clauses p with Not_found -> ([],[]) in
        Hashtbl.replace prop_to_clauses p (oldp, OrdSet.union [cl] oldn)

    
    (*assume CNF*)
    method init formula = 
      props <- get_proposition_set formula;
      PredSet.iter (fun x -> Hashtbl.add prop_to_clauses x ([],[])) props;
      match formula with
      | And lst ->
        begin
          let n = List.length lst in
            clauses <- Array.make n (new clause (Or [Eq(Constant 1.0,Constant 1.0)]) true);
            ignore (List.fold_left (fun i e -> 
                let cl = new clause e false in
                  clauses.(i) <- cl;
                  let pos = cl#pos_props in PredSet.iter (fun x -> self#add_pos_clause_for_prop x cl) pos;
                  let neg = cl#neg_props in PredSet.iter (fun x -> self#add_neg_clause_for_prop x cl) neg;
                    i + 1
              ) 0 lst);
            unsat_clauses <- OrdSet.list_to_ordSet (Array.to_list clauses);
            let average_size = (Array.fold_left (fun acc cl -> acc + cl#size) 0 clauses) / (Array.length clauses) in
              self#set_learning_level ((3 * average_size) / 2)
        end
      | _ -> failwith "DPLL: expect CNF"
     
    (** Is there a contradiction (clause impossible to satisfy) ? *)
    method has_contra = 
      List.exists (fun x -> x#contradiction) unsat_clauses

    (** Does the current assignment satisfy the system ? *)
    method is_sat =
      match unsat_clauses with
      | [] -> true
      | _ -> false

    method affect p reason =
      Message.print Message.Debug (lazy("DPLL, affecting : "^(print p)));
      assert (Global.is_off_assert() || not (PredSet.mem (contra p) affected));
      affected <- PredSet.add p affected;
      let (pos,neg) = Hashtbl.find prop_to_clauses (proposition_of_lit p) in
      let (_true,_false) = if (proposition_of_lit p) = p then (pos,neg) else (neg,pos)
      in
      let newly_sat = List.filter (fun x -> not x#is_sat) _true in
        List.iter (fun x -> x#affect p) _false;
        List.iter (fun x -> x#affect p) _true;
        unsat_clauses <- OrdSet.subtract unsat_clauses newly_sat;
        Stack.push (p,reason, newly_sat) choices

    method forget =
      let (pivot,how,satisfied) = Stack.pop choices in
      Message.print Message.Debug (lazy("DPLL, forgetting: "^(print pivot)));
      assert (Global.is_off_assert() || PredSet.mem pivot affected);
      affected <- PredSet.remove pivot affected;
      let (pos,neg) = Hashtbl.find prop_to_clauses (proposition_of_lit pivot) in
      let (_true,_false) = if (proposition_of_lit pivot) = pivot then (pos,neg) else (neg,pos)
      in
        List.iter (fun x -> x#forget pivot) _true;
        List.iter (fun x -> x#forget pivot) _false;
        unsat_clauses <- OrdSet.union unsat_clauses satisfied;
        (pivot,how)

    method get_assign = predSet_to_ordSet affected
    
    method get_assigned_props = List.map proposition_of_lit self#get_assign

    (*return the first clause that satisfies fct*)
    method scan_clauses fct =
      let i = ref 0 in
      let n = Array.length clauses in
      let ans = ref false in
        while (not !ans) && !i < n do
          ans := fct clauses.(!i);
          i := !i + 1
        done;
        if !ans then Some clauses.(!i-1) else None
    
    method filter_clauses fct =
      List.filter fct (Array.to_list clauses)
    
    method iter_clauses fct =
      Array.iter fct clauses

    method to_string =
      let buffer = Buffer.create 1024 in
      let assign = self#get_assign in
        Buffer.add_string buffer "current assign is ";
        List.iter (fun x ->
            Buffer.add_string buffer (print x); 
            Buffer.add_string buffer ", ";
          ) assign;
        Buffer.add_char buffer '\n';
        self#iter_clauses (fun x ->
          Buffer.add_string buffer (x#to_string_detailed);
          Buffer.add_char buffer '\n');
        Buffer.contents buffer

    (************************************************************)
    (****************   DECISION POLICY   ***********************)
    (************************************************************)

    (*return a variable that only satisfies clauses *)
    method find_max_unipolar_variable =
      let max = ref 0 in
      let prop = ref None in
        Hashtbl.iter
          (fun pr (pos,neg) ->
            if not (PredSet.mem pr affected) && not (PredSet.mem (contra pr) affected) then
              begin
                let pos = List.filter (fun x -> not x#is_sat) pos in
                let neg = List.filter (fun x -> not x#is_sat) neg in
                  match (pos,neg) with
                  | ([],[]) -> ()
                  | (p, []) -> if List.length p > !max then (prop := Some pr; max := List.length p)
                  | ([], n) -> if List.length n > !max then (prop := Some (contra pr); max := List.length n)
                  | _ -> ()
              end
          ) prop_to_clauses;
        !prop

    (** try to find a clause with only one literal left.
     * @return Some(literal,clause)
     *)
    method find_unit_propagation =
      try 
        let p = List.find (fun x -> x#size = 1) unsat_clauses in
        let c = p#get_choice in
          Some (c,p)
      with Not_found -> None
      (*match self#scan_clauses (fun x -> x#size = 1 && not x#is_sat) with
      | Some p -> let c = p#get_choice in Some (c,p)
      | None -> None*)

    (*return a variable that satisfies the maximun #clauses *)
    method find_max_degree =
      let max = ref 0 in
      let prop = ref None in
        Hashtbl.iter
          (fun pr (pos,neg) ->
            if not (PredSet.mem pr affected) && not (PredSet.mem (contra pr) affected) then
              begin
                let pos = List.filter (fun x -> not x#is_sat) pos in
                let neg = List.filter (fun x -> not x#is_sat) neg in
                  if abs ((List.length pos) - (List.length neg)) > !max then
                    begin
                      max := abs ((List.length pos) - (List.length neg));
                      if (List.length pos) - (List.length neg) > 0
                        then prop := Some pr
                        else prop := Some (contra pr)
                    end
              end
          ) prop_to_clauses;
        !prop
      
    (** return a literal that will make a clause sat*)
    method find_random =
      let length = List.length unsat_clauses in
      let n = Random.int length in
      let c = (List.nth unsat_clauses n) in
        Some c#get_choice
      

    (** return a clause that cannot be satisfied*)
    method get_unsat_clause =
      try List.find (fun x -> x#contradiction) unsat_clauses
      with Not_found -> failwith "DPLL: get_unsat_clause called without contradiction"

    (** insert a new clause
     * @return false if need to backtrack
     *)
    method new_clause cl =
      let pos = cl#pos_props in PredSet.iter (fun x -> self#add_pos_clause_for_prop x cl) pos;
      let neg = cl#neg_props in PredSet.iter (fun x -> self#add_neg_clause_for_prop x cl) neg;
      List.iter (cl#affect) self#get_assign;
      clauses <- Array.append clauses (Array.make 1 cl);
      if cl#is_sat then
        begin
          let sat_element = ref (cl#get_satisfied) in
          (*unstack to the first lit that satisfied the clause*)
          let copy = ref [] in
            while (PredSet.cardinal !sat_element) > 0 do
              let (pivot,_,_) as entry = Stack.pop choices in
                copy := entry::!copy;
                sat_element := PredSet.remove pivot !sat_element
            done;
            let (pivot,reason,clauses) = List.hd !copy in
              assert (Global.is_off_assert() || cl#has pivot);
              Stack.push (pivot,reason, OrdSet.union [cl] clauses) choices;
              List.fold_left (fun () x -> Stack.push x choices) () (List.tl !copy);
              true
        end
      else
        begin
          unsat_clauses <- OrdSet.union [cl] unsat_clauses;
          not (cl#contradiction)
        end

    method learned_clause disj =
      let cl = new clause disj true in
      let res = self#new_clause cl in
        assert (Global.is_off_assert() || res)
    
    method learn_clause cl =
      ignore (self#new_clause cl)
      (*
      let res = self#new_clause cl in
        assert (Global.is_off_assert() || res)
      *)
    
    val partial_proof = Hashtbl.create 1000
    method store_proof clause proof = Hashtbl.replace partial_proof clause proof
    method get_partial_proof clause = Hashtbl.find partial_proof clause

    
    (** to call when unsat + need a proof
     *)
    method backjump explanation =
      let clause_of_set set =
        new clause (Or (PredSet.fold (fun x acc -> x::acc) set [])) true
      in
      let rec build_proof prf =
        try 
          let (pivot, how) = self#forget in
            match how with
            | OOpen -> (*can stop the proof here and pick new assign*)
              begin
                let assigned = OrdSet.list_to_ordSet (self#get_assigned_props) in
                let choices =
                  OrdSet.list_to_ordSet
                    (PredSet.fold (fun x acc -> x::acc)
                      (PredSet.fold
                        (fun e acc -> let p = List.hd (get_proposition e) in PredSet.add p acc)
                        (get_result prf) PredSet.empty)
                      [])
                in
                let resulting = OrdSet.subtract choices assigned in
                  if List.length resulting > 0 then
                    begin
                      Message.print Message.Debug (lazy("DPLL, backjumping ended in Open"));
                      let c =
                        let tmp = (List.hd resulting) in
                          if PredSet.mem tmp (get_result prf) then
                            tmp
                          else
                            begin
                              assert (Global.is_off_assert() || PredSet.mem (contra tmp) (get_result prf));
                              contra tmp
                            end

                      in
                        if keep_proof then
                          self#affect c (OClosed prf)
                        else
                          self#affect c (OClosed (RPLeaf (get_result prf)))
                    end
                  else
                    build_proof prf
              end
            | OClosed proof -> (*try to find an not tested var or continue proof further*)
              begin
                let satisfied_clause = get_result proof in
                let to_satisfy = get_result prf in
                let new_prf =
                  if PredSet.mem (contra pivot) to_satisfy then
                    begin
                      let new_unsat_disj = 
                        PredSet.remove (contra pivot)
                          (PredSet.remove pivot
                            (PredSet.union to_satisfy satisfied_clause))
                      in
                        let new_prf = if keep_proof then
                            RPNode (List.hd (get_proposition pivot), proof, prf, new_unsat_disj)
                          else
                            RPLeaf new_unsat_disj
                        in
                          if learning_level >= 1 && PredSet.cardinal new_unsat_disj <= learning_level then
                            begin
                              let cl = clause_of_set new_unsat_disj in
                                self#store_proof cl new_prf;
                                self#learn_clause cl
                            end;
                          new_prf
                    end
                  else
                    begin
                      (*at this point, it may be usefull to learn the clause of (Closed proof)*)
                      (*also keep the proof*)
                      if learning_level = 0 then
                        begin
                          let cl = clause_of_set satisfied_clause in
                            self#store_proof cl prf;
                            self#learn_clause cl
                        end;
                      prf
                    end
                in
                  let possible = PredSet.fold (fun x acc -> x::acc ) (get_result new_prf) [] in
                    try
                      let new_try = List.find
                        (fun x ->
                          (not (PredSet.mem x affected)) && (not (PredSet.mem (contra x) affected))
                        ) possible
                      in
                        Message.print Message.Debug (lazy("DPLL, backjumping ended in Closed"));
                        self#affect new_try (OClosed new_prf)
                    with Not_found ->
                      build_proof new_prf
              end
            | OImplied proof -> (*continue proof further*)
              begin
                let satisfied_clause = get_result proof in
                let to_satisfy = get_result prf in
                let new_prf =
                  if PredSet.mem (contra pivot) to_satisfy then
                    begin
                      let new_unsat_disj = 
                          PredSet.remove (contra pivot)
                            (PredSet.remove pivot
                              (PredSet.union to_satisfy satisfied_clause))
                      in
                        let new_prf = if keep_proof then
                            RPNode (List.hd (get_proposition pivot), proof, prf, new_unsat_disj)
                          else
                            RPLeaf new_unsat_disj
                        in
                          if learning_level >= 1 && PredSet.cardinal new_unsat_disj <= learning_level then
                            begin
                              let cl = clause_of_set new_unsat_disj in
                                self#store_proof cl new_prf;
                                self#learn_clause cl
                            end;
                          new_prf
                    end
                  else
                    begin
                      prf
                    end
                in
                  build_proof new_prf
              end
            | OTImplied proof -> (*continue proof further*)
              begin
                (*TODO need T-lemma*)
                failwith "DPLL: theory deduction yet to come"
              end
        with Stack.Empty ->
          begin (*now we have a proof of unsat*)
            Message.print Message.Debug (lazy(tracecheck_of_proof prf));
            assert (Global.is_off_assert() || (get_result prf) = PredSet.empty);
            resolution_proof <- Some prf;
            possibly_sat <- false
          end
      in
      let start_proof = 
        if explanation#is_learned then
          self#get_partial_proof explanation
        else
          RPLeaf explanation#get_propositions
      in
        build_proof start_proof


    method add_clause disj =
      let cl = new clause disj false in
      let res = self#new_clause cl in
        if not res then self#backjump cl
   
    (*TODO T-propagation*)
    method decision_policy =
      match self#find_unit_propagation with
      | Some (lit,cl) ->
        begin
          Message.print Message.Debug (lazy("DPLL, found unit propagation: "^(print lit)));
          (*self#affect (lit) (Implied (RPLeaf cl))*)
          let proof = 
            if cl#is_learned then
              self#get_partial_proof cl
            else
              RPLeaf cl#get_propositions
          in
            self#affect (lit) (OImplied proof)
        end
      | None ->
        begin
          Message.print Message.Debug (lazy("DPLL, no unit propagation"));
          match self#find_max_unipolar_variable with
          | Some lit  ->
            begin
              Message.print Message.Debug (lazy("DPLL, found max unipolar literal: "^(print lit)));
              self#affect lit OOpen
            end
          | None ->
            begin
              Message.print Message.Debug (lazy("DPLL, no max degree literal"));
              match self#find_max_degree with
              | Some lit  ->
                begin
                  Message.print Message.Debug (lazy("DPLL, found max max degree literal: "^(print lit)));
                  self#affect lit OOpen
                end
              | None ->
                begin
                  match self#find_random with
                  | Some lit  ->
                    begin
                      Message.print Message.Debug (lazy("DPLL, found random literal: "^(print lit)));
                      self#affect lit OOpen
                    end
                  | None ->
                    failwith "DPLL, decision_policy: no possible affectation"
                end
            end
        end

    method solve =
      if possibly_sat then
        begin
        Message.print Message.Debug (lazy("DPLL, system is possibly sat."));
          if self#is_sat then
            Some(self#get_assign)
          else if self#has_contra then
            begin
              let cl = self#get_unsat_clause in
                Message.print Message.Debug (lazy("DPLL, backtracking with: "^(cl#to_string)));
                self#backjump cl;
                self#solve
            end
          else
            begin
              Message.print Message.Debug (lazy("DPLL taking decision_policy branch"));
              self#decision_policy;
              self#solve
            end
        end
      else
        None

    method get_proof_of_unsat =
      match resolution_proof with
      | Some prf -> prf
      | None -> failwith "DPLL, no resolution proof"

  end

(*** Wrapper ***)
class csi_dpll with_proof =
  object
    inherit sat_solver with_proof
    val sys = new system with_proof

    method init formulae = sys#init formulae
    
    method add_clause formula = sys#add_clause formula
    
    val mutable last_solution: predicate list option = None
    method solve = match sys#solve with
      | Some sol -> last_solution <- Some sol; true
      | None -> last_solution <- None; false

    method get_solution = match last_solution with
      | Some sol -> List.map  normalize_only sol
      | None -> failwith "DpllCore: no solution for the moment"
    
    method get_proof = sys#get_proof_of_unsat
  end
