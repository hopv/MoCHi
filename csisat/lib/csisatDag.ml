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

(** Directed acyclic graph to reason about = and =\=*)

open   CsisatAst
open   CsisatAstUtil
(**/**)
module Message = CsisatMessage
module Utils   = CsisatUtils
module OrdSet  = CsisatOrdSet
module Global  = CsisatGlobal
(**/**)

(** A node in the graph: uninterpreted fct or variable.
 * A variable is an uninterpreted fct of arity 0.
 * The equivalence classes are managed with an union-find structure (parent field).
 *)
class node = 
  fun
    (ffname: string) 
    (aargs: node list) -> 
  object (self)
    val fname = ffname
    method get_fname = fname
    
    val args = aargs
    method get_args = args
    
    val arity = List.length aargs
    method get_arity = arity
    
    (*for equivalence class*)
    val mutable parent: node option = None
    method set_parent n = parent <- Some n
    method find: node = match parent with
      | None -> (self :> node)
      | Some n ->
        begin 
          let p = n#find in
            parent <- Some p;
            p
        end

    method congruent (that: node) =
        self#get_fname = that#get_fname
      &&
        self#get_arity = that#get_arity
      &&
        List.for_all (fun (a,b) -> a#find = b#find) (List.rev_map2 (fun x y -> (x,y)) (self#get_args) (that#get_args))

    (** return pairs of nodes whose equality may change the result of the 'congruent' method*)
    method may_be_congruent (that: node) =
      if self#get_fname <> that#get_fname
      || self#get_arity <> that#get_arity
      || self#find = that#find then []
      else
        List.filter (fun (a,b) -> a#find <> b#find) (List.rev_map2 (fun x y -> (x,y)) (self#get_args) (that#get_args))

    (*union of two equivalence classes*)
    method merge (that: node) =
      if self#find <> that#find then
        begin
          let n1 = self#find in
          let n2 = that#find in
            n1#set_parent n2
        end
    
  end

(** The DAG itself. Basically a set of node with tables to make the translation expr <-> node.
 * It also remember what was given (what is deduced). 
 *)
class dag = fun expr ->
  let table1 = Hashtbl.create 53 in
  let table2 = Hashtbl.create 53 in
  let create_and_add expr fn args =
    try Hashtbl.find table1 expr
    with Not_found ->
      begin
        let n = new node fn args
        in
          Hashtbl.replace table1 expr n;
          Hashtbl.replace table2 n expr;
          n
      end
  in
  let rec convert_exp expr = match expr with
    | Constant c as cst -> create_and_add cst (string_of_float c) []
    | Variable v as var -> create_and_add var v []
    | Application (f, args) as appl ->
      let node_args = (List.map convert_exp args) in
      let new_node  = create_and_add appl f node_args in
        new_node
    | Sum lst as sum ->
      let node_args = (List.map convert_exp lst) in
      let new_node  = create_and_add sum "+" node_args in
        new_node
    | Coeff (c, e) as coeff ->
      let node_args = (List.map convert_exp  [Constant c; e]) in
      let new_node  = create_and_add coeff "*" node_args in
        new_node
  in
  let _ = List.iter (fun x -> ignore (convert_exp x)) expr in
  object (self)
    val nodes: (expression, node) Hashtbl.t = table1
    val node_to_expr: (node, expression) Hashtbl.t = table2
    method get_node expr = Hashtbl.find nodes expr
    method get_expr n = Hashtbl.find node_to_expr n
    method get_nodes = Hashtbl.copy nodes

    (** set of equalities*)
    val mutable given_eq = PredSet.empty
    method add_eq eq = given_eq <- PredSet.add eq given_eq
    method was_given_eq eq = PredSet.mem eq given_eq
    method get_given_eq = predSet_to_ordSet given_eq 
    
    (** set of disequalities*)
    val mutable given_neq = PredSet.empty
    method add_neq neq = given_neq <- PredSet.add neq given_neq
    method get_given_neq = predSet_to_ordSet given_neq
    method remove_neq neq = given_neq <- PredSet.remove neq given_neq

    (** creates the node needed for the predicate (expression not given to the constructor)*)
    method create_needed_nodes pred = match pred with
      | Eq (e1, e2) | Not (Eq (e1, e2)) ->
        begin
          ignore( try self#get_node e1 with Not_found -> convert_exp e1);
          ignore( try self#get_node e2 with Not_found -> convert_exp e2);
        end
      | _ -> failwith "Dag: 'create_needed_nodes' only for N/Eq"

    (** add an equality constraint*)
    method add_constr eq = match eq with
      | Eq (e1, e2) ->
        let n1 = self#get_node e1 in
        let n2 = self#get_node e2 in
          self#add_eq eq;
          n1#merge n2
      | _ -> failwith "Dag: 'add_constr' only for Eq"

    (** add an equality constraint, create node is needed*)
    method create_and_add_constr eq = match eq with(*TODO buggy*)
      | Eq (e1, e2) ->
        let n1 =
            try self#get_node e1
            with Not_found -> convert_exp e1
        in
        let n2 =
            try self#get_node e2
            with Not_found -> convert_exp e2
        in
          self#add_eq eq;
          n1#merge n2
      | _ -> failwith "Dag: 'create_and_add_constr' only for Eq"

    (** is there a contradiction between what DAG and given '!=' *)
    method neq_contradiction neq = match neq with
      | Not (Eq (e1, e2)) ->
        let n1 = self#get_node e1 in
        let n2 = self#get_node e2 in
          self#add_neq neq;
          n1#find = n2#find
      | _ -> failwith "Dag: 'neq_contradiction' only for Not Eq"


    method is_satisfiable conj =
      let rec split_eq_neq accEq accNeq lst = match lst with
        | (Eq _ as eq)::xs -> split_eq_neq (eq::accEq) accNeq xs
        | (Not (Eq _) as neq)::xs -> split_eq_neq accEq (neq::accNeq) xs
        | [] ->  (accEq,accNeq)
        | c -> failwith ("Dag: only for a conjunction of eq/ne, given:"^(Utils.string_list_cat ", " (List.map print c)))
      in
      match conj with
        | And lst ->
          begin
            let (eq,neq) = split_eq_neq [] [] lst in
              List.iter (self#add_constr) eq;
              not (List.exists self#neq_contradiction neq || self#has_contradiction)
          end
        | Eq _ as eq -> self#add_constr eq; not self#has_contradiction
        | True -> not self#has_contradiction
        | False ->  self#create_and_add_constr (Not (Eq (Constant 0.0, Constant 0.0))); false
        | _ -> failwith "Dag: only for a conjunction of eq/ne"

    (* test if the '!=' are respected and return the failing cstrs*)
    method test_for_contradition =
      let failing = PredSet.filter self#neq_contradiction given_neq in
        predSet_to_ordSet failing

    (* for incremental use *)
    method has_contradiction =
      PredSet.exists self#neq_contradiction given_neq

    (** get a list of list of equal expressions *)
    method get_cc =
      let node_to_cc = Hashtbl.create (Hashtbl.length nodes) in
        Hashtbl.iter (fun e n ->
            let parent = n#find in
            let already =
              try Hashtbl.find node_to_cc parent
              with Not_found -> []
            in
              Hashtbl.replace node_to_cc parent (e::already)
          ) nodes;
        Hashtbl.fold (fun _ cc acc -> cc::acc) node_to_cc []

    (** is given eq true in all cases ?
     *)
    method entailed eq =
      match eq with
      | Eq(e1,e2) ->
        begin
          try
            let n1 = (self#get_node e1)#find in
            let n2 = (self#get_node e2)#find in
              n1 = n2
          with Not_found -> false
        end
      | _ -> failwith "Dag, entailed: expected EQ"

    (** try to get an expr that is equal*)
    method project_expr expr targets =
      List.find (fun x -> self#entailed (Eq (expr, x))) targets

    (** Returns a list of new deduced equalities.
     *  the returned equalities are then put in the set of equalities
     *)
    method new_equalities =
      let new_eq = ref [] in
      let cc = self#get_cc in
        List.iter
          (fun x ->
            ignore (List.fold_left
              (fun acc y ->
                List.iter
                  (fun x ->
                    let eq = order_eq (Eq(x,y)) in
                      if not (self#was_given_eq eq)  then
                        begin
                          self#add_eq eq;
                          new_eq := eq::(!new_eq)
                        end
                  ) acc;
                y::acc
              ) [] x
            )
          ) cc;
        !new_eq


    (** Returns a list a equalities that may change the graph.
     *  This method is for nelson oppen: it is the equalities
     *  that the LI solver needs to check.
     *)
    method relevant_equalites =
      let eqs = ref PredSet.empty in
      let cc = self#get_cc in
        let rec process lst = match lst with
          | _::[] | [] -> ()
          | x::xs ->
            let fxs = List.flatten xs in
              List.iter (
                fun e1 ->
                  List.iter (
                    fun e2 ->
                      let n1 = self#get_node e1 in
                      let n2 = self#get_node e2 in
                      let pairs = n1#may_be_congruent n2 in
                      (*TODO cc_pairs may be a bottle neck...*)
                      let cc_pairs = List.map (fun (x,y) -> (
                            List.hd (List.filter (List.mem (self#get_expr x)) cc),
                            List.hd (List.filter (List.mem (self#get_expr y)) cc)
                          )) pairs
                      in
                      let uniq_cc_pairs = OrdSet.list_to_ordSet cc_pairs in
                        List.iter (
                          fun (x,y) ->
                            List.iter (fun e1 ->
                              List.iter (fun e2 ->
                                  eqs := PredSet.add (order_eq (Eq (e1, e2))) !eqs
                                ) y
                              ) x
                          ) uniq_cc_pairs
                    ) fxs
                ) x;
              process xs
        in
          process cc;
          predSet_to_ordSet !eqs

    (** Tells if the given equalities may change the graph *)
    method is_relevant_equality eq = match eq with
      | Eq (e1,e2) ->
        begin
          let n1 = self#get_node e1 in
          let n2 = self#get_node e2 in
            n1 <> n2
        end
      | err -> failwith ("Dag, is_relevant_equality: found "^(print err))

    (** Returns the 'projection' of the graph on a set of restricted variables.
     *  Assumes that the graph is in a satisfiable state.
     *  @param vars a list of expression considered as the target terms.
     *)
    method project vars =
      let template: (node * node) list ref = ref [] in
        (*makes the templates*)
        PredSet.iter (
          fun x -> match x with 
            | Not (Eq (e1, e2)) ->
              begin
                let n1 = (self#get_node e1)#find in
                let n2 = (self#get_node e2)#find in
                let pair = if n1 < n2 then (n1,n2)
                           else if n2 < n1 then (n2,n1)
                           else failwith "satUIF: project, system is unsat."
                in
                  template := OrdSet.union !template [pair]
              end
            | e -> failwith ("Dag: given_neq contains something strange: "^(print e))
          ) given_neq;
        (*fill one side of the template*)
        let half_instanciated: (expression * node) list ref  = ref [] in
          List.iter (
            fun v ->
              try
                let n = (self#get_node v)#find in
                  List.iter (
                    fun (t1,t2) ->
                      if n = t1 then
                        half_instanciated:= OrdSet.union !half_instanciated [(v,t2)];
                      if n = t2 then
                        half_instanciated:= OrdSet.union !half_instanciated [(v,t1)]
                    ) !template
              with Not_found ->
                () (*new var ??*)
            ) vars;
          (*fill the other side of the template*)
          let instanciated = ref PredSet.empty in
            List.iter (
              fun v ->
                try
                  let n = (self#get_node v)#find in
                    List.iter (
                      fun (e1,t2) ->
                        if n = t2 then
                          instanciated:= PredSet.add (Not (order_eq (Eq (e1,v)))) !instanciated
                      ) !half_instanciated
                with Not_found ->
                  () (*new var ??*)
              ) vars;
            instanciated := PredSet.remove True !instanciated; (*just in case*)
            (*now the eq*)
            let rec process_eq todo = match todo with
              | x::xs ->
                begin 
                  try
                    let n1 = (self#get_node x)#find in
                      List.iter (
                        fun y ->
                          try
                            let n2 = (self#get_node y)#find in
                              if n1 = n2 then
                                instanciated := PredSet.add (order_eq (Eq(x,y))) !instanciated
                          with Not_found -> ()
                      ) xs
                  with Not_found -> ()
                end;
                process_eq xs
              | [] -> ()
            in
              process_eq vars;
              predSet_to_ordSet !instanciated

    method copy =
      let expressions = Hashtbl.fold (fun e _ acc -> e::acc ) nodes [] in
      let cp = new dag expressions in
      let new_of_old = Hashtbl.create (List.length expressions) in
        List.iter (fun e -> Hashtbl.add new_of_old (self#get_node e) (cp#get_node e) ) expressions;
        List.iter (fun e ->
          let new_node = cp#get_node e in
          let old_node = self#get_node e in 
            let new_parent = Hashtbl.find new_of_old (old_node#find) in
              if new_parent <> new_node then new_node#set_parent new_parent
          ) expressions;
        List.iter (cp#add_eq) (self#get_given_eq);(*TODO avoid unnecessary list*)
        List.iter (cp#add_neq) (self#get_given_neq);(*TODO avoid unnecessary list*)
        cp

    method copy_and_extend expr =
      let expressions = Hashtbl.fold (fun e _ acc -> e::acc ) nodes [] in
      let cp = new dag (expressions @ expr) in
      let new_of_old = Hashtbl.create (List.length expressions) in
        List.iter (fun e -> Hashtbl.add new_of_old (self#get_node e) (cp#get_node e) ) expressions;
        List.iter (fun e ->
          let new_node = cp#get_node e in
          let old_node = self#get_node e in 
            let new_parent = Hashtbl.find new_of_old (old_node#find) in
              if new_parent <> new_node then new_node#set_parent new_parent
          ) expressions;
        List.iter (cp#add_eq) (self#get_given_eq);(*TODO avoid unnecessary list*)
        List.iter (cp#add_neq) (self#get_given_neq);(*TODO avoid unnecessary list*)
        cp

    method merge (graph: dag) =
      let expr = Hashtbl.fold (fun e _ acc -> e::acc ) nodes [] in
      let cp = graph#copy_and_extend expr in
        PredSet.iter cp#add_constr given_eq;
        PredSet.iter cp#add_neq given_neq;
        cp

    method print =
      let buffer = Buffer.create 100 in
        Buffer.add_string buffer ("  CC are: "^(Utils.string_list_cat ", "(List.map (fun x -> "["^(Utils.string_list_cat ", " (List.map print_expr x))^"]") self#get_cc)));
        Buffer.add_string buffer "\n  Eq are: ";
        List.iter (fun x -> Buffer.add_string buffer (print x);Buffer.add_string buffer ", ") (self#get_given_eq);
        Buffer.add_string buffer "\n  Neq are: ";
        List.iter (fun x -> Buffer.add_string buffer (print x);Buffer.add_string buffer ", ") (self#get_given_neq);
        Buffer.contents buffer
      
  end

(*TODO refactor -> also somewhere else*)
let rec split_eq_neq accEq accNeq lst = match lst with
  | (Eq _ as eq)::xs -> split_eq_neq (eq::accEq) accNeq xs
  | (Not (Eq _) as neq)::xs -> split_eq_neq accEq (neq::accNeq) xs
  | [] ->  (accEq,accNeq)
  | c -> failwith ("DAG: only for a conjunction of eq/ne, given:"^(Utils.string_list_cat ", " (List.map print c)))


(** breadth first search (shortest path from source to sink): consider equalities as edges *)
let bfs eqs source sink =
  let eq_to_edges eq = match eq with
    | Eq (x,y) -> (x,y)
    | _ -> failwith "Dag: eq_to_edges expects EQ"
  in
  let graph = Utils.edges_to_graph_not_directed (List.map eq_to_edges eqs) in
  let visited = ref ExprSet.empty in
  let queue = Queue.create () in
  let rec search () =
    if Queue.is_empty queue then
      raise Not_found
    else
      begin
        let (n, path) = Queue.pop queue in
          if n = sink then
            n::path
          else if ExprSet.mem n !visited then
            search ()
          else
            begin
              visited := ExprSet.add n !visited;
              let succ = Hashtbl.find graph n in
                List.iter
                  ( fun x ->
                    Queue.push (x, n::path) queue
                  ) succ;
                search ()
            end
      end
  in
    Queue.push (source, []) queue;
    search ()

(** transform a path in a graph (a -> b -> c) into equalities (a=b, b=c) *)
let path_to_eq path =
  let eqs = ref [] in
  let rec process lst = match lst with
    | x::y::xs ->
      begin
        eqs := (order_eq (Eq(x,y)))::!eqs;
        process (y::xs)
      end
    | _::[] -> ()
    | [] -> ()
  in
    process path;
    !eqs

let interpolate_from_graph graph_a graph_b =
  Message.print Message.Debug (lazy("graph A:\n"^graph_a#print));
  Message.print Message.Debug (lazy("graph B:\n"^graph_b#print));

  let find_proof neq eqs = match neq with
     | Not (Eq(e1,e2)) ->
       begin
         let path = bfs eqs e1 e2 in
           path_to_eq path
       end
     | _ -> failwith "Dag: find_proof"
  in

    match (graph_a#has_contradiction, graph_b#has_contradiction) with
    | (true,_) ->
      begin
        Message.print Message.Debug (lazy "contradiction in A");
        False
      end
    | (_,true) ->
      begin
        Message.print Message.Debug (lazy "contradiction in B");
        True
      end
    | (false,false) ->
      begin
        let a_expr = OrdSet.list_to_ordSet (List.flatten graph_a#get_cc) in
        let b_expr = OrdSet.list_to_ordSet (List.flatten graph_b#get_cc) in
        let common_expr = OrdSet.intersection a_expr b_expr in
        
        let (proj_a_eq,proj_a_neq) = split_eq_neq [] [] (graph_a#project common_expr) in
        let (proj_b_eq,proj_b_neq) = split_eq_neq [] [] (graph_b#project common_expr) in

        let graph_common = new dag common_expr in
          if graph_common#is_satisfiable (And (proj_a_eq @ proj_a_neq @ proj_b_eq @ proj_b_neq)) then
            raise SAT
          else
            begin
              (*one neq that isn't true*)
              let brocken = List.hd (graph_common#test_for_contradition) in
              let path = find_proof brocken (proj_a_eq @ proj_b_eq) in
              let a_eq = List.filter (graph_a#entailed) path in
                if List.mem brocken proj_a_neq then
                  begin
                    And (brocken::a_eq)
                  end
                else
                  begin
                    assert (Global.is_off_assert() || List.mem brocken proj_b_neq);
                    And a_eq
                  end
            end
      end

(*without preexisting graphs*)
let interpolate_eq a b =
  let a_expr = get_expr a in
  let b_expr = get_expr b in

  let graph_a = new dag a_expr in
  let graph_b = new dag b_expr in
    ignore (graph_a#is_satisfiable a, graph_b#is_satisfiable b);
    interpolate_from_graph graph_a graph_b

let find_common_expr_graph expr_a expr_b graph_a graph_b common_var common_sym =
  let eqs = (graph_a#get_given_eq @ graph_b#get_given_eq) in
  let path = bfs eqs expr_a expr_b in
  let is_cst e = match e with
    | Constant _ -> true
    | _ -> false
  in
    try
      List.find (fun x -> (not (is_cst x)) && (only_vars_and_symbols common_var common_sym (Eq(x,Constant 0.0)))) path
    with Not_found ->
      List.find (fun x -> only_vars_and_symbols common_var common_sym (Eq(x,Constant 0.0))) path

let find_common_expr expr_a expr_b eqs common_var common_sym =
  let path = bfs eqs expr_a expr_b in
  let is_cst e = match e with
    | Constant _ -> true
    | _ -> false
  in
    try
      List.find (fun x -> (not (is_cst x)) && (only_vars_and_symbols common_var common_sym (Eq(x,Constant 0.0)))) path
    with Not_found ->
      List.find (fun x -> only_vars_and_symbols common_var common_sym (Eq(x,Constant 0.0))) path

let unsat_core formula =
  let expr = get_expr formula in
  let graph = new dag expr in
    if (graph#is_satisfiable formula) then 
      raise (SAT_FORMULA formula)
    else
      begin
        match List.hd (graph#test_for_contradition) with
        | Not (Eq(e1,e2)) as neq ->
          begin
            let formula_lst = match formula with
              | And lst -> lst
              | _ -> failwith "Dag: unsat_core (1)"
            in
            let (eqs,_) = split_eq_neq [] [] formula_lst in
            let path = bfs eqs e1 e2 in
              And (neq::(path_to_eq path))
          end
        | _ -> failwith "Dag: unsat_core (2)"
      end

(*experimantal code*)
(*TODO tests*)
let interpolate_eq_lst common_var common_sym lst =
  let common_var = Array.of_list common_var in
  let common_sym = Array.of_list common_sym in
  
  let find_proof neq eqs = match neq with
     | Not (Eq(e1,e2)) ->
       begin
         let path = bfs eqs e1 e2 in
           path_to_eq path
       end
     | _ -> failwith "Dag: find_proof"
  in

  let exprs = List.map get_expr_set lst in
  let (cumulative_expr,graphs) =
    let (_,_,cumulative_expr,gr) = List.fold_left2
      (fun (exprs,formula_lst,accExpr,accGr) expr lst ->
        let exprs = ExprSet.union exprs expr in
        let exprs_lst = exprSet_to_ordSet exprs in
        let graph = new dag exprs_lst in
        let formula = normalize_only (And [lst;formula_lst]) in
        let _ = graph#is_satisfiable formula in
          (exprs, formula, exprs::accExpr,graph::accGr)
      )
      (ExprSet.empty,True,[],[]) exprs lst
    in
      (Array.of_list (List.rev cumulative_expr), Array.of_list (List.rev gr))
  in

  let graph = graphs.((Array.length graphs) -1) in
    if not (graph#has_contradiction) then 
      raise SAT
    else
      begin
        let brocken = List.hd (graph#test_for_contradition) in
        let brocken_eq = match brocken with
          |Not (Eq _ as eq) -> eq
          | _ -> failwith "Dag, interpolate_eq_lst (1)"
        in
        let eqs = List.map (fun l -> match l with
            | And conj -> List.filter (fun x -> match x with Eq _ -> true | _ -> false) conj
            | Eq _ as eq -> [eq]
            | _ -> []
          ) lst
        in
        let path = find_proof brocken (List.flatten eqs) in
        let its = Array.make ((Array.length graphs) -1) True in
          for i = 0 to (Array.length its) -1 do
            let graph = graphs.(i) in
              if graph#entailed brocken_eq then
                its.(i) <- False
              else
                begin
                  let local_path = List.filter (fun eq -> graph#entailed eq) path in
                  let expr =
                    ExprSet.filter
                      (fun x -> only_vars_and_symbols common_var.(i) common_sym.(i) (Eq(x,Constant 0.0)))
                      cumulative_expr.(i) 
                  in
                  let expr_lst = exprSet_to_ordSet expr in
                  let common =
                    List.map
                      (fun eq -> match eq with
                        | Eq (e1,e2) ->
                          order_eq
                            (Eq(graph#project_expr e1 expr_lst,
                                graph#project_expr e2 expr_lst))
                        | _ -> failwith "Dag, interpolate_eq_lst (2)"
                      )
                      local_path
                  in
                    its.(i) <- (And common)
                end
          done;
          Array.to_list its
      end

