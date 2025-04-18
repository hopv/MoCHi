open Util
open! Mochi_util
module IdMap = IntMap

type debug = { debug_label : label; debug_problem : Problem.t; debug_args : string list }

(**
  --- ABOUT PREPROCESS TREE ---
  A "preprocess tree" is a tree that represents all the process of preprocessing.
  The initial proprocess tree just consists of the initial problem, i.e.,
  the input problem before preprocessing, and the list of preprocessing functions.
  By `run_one_step` and `run` functions, a proprocess tree is expanded until
  "ready instance" is generated. Here, "ready instance" means a problem to which all
  the preprocessing are applied. A preprocess tree is expanded in the depth-first manner.
  Children are not calculated/generated simultaneously. Instead children are generated
  one-by-one by [next] function.

  Functions in [pullback] calculate refinement types and counterexamples from those of childrens.
  If [make_get_rtyp] (resp. [trans_cex]) is [None], then it means that the preprocess does not change
  refinement types (resp. counterxamples).

  TODO: Current implementation does not support a preprocess that flips the result
  (i.e., the safety of the translated program means the unsafety of the original program)
*)

and t = label * (descr * trans)
(** Type of one preprocessing
    [label]: The label of the preprocess, which is used to refer the prepprocess
    [descr]: The description of the preprocess. The description must be unique in the list of preprocesses.
             This is also used for options (e.g., -stop-after)
    [trans]: The actual function of the prepprocess
 *)

and trans = op * (problem -> pullback * (trans_result * next option) option)
(** Type of a single preprocessing
    [op]: The meaning of branches (all the children must be safe or one of the children must be safe)*)

and next = Trans of (history -> (trans_result * next option) option)
and history = (info * verif_result) list
and trans_result = info * problem

and verif_result =
  | Safe of Trans.get_rtyp [@printer fun fm _ -> Format.fprintf fm "Safe"]
  | Unsafe of counterexample
  | Unknown of string

and counterexample = {
  vals_main : vals_main Lazy.t;
  orig : mc_cex; (* Original counterexample generated by [Model_check.check] *)
}

(* for pretty-printing *)
and term = (Syntax.term[@printer Print.term])
and mc_cex = (Model_check.counterexample[@printer fun fm _ -> Format.fprintf fm "cex"])
and info = (Syntax.prep_info option[@printer fun fm _ -> Format.fprintf fm "info"])
and pullback = { make_get_rtyp : make_get_rtyp option; trans_cex : trans_cex option }
and make_get_rtyp = (Trans.make_get_rtyp[@printer fun fm _ -> Format.fprintf fm "Get_rtyp"])
and cex_values = term list (* Sequence of values generated by rand *)

and trans_cex =
  (* TODO: arguments must have translated problems *)
  (id * info * vals_main Lazy.t) list ->
  vals_main

and vals_main =
  cex_values (* List of values generated by rand() *) * term option (* term that reaches failure *)

and tree = Before of node | After of after_label

and after_label = {
  node : node;
  label : label;  (** Label of preprocess *)
  descr : descr;  (** Short description of preprocess *)
  op : op;  (** How to calculate the result from those of the children *)
  next : next option;  (** Generator of the next child *)
  children : tree list;  (** Head is the latest result *)
  pullback : pullback;
      (** How to calculate certificates/counterexamples from those of the children *)
}

and id = int
and descr = string
and problem = Problem.t
and op = And | Or
and path = node list

and node = {
  id : int;
  time : float;  (** Time of creation *)
  info : info;
      (** Information of the result
          (e.g., what parameter was used, what was the target function, etc.) *)
  problem : problem;  (** original problem *)
  rest : t list;
}
(** List of preprocessing which will be applied to [problem] *)

and ready = id * info * problem
and results = ((info * verif_result) IdMap.t[@printer fun fm _ -> Format.fprintf fm "results"])

and label =
  | Init
  | Ref_type_pred_type_check
  | Set_main
  | Eliminate_unused_let
  | Replace_const
  | Lift_type_decl
  | Inline_record_type
  | Encode_lazy
  | Encode_mutable_record
  | Encode_record
  | Encode_array
  | Abst_ref
  | Abst_object
  | Make_fun_tuple
  | Rename_target_ext_funs
  | Make_ext_funs
  | Copy_poly_values
  | Copy_poly_type
  | Ignore_non_termination
  | Eliminate_redundant_arguments
  | Recover_const_attr
  | Decomp_pair_eq
  | Add_preds
  | Add_preds_CPS
  | Replace_fail_with_raise
  | Ignore_data_arg
  | Ignore_excep_arg
  | Ignore_excep_fun_arg
  | Ignore_mutual_data_arg
  | Encode_recdata
  | Encode_option
  | Replace_base_with_int
  | Replace_list_with_int
  | Replace_data_with_int
  | Replace_data_with_int_but_exn
  | Abstract_exn
  | Inline_type_decl
  | Encode_list
  | Abst_div
  | Ret_fun
  | Ref_trans
  | Tupling
  | Inline
  | Mark_safe_fun_arg
  | CPS
  | Remove_pair
  | Replace_bottom_def
  | Add_cps_preds
  | Eliminate_same_arguments
  | Insert_unit_param
  | Extract_module
  | Remove_ext_typ
  | Inline_functor
  | Mark_fv_as_external
  | Alpha_rename
  | Instansiate_weak_poly_types
  | Abst_recursive_record
  | Inline_simple_types
  | Abst_polymorphic_comparison
  | Abst_literal
  | Encode_bool_as_int
  | Reduce_rand
  | Reduce_ignore
  | Reduce_branch
  | Split_assert
  | Insert_extra_param
  | Replace_complex_data_with_int
  | Variant_args_to_tuple
  | Unify_pure_fun_app
  | Add_occurence_param
  | Slice
  | Split_by_ref_type
  | Slice_top_fun
  | Set_main_sliced
  | Merge_deref
  | Elim_unused_assumption
  | Set_to_primitive
  | Inline_exn_type
  | Inline_type_alias
  | Inline_ext_rebind
  | Abstract_first_class_module
  | Abstract_magical_functions
  | Add_external_types
  | Replace_abst_with_int
  | Instansiate_matched_poly
  | Abstract_polymorphic_variant
  | Abstract_GADT
  | Extract_include
  | Make_bind_for_PAlias
  | Inline_tvar
  | Encode_enum_variant
  | Encode_nonrec_variant
  | Reduce_fail_free
  | Abstract_menhir
  | Add_ref_check
  | Reduce_external
  | Merge_branch
[@@deriving show { with_path = false }]

let pp_results fm (results : results) =
  results
  |> IntMap.bindings
  |> Format.fprintf fm "%a" Print.(list (int * (pp_info * pp_verif_result)))

let ( +++ ) x y = IdMap.union (fun _ _ _ -> assert false) x y
let measure_time f t = Time.measure_and_add Flag.Log.Time.preprocess f t

module Node = struct
  let id { id } = id
  let info { info } = info
  let problem { problem } = problem
  let rest { rest } = rest
end

module Path = struct
  let assoc_id_opt id p = List.find_opt (fun node -> node.id = id) p

  let rec assoc_label_opt label p =
    match p with
    | [] -> None
    | { rest = (label', _) :: _ } :: p' when label = label' -> Some (List.hd p')
    | _ :: p' -> assoc_label_opt label p'
end

let id_pullback = { make_get_rtyp = None; trans_cex = None }
let node_of_root tree = match tree with Before node | After { node } -> node
let id_of_root tree = (node_of_root tree).id
let problem_of_root tree = (node_of_root tree).problem

let rec find_label target tree =
  match tree with
  | Before _ -> []
  | After { label; children } ->
      if label = target then [ tree ] else List.flatten_map (find_label target) children

let id : trans = (And, fun _ -> (id_pullback, None))
let if_ b (tr : trans) : trans = if b then tr else id

let map_lazy_list_gen ?(op = And) (tr : Problem.t -> pullback option * ('a * Problem.t) LazyList.t)
    (map_info : 'a -> info) : trans =
  ( op,
    fun p ->
      match tr p with
      | pullback, (lazy (Cons (r, ps'))) ->
          let map_result (info, p) = (map_info info, p) in
          let rec next ps _ =
            match !?ps with
            | LazyList.Nil -> None
            | Cons (r, ps') -> Some (map_result r, Some (Trans (next ps')))
          in
          (Option.default id_pullback pullback, Some (map_result r, Some (Trans (next ps'))))
      | _ -> assert false )

let map_lazy_list_with_info ?(op = And)
    (tr : Problem.t -> (Syntax.prep_info * Problem.t) LazyList.t) : trans =
  let tr' p = (None, tr p) in
  map_lazy_list_gen ~op tr' Option.some

let map_lazy_list ?(op = And) (tr : Problem.t -> Problem.t LazyList.t) : trans =
  let tr' p = (None, LazyList.map (fun x -> (None, x)) @@ tr p) in
  map_lazy_list_gen ~op tr' Fun.id

let map_list_gen ?(op = And) (tr : Problem.t -> pullback option * ('a * Problem.t) list)
    (map_info : 'a -> info) : trans =
  ( op,
    fun p ->
      match tr p with
      | pullback, r :: ps ->
          let map_result (info, p) = (map_info info, p) in
          let rec next ps _ =
            match ps with
            | [] -> None
            | r :: ps' ->
                let next' = if ps' = [] then None else Some (Trans (next ps')) in
                Some (map_result r, next')
          in
          (Option.default id_pullback pullback, Some (map_result r, Some (Trans (next ps))))
      | _ -> assert false )

let map_list_with_info ?(op = And) (tr : Problem.t -> (Syntax.prep_info * Problem.t) list) : trans =
  let tr' p = (None, tr p) in
  map_list_gen ~op tr' Option.some

let map_list ?(op = And) (tr : Problem.t -> Problem.t list) : trans =
  let tr' p = (None, List.map (Pair.pair None) @@ tr p) in
  map_list_gen ~op tr' Fun.id

let none_if_equal p p' = (id_pullback, if p = p' then None else Some ((None, p'), None))
let map (tr : Problem.t -> Problem.t) : trans = (And, fun p -> none_if_equal p (tr p))

let map_term (tr : Syntax.term -> Syntax.term) : trans =
  (And, fun p -> none_if_equal p (Problem.map tr p))

let map_option (tr : Problem.t -> Problem.t option) : trans =
  (And, fun p -> match tr p with None -> (id_pullback, None) | Some p' -> none_if_equal p p')

let map_list_option (tr : Problem.t -> Problem.t LazyList.t option) : trans =
  ( And,
    fun p ->
      ( id_pullback,
        match tr p with
        | None -> None
        | Some (lazy Nil) -> assert false
        | Some (lazy (Cons (p', ps))) ->
            let rec next ps _ =
              match Lazy.force ps with
              | LazyList.Nil -> None
              | Cons (p'', ps') -> Some ((None, p''), Some (Trans (next ps')))
            in
            Some ((None, p'), Some (Trans (next ps))) ) )

let map_with_get_rtyp (tr : Problem.t -> Problem.t * Trans.make_get_rtyp_single) : trans =
  ( And,
    fun p ->
      let p', make = tr p in
      if p = p' then (id_pullback, None)
      else
        let make_get_rtyp = Some (List.get |- make) in
        let pullback = { make_get_rtyp; trans_cex = None } in
        (pullback, Some ((None, p'), None)) )

let map_with_trans_cex (tr : Problem.t -> Problem.t * trans_cex) : trans =
  ( And,
    fun p ->
      let p', trans = tr p in
      if p = p' then (id_pullback, None)
      else
        let pullback = { make_get_rtyp = None; trans_cex = Some trans } in
        (pullback, Some ((None, p'), None)) )

let assoc label pps = List.find (( = ) label -| fst) pps
let before label (pps : t list) = List.takewhile (( <> ) label -| fst) pps
let before_and label (pps : t list) = List.takewhile (( <> ) label -| fst) pps @ [ assoc label pps ]
let and_after label (pps : t list) = List.dropwhile (( <> ) label -| fst) pps
let after label (pps : t list) = List.tl @@ and_after label pps

let split label (pps : t list) =
  let pps1, pps2 = List.takedrop_while (( <> ) label -| fst) pps in
  (pps1, snd (List.hd pps2), List.tl pps2)

let filter_out labels pps = List.filter_out (fst |- List.mem -$- labels) pps

let get_path_of id tree : path =
  let rec get acc_rev k tree : path option =
    let acc_rev' = node_of_root tree :: acc_rev in
    match tree with
    | (Before node | After { node }) when node.id = k -> Some (List.rev acc_rev')
    | Before _ -> raise Not_found
    | After { children } -> List.find_map_opt (get acc_rev' k) children
  in
  match get [] id tree with None -> raise Not_found | Some p -> p

let rec get_leaves tree =
  match tree with
  | Before node -> [ node ]
  | After { node } when node.rest = [] -> [ node ]
  | After { children } -> List.rev_flatten_map get_leaves children
