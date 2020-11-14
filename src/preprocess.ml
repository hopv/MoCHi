open Util
open Mochi_util

module Debug_ty = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".ty") end)
module Debug_tree = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".tree") end)
module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type debug = {debug_label:label; debug_problem:Problem.t; debug_args:string list}

and preprocess = label * tr
and tr = Problem.t -> tr_result option
and tr_result = op * problem LazyList.t

and tree =
  | Before of problem
  | After of {id : int;
              time : float;
              label : label;
              no_change : bool;
              problem : problem;
              op : op;
              result : tree LazyList.t}

and problem = Problem.t * get_rtyp
and get_rtyp = (Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t
and op = And | Or
and path = (label * problem) list

and label =
  | Init
  | Ref_type_pred_type_check
  | Set_main
  | Eliminate_unused_let
  | Replace_const
  | Lift_type_decl
  | Inline_record_type
  | Encode_mutable_record
  | Encode_record
  | Encode_array
  | Abst_ref
  | Make_fun_tuple
  | Rename_target_ext_funs
  | Make_ext_funs
  | Copy_poly
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
  | Encode_simple_variant
  | Encode_recdata
  | Encode_option
  | Replace_base_with_int
  | Replace_list_with_int
  | Replace_data_with_int
  | Replace_data_with_int_but_exn
  | Abstract_exn
  | Inline_type_decl
  | Encode_list
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
  | Inline_functor
  | Remove_open
  | Mark_fv_as_external
  | Alpha_rename
  | Instansiate_poly_types
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

let string_of_label = function
  | Init -> "Init"
  | Ref_type_pred_type_check -> "Type check of refinement type predicates"
  | Set_main -> "Set main"
  | Eliminate_unused_let -> "Eliminate unused let"
  | Replace_const -> "Replace const"
  | Lift_type_decl ->  "Lift type decl"
  | Inline_record_type -> "Inline record type"
  | Encode_mutable_record -> "Encode mutable record"
  | Encode_record -> "Encode record"
  | Encode_option -> "Encode option"
  | Encode_array -> "Encode array"
  | Abst_ref -> "Abst ref"
  | Make_fun_tuple -> "Make fun tuple"
  | Rename_target_ext_funs -> "Rename target external functions"
  | Make_ext_funs -> "Generate external function"
  | Copy_poly -> "Copy poly"
  | Ignore_non_termination -> "Ignore non termination"
  | Eliminate_redundant_arguments -> "Eliminate redundant arguments"
  | Recover_const_attr -> "Recover const attr"
  | Decomp_pair_eq -> "Decomp pair eq"
  | Add_preds -> "Add preds"
  | Add_preds_CPS -> "Add preds CPS"
  | Replace_fail_with_raise -> "Replace fail with raise"
  | Ignore_data_arg -> "Ignore arguments of data type constructors"
  | Ignore_excep_arg -> "Ignore arguments of exceptions"
  | Ignore_excep_fun_arg -> "Ignore function arguments of exceptions"
  | Encode_simple_variant -> "Encode simple variant"
  | Encode_recdata -> "Encode recdata"
  | Replace_base_with_int -> "Replace base with int"
  | Replace_list_with_int -> "Replace lists with int"
  | Replace_data_with_int -> "Replace data with int"
  | Replace_data_with_int_but_exn -> "Replace data with int except exceptions"
  | Replace_complex_data_with_int -> "Replace non-regular data with int"
  | Abstract_exn -> "Abstract exceptions"
  | Inline_type_decl -> "Inline type decl"
  | Encode_list -> "Encode list"
  | Ret_fun -> "Ret fun"
  | Ref_trans -> "Ref trans"
  | Tupling -> "Tupling"
  | Inline -> "Inline"
  | Mark_safe_fun_arg -> "Mark safe fun arg"
  | CPS -> "CPS"
  | Remove_pair -> "Remove pair"
  | Replace_bottom_def -> "Replace bottom def"
  | Add_cps_preds -> "Add cps preds"
  | Eliminate_same_arguments -> "Eliminate same arguments"
  | Insert_unit_param -> "Insert unit param"
  | Extract_module -> "Extract module"
  | Inline_functor -> "Inline functor"
  | Remove_open -> "Remove open"
  | Mark_fv_as_external -> "Mark free variables as external"
  | Alpha_rename -> "Alpha renaming"
  | Instansiate_poly_types -> "Instansiate polymorphic types"
  | Abst_recursive_record -> "Abst recursive record"
  | Inline_simple_types -> "Inline simple types"
  | Abst_polymorphic_comparison -> "Abst polymorphic comparison"
  | Abst_literal -> "Abst literal"
  | Encode_bool_as_int -> "Encode bool as int"
  | Reduce_rand -> "Reduce rand"
  | Reduce_ignore -> "Reduce ignore"
  | Reduce_branch -> "Reduce branch"
  | Split_assert -> "Split assert"
  | Insert_extra_param -> "Insert extra parameters"
  | Variant_args_to_tuple -> "Replace variant arguments with tuples"
  | Unify_pure_fun_app -> "Unify applications of pure functions"
  | Add_occurence_param -> "Add occurence parameters"
  | Slice -> "Slice"
  | Split_by_ref_type -> "Split by refinement types"
  | Slice_top_fun -> "Slice by top-level function definitions"
  | Set_main_sliced -> "Set main for slice"
  | Merge_deref -> "Merge derefences"
  | Elim_unused_assumption -> "Eliminate unused assumptions"
  | Set_to_primitive -> "Translate set functions to primitive operations"

let measure_time f t = Time.measure_and_add Flag.Log.Time.preprocess f t

let rec get r =
  match r with
  | Before(p,_) -> Problem.term p
  | After {result} ->
      match LazyList.next result with
      | Cons(r, rs) when LazyList.is_empty rs -> get r
      | _ -> unsupported "Multiple targets"

let rec exists_or r =
  match r with
  | Before _ -> false
  | After {op=And; result} -> LazyList.exists exists_or result
  | After {op=Or; result} when LazyList.is_singleton result -> exists_or @@ LazyList.hd result
  | After {op=Or} -> true

let rec list_of_leaves r =
  match r with
  | Before pg -> [pg]
  | After {op=And; result} -> List.flatten_map list_of_leaves @@ LazyList.to_list result
  | After {op=Or; result} when LazyList.is_singleton result -> list_of_leaves @@ LazyList.hd result
  | After {op=Or} -> unsupported "Multiple targets"

let rec lists_of_paths r =
  match r with
  | Before problem -> [[Init, problem]]
  | After {label; problem; op=And; result} ->
      result
      |> LazyList.to_list
      |> List.flatten_map lists_of_paths
      |> List.map (List.cons (label, problem))
  | After {label; problem; op=Or; result} when LazyList.is_singleton result ->
      let r = LazyList.hd result in
      List.map (List.cons (label, problem)) @@ lists_of_paths r
  | After {op=Or} -> unsupported "Multiple targets"

let last (acc:path) = snd @@ List.hd acc
let last_problem (acc:path) = fst @@ last acc
let last_get_rtyp (acc:path) = snd @@ last acc
let take_result l (acc:path) = fst @@ List.assoc l acc

let get_rtyp_id get_rtyp f = get_rtyp f
let with_get_rtyp_id ?(op=And) problems = Some (op, LazyList.map (Pair.pair -$- get_rtyp_id) problems)

let if_ b (tr:tr) x : tr_result option = if b then tr x else None
let map_list ?(op=And) (tr:Problem.t->Problem.t LazyList.t) r : tr_result option = Some (op, LazyList.map (Pair.pair -$- get_rtyp_id) @@ tr r)
let map tr = map_list (tr |- LazyList.singleton)
let map_term tr = map_list (Problem.map tr |- LazyList.singleton)
let map_option (tr : Problem.t -> Problem.t option) problem =
  match tr problem with
  | None -> None
  | Some problem' -> Some (And, LazyList.singleton (problem', get_rtyp_id))
let map_list_option (tr : Problem.t -> Problem.t LazyList.t option) problem =
  match tr problem with
  | None -> None
  | Some problems -> Some (And, LazyList.map (Pair.pair -$- get_rtyp_id) problems)
let singleton tr = Option.some -| Pair.pair And -| LazyList.singleton -| tr
let exists tr : tr = Option.some -| Pair.pair Or -| tr

let assoc label pps =
  List.find ((=) label -| fst) pps

let before label (pps:preprocess list) =
  List.takewhile ((<>) label -| fst) pps

let before_and label (pps:preprocess list) =
  List.takewhile ((<>) label -| fst) pps @ [assoc label pps]

let and_after label (pps:preprocess list) =
  List.dropwhile ((<>) label -| fst) pps

let after label (pps:preprocess list) =
  List.tl @@ and_after label pps

let split label (pps:preprocess list) =
  let pps1,pps2 = List.takedrop_while ((<>) label -| fst) pps in
  pps1, snd (List.hd pps2), List.tl pps2

let filter_out labels pps =
  List.filter_out (fst |- List.mem -$- labels) pps

let all () : preprocess list =
  let open Trans_problem in
  [
    Init,
      Fun.const None;
    Remove_open,
      map_term Module.remove_open;
    Set_to_primitive,
      if_ !Flag.Method.use_set_theory @@
      map_term Trans.set_to_primitive;
    Inline_functor,
      map_term Module.inline_functor;
    Extract_module,
      map_term Module.extract;
    Instansiate_poly_types,
      map_term Trans.instansiate_poly_types;
    Ref_type_pred_type_check,
      map Ref_type_pred_typing.ref_type_pred_typing;
    Set_main,
      map_list set_main;
    Split_by_ref_type,
      map_list_option split_by_ref_type;
    Eliminate_unused_let,
      map_list ~op:Or elim_unused_let;
    Mark_fv_as_external,
      map_term Trans.mark_fv_as_external;
    Insert_extra_param,
      if_ !Flag.Method.relative_complete @@
      map_term Trans.insert_extra_param;
    Encode_bool_as_int,
      if_ !Flag.Encode.bool_to_int @@
      map_term Trans.encode_bool_as_int;
    Replace_const,
      if_ !Flag.Method.replace_const @@
      map CFA.replace_const;
    Lift_type_decl,
      map_term Trans.lift_type_decl;
    Rename_target_ext_funs,
      map rename_target_ext_funs;
    Copy_poly,
      singleton copy_poly_funs;
    Slice_top_fun,
      if_ !Flag.Method.sub @@
      map_list ~op:Or slice_top_fun;
    Set_main_sliced,
      if_ !Flag.Method.sub @@
      map_list set_main_for_slice;
    Elim_unused_assumption,
      map elim_unused_assumption;
    Encode_mutable_record,
      map Encode.mutable_record;
    Inline_simple_types,
      map inline_simple_types;
    Abst_recursive_record,
      map Encode.abst_rec_record;
    Inline_record_type,
      map inline_record_type;
    Encode_record,
      map Encode.record;
    Encode_array,
      map Encode.array;
    Merge_deref,
      map_term Trans.merge_deref;
    Abst_ref,
      map Encode.abst_ref;
    Make_fun_tuple,
      if_ !Flag.Method.tupling @@
      map @@ Problem.map Ref_trans.make_fun_tuple;
    Ignore_non_termination,
      if_ !Flag.Method.ignore_non_termination @@
      map_term Trans.ignore_non_termination;
    Eliminate_redundant_arguments,
      if_ !Flag.Method.elim_redundant_arg @@
      map_term Trans.elim_redundant_arg;
    Recover_const_attr,
      map_term Trans.recover_const_attr;
    Decomp_pair_eq,
      map_term Trans.decomp_pair_eq;
    Add_preds,
      map_option (add_preds Spec.get_abst_env);
    Replace_data_with_int_but_exn,
      if_ !Flag.Abstract.data_to_int_but_exn @@
      map replace_data_with_int_but_exn;
    Abstract_exn, (* TODO: trans env *)
      (* Must precede Encode_simple_variant, Replace_data_with_int *)
      if_ !Flag.Abstract.exn_to_bool @@
      map_term Trans.abstract_exn;
    Ignore_data_arg,
      if_ !Flag.Abstract.ignore_data_arg @@
      map_term Encode.ignore_data_arg;
    Ignore_excep_arg,
      if_ !Flag.Abstract.ignore_exn_arg @@
      map_term Encode.ignore_exn_arg;
    Ignore_excep_fun_arg,
      map_term Encode.ignore_exn_fun_arg;
    Make_ext_funs,
      if_ (not !Flag.Method.encode_before_make_ext_fun) @@
      map make_ext_funs;
    Encode_simple_variant,
      map Encode.simple_variant;
    Replace_base_with_int,
      if_ Flag.Abstract.(!base_to_int || !data_to_int) @@
      map replace_base_with_int;
    Inline_simple_types,
      map inline_simple_types;
    Replace_data_with_int,
      if_ !Flag.Abstract.list_to_int @@
      map replace_list_with_int;
    Replace_data_with_int,
      if_ !Flag.Abstract.data_to_int @@
      map replace_data_with_int;
    Replace_complex_data_with_int, (* TODO: trans env *)
      if_ !Flag.Abstract.complex_data_to_int @@
      map_term Trans.replace_complex_data_with_int;
    Inline_simple_types,
      map inline_simple_types;
    Encode_recdata,
      map Encode.recdata;
    Encode_option,
      map Encode.option;
    Inline_type_decl,
      map_term Trans.inline_type_decl;
    Abst_literal,
      map_term Trans.abst_literal;
    Encode_list,
      singleton Encode.list;
    Unify_pure_fun_app,
      map_term Trans.unify_pure_fun_app;
    Ret_fun,
      if_ !Flag.Method.tupling @@
      singleton @@ Problem.map_on Focus.fst Ret_fun.trans;
    Ref_trans,
      if_ !Flag.Method.tupling @@
      singleton @@ Problem.map_on Focus.fst Ref_trans.trans;
    Tupling,
      if_ !Flag.Method.tupling @@
      singleton @@ Problem.map_on Focus.fst Tupling.trans;
    Inline,
      map inline;
    Make_ext_funs,
      if_ !Flag.Method.encode_before_make_ext_fun @@
      map make_ext_funs;
    Reduce_rand,
      map_term Trans.reduce_rand;
    Reduce_ignore,
      map_term Trans.reduce_ignore;
    Reduce_branch,
      map_term Trans.reduce_branch;
    Split_assert,
      if_ !Flag.Method.split_assert @@
      map_list split_assert;
    Mark_safe_fun_arg,
      if_ !Flag.PredAbst.shift_pred @@
      map @@ Problem.map Effect.mark_safe_fun_arg;
    Abst_polymorphic_comparison,
      map Encode.abst_poly_comp;
    Variant_args_to_tuple,
      map_term Trans.variant_args_to_tuple;
    Slice,
      if_ !Flag.Method.slice @@
      map_term Slice.slice;
    CPS,
      if_ !Flag.Mode.trans_to_CPS @@
      singleton CPS.trans;
    Remove_pair,
      if_ !Flag.Mode.trans_to_CPS @@
      singleton Curry.remove_pair;
    Add_occurence_param,
      if_ !Flag.Method.occurence_param @@
      map_term Trans.add_occurence_param;
    Replace_bottom_def,
      map_term Trans.replace_bottom_def;
    Add_preds_CPS,
      map_option (add_preds Spec.get_abst_cps_env);
    Eliminate_same_arguments,
      if_ !Flag.Method.elim_same_arg @@
      map @@ Problem.map Elim_same_arg.trans;
    Insert_unit_param,
      if_ !Flag.Method.insert_param_funarg @@
      map_term Trans.insert_param_funarg;
    Alpha_rename,
      if_ Flag.(!mode <> Termination) @@
      singleton alpha_rename;
  ]

let pr () = if !!Debug_ty.check then Problem.print_debug else Problem.print
let print s_id desc problem = Verbose.printf "%a###[%.3f]%s%t %a:@. @[%a@.@." Color.set Color.Green !!Time.get s_id Color.reset Color.s_red desc !!pr problem

let print_log_tree fm t =
  let rec pr indent first last t =
    let indent' =
      if last then
        indent ^ "   "
      else
        indent ^ "│  "
    in
    let head =
      if first then
        ""
      else if last then
        "└─"
      else
        "├─"
    in
    match t with
    | Before _ -> ()
    | After {result} when not @@ Lazy.is_val result ->
        Format.fprintf fm "%s%s(delayed)@\n" indent head;
    | After {label; no_change; result} when label <> Init && no_change && not !!Debug_tree.check ->
        pr indent false last @@ List.get @@ LazyList.to_list result
    | After {id; time; label; result} ->
        let children =
          let rec aux result =
            if Lazy.is_val result then
              match Lazy.force result with
              | LazyList.Nil -> []
              | LazyList.Cons(t',result') -> t'::aux result'
            else
              []
          in
          aux result
        in
        let len = List.length children in
        Format.fprintf fm "%s%s[#%d %a@@ %.3f%t] %s@\n" indent head id Color.set Color.Green time Color.reset @@ string_of_label label;
        List.iteri (fun i t -> pr indent' false (i=len-1) t) children
  in
  pr "" true true t

let check_type problem =
  let t =
    Problem.term problem
    |> Term_util.add_mark
  in
  try
    Type_check.check t ~ty:t.Syntax.typ
  with e ->
    Color.eprintf Color.Red "Type-check failed: %s@." @@ Printexc.to_string e;
    Format.eprintf "%a@.@." Print.term_typ t;
    Format.eprintf "%a@.@." Print.term' t;
    Format.eprintf "%a@.@." Syntax.pp_typ (t.Syntax.typ);
    assert false

let check_fv before after =
  let get_fv p =
    let fv_term = Term_util.get_fv @@ Problem.term p in
    let ext_funs = List.map Triple.fst (Problem.spec p).Spec.ext_ref_env in
    List.Set.diff ~eq:Id.eq fv_term ext_funs
  in
  let fv =
    List.Set.diff ~eq:Id.eq (get_fv after) (get_fv before)
    |> List.filter_out Id.is_external
  in
  if fv <> [] then
    begin
      Color.eprintf Color.Red "FV-check failed:@.";
      Format.eprintf "  %a@.@." Print.term_typ (Problem.term after);
      Format.eprintf "  fv: %a@.@." Print.(list id) fv;
      assert false
    end

let write_debug_file label problem =
  let file = Filename.change_extension !!Flag.Input.main "debug" in
  let debug =
    let debug_label = label in
    let debug_problem = problem in
    let debug_args = !Flag.Log.args in
    {debug_label; debug_problem; debug_args}
  in
  Marshal.to_file ~flag:[Marshal.Closures] file debug

let check label before after write_debug =
  try
    Color.printf Color.Green "@.### Check %S@." (string_of_label label);
    check_type after;
    check_fv before after;
  with e when write_debug -> write_debug_file label before; raise e

let trans_and_print
      ?(id : int option)
      ?(write_debug = false)
      ((label,tr) : label * tr)
      (problem : Problem.t) =
  let desc = string_of_label label in
  let s_id =
    match id with
    | None -> ""
    | Some id -> Format.sprintf "[#%d]" id
  in
  Debug.printf "START%s: %s@." s_id desc;
  let r = tr problem in
  match r with
  | None ->
      Debug.printf "END%s (skipped): %s@.@." s_id desc;
      if label = Init then
        print s_id desc problem;
      None
  | Some(op,rs) ->
      match LazyList.next rs with
      | Cons(r,_) when label <> Init && problem = fst r ->
          Debug.printf "END%s (without change): %s@.@." s_id desc;
          if desc = !Flag.Debug.stop_after then
            exit 0;
          None
      | _ ->
          if !!Verbose.check || !!Debug.check || !!Debug_ty.check then
            let pr (problem',_) =
              if problem <> problem' then
                print s_id desc problem';
              if !!Debug.check then
                check label problem problem' write_debug
            in
            if desc = !Flag.Debug.stop_after then
              (LazyList.iter pr rs;
               exit 0)
            else
              Some(op, LazyList.map (fun r -> pr r; r) rs)
          else
            Some(op, rs)

let make_init problem = Before(problem, get_rtyp_id)

let run (pps:preprocess list) (results:tree) : tree =
  let counter = ref 0 in
  let rec aux (acc:tree) (label,tr) : tree =
    match acc with
    | Before problem ->
        incr counter;
        let id = !counter in
        let time = !!Time.get in
        let op, no_change, result =
          match trans_and_print ~id (label,tr) (fst problem) with
          | None -> And, true, LazyList.singleton acc
          | Some(op,rs) -> op, false, LazyList.map (fun r -> Before r) rs
        in
        After {id; time; label; no_change; problem; op; result}
    | After r ->
        let result = LazyList.map (aux -$- (label,tr)) r.result in
        After {r with result}
  in
  (*  let aux acc ltr = aux acc ltr |@> print_log_tree in*)
  Time.measure_and_add
    Flag.Log.Time.preprocess
    (List.fold_left aux results) pps

let run_problem pps problem = run pps @@ make_init problem

let run_on_term pps t =
  t
  |> Problem.safety
  |> run_problem pps
  |> get
