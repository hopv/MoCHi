open Util
open Mochi_util

(** Print types without checking the type consistency *)
module Debug_ty_wo_check = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".ty_wo_check") end)

let all = Flag.Debug.make_check (__MODULE__^".all")

(** Print types and check the type consistency *)
module Debug_ty = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".ty") ||| all end)

(** Check the consistency of free variablse *)
module Debug_fv = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".fv") ||| all end)

(** Check the non-existence of LDot and LApp after extracting modules *)
module Debug_lid = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".lid") ||| all end)

(** Print results even for unchanged cases *)
module Debug_tree = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".tree") end)

(** Print problems by Problem.pp *)
module Debug_pp = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".pp") end)

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type debug = {debug_label:label; debug_problem:Problem.t; debug_args:string list}

and t = label * (descr * tr)
and tr = Problem.t -> tr_result option
and tr_result = op * problem LazyList.t
and descr = string

and tree =
  | Before of problem
  | After of {id : int;
              time : float;
              label : label;
              descr : string;
              no_change : bool;
              problem : problem option; (* None if !Flag.Method.reduce_memory is true *)
              op : op;
              result : tree LazyList.t}

and problem = Problem.t * get_rtyp
and get_rtyp = (Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t
and op = And | Or
and path = node list
and node = label * (descr * problem)

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
  | Abst_format_const
  | Extract_include
  | Make_bind_for_PAlias
  | Inline_tvar
  | Encode_enum_variant
  | Encode_nonrec_variant
  | Reduce_fail_free
  | Abstract_menhir

let measure_time f t = Time.measure_and_add Flag.Log.Time.preprocess f t

let rec get r =
  match r with
  | Before(p,_) -> Problem.term p
  | After {result} ->
      match LazyList.next result with
      | Cons(r, rs) when LazyList.is_empty rs -> get r
      | _ -> unsupported "Multiple targets"

let root r =
  match r with
  | Before(p,_) -> Some p
  | After {problem} -> Option.map fst problem

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

let rec lists_of_paths (r:tree) : path list =
  match r with
  | Before problem -> [[Init, ("Init", problem)]]
  | After {label; descr; problem; op=And; result} ->
      result
      |> LazyList.to_list
      |> List.flatten_map lists_of_paths
      |> List.map (List.cons (label, (descr, Option.get problem)))
  | After {label; descr; problem; op=Or; result} when LazyList.is_singleton result ->
      let r = LazyList.hd result in
      List.map (List.cons (label, (descr, Option.get problem))) @@ lists_of_paths r
  | After {op=Or} -> unsupported "Multiple targets"

let last (acc:path) = snd @@ snd @@ List.hd acc
let last_problem (acc:path) = fst @@ last acc
let last_get_rtyp (acc:path) = snd @@ last acc
let take_result l (acc:path) = fst @@ snd @@ List.assoc l acc

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

let before label (pps:t list) =
  List.takewhile ((<>) label -| fst) pps

let before_and label (pps:t list) =
  List.takewhile ((<>) label -| fst) pps @ [assoc label pps]

let and_after label (pps:t list) =
  List.dropwhile ((<>) label -| fst) pps

let after label (pps:t list) =
  List.tl @@ and_after label pps

let split label (pps:t list) =
  let pps1,pps2 = List.takedrop_while ((<>) label -| fst) pps in
  pps1, snd (List.hd pps2), List.tl pps2

let filter_out labels pps =
  List.filter_out (fst |- List.mem -$- labels) pps

let all () : t list =
  let open Trans_problem in
  [
    Init,
      ("Init",
       Fun.const None);
    Abstract_menhir, (* TODO: must check the existence of assert/raise *)
      ("Abstract functions generated by Menhir",
       if_ !Flag.Abstract.menhir @@
       map_term Trans.abst_menhir);
    Set_to_primitive,
      ("Translate set functions to primitive operations",
       if_ !Flag.Method.use_set_theory @@
       map_term Trans.set_to_primitive);
    Abstract_magical_functions,
      ("Abstract Obj.magic",
       map_term Trans.abst_magic);
    Abstract_first_class_module,
      ("Abstract first-class modules",
       map Module.abst_first_class_module);
    Inline_functor,
      ("Inline functor",
       map_option Functor.inline);
    Extract_include,
      ("Extract include",
       map Module.extract_include);
    Extract_module,
      ("Extract module",
       map Module.extract);
    Add_external_types,
      ("Add external type definitions",
       map add_ext_typ);
    Instansiate_weak_poly_types,
      ("Instansiate weakly polymorphic types",
       map_term Trans.instansiate_weak_poly_types);
    Abstract_polymorphic_variant,
      ("Abstract polymorphic variant",
       map_term Trans.abst_poly_variant);
    Abstract_GADT,
      ("Abstract GADT",
       map GADT.abstract);
    Inline_tvar, (* for polymorphic first-class modules *)
      ("Inline type variables",
       map_term Trans.inline_tvar);
    Lift_type_decl,
      ("Lift type decl",
       map lift_type_decl);
    Ref_type_pred_type_check,
      ("Type check of refinement type predicates",
       map Ref_type_pred_typing.ref_type_pred_typing);
    Inline_type_alias,
      ("Inline type aliases",
       map_term Trans.inline_type_alias);
    Inline_ext_rebind,
      ("Inline rebinding of exception constructors",
       map_term Trans.inline_ext_rebind);
    Inline_exn_type,
      ("Inline exception type",
       map_term Trans.inline_exn_type);
    Set_main,
      ("Set main",
       map_list set_main);
    Split_by_ref_type,
      ("Split by refinement types",
       map_list_option split_by_ref_type);
    Eliminate_unused_let,
      ("Eliminate unused let",
       map_list ~op:Or elim_unused_let);
    Reduce_fail_free,
      ("Reduce fail free",
       if_ (not !Flag.Method.modular) @@
       map_option reduce_fail_free);
    Insert_extra_param,
      ("Insert extra parameters",
       if_ !Flag.Method.relative_complete @@
       map_term Trans.insert_extra_param);
    Encode_bool_as_int,
      ("Encode bool as int",
       if_ !Flag.Encode.bool_to_int @@
       map_term Trans.encode_bool_as_int);
    Abst_format_const,
      ("Abstract format constants",
       map_term Trans.abst_format_const);
    Replace_const,
      ("Replace const",
       if_ !Flag.Method.replace_const @@
       map CFA.replace_const);
    Rename_target_ext_funs,
      ("Rename target external functions",
       map rename_target_ext_funs);
    Copy_poly_values,
      ("Copy polymorphic values",
       singleton copy_poly_values);
    Copy_poly_type,
      ("Copy polymorphic types",
       map_term Trans.copy_poly_type);
    Slice_top_fun,
      ("Slice by top-level function definitions",
       if_ !Flag.Method.sub @@
       map_list ~op:Or slice_top_fun);
    Set_main_sliced,
      ("Set main for slice",
       if_ !Flag.Method.sub @@
       map_list set_main_for_slice);
    Elim_unused_assumption,
      ("Eliminate unused assumptions",
       map elim_unused_assumption);
    Encode_lazy,
      ("Encode lazy",
       map Encode.lazy_);
    Encode_mutable_record,
      ("Encode mutable record",
       map Encode.mutable_record);
    Inline_simple_types,
      ("Inline simple types",
       map inline_simple_types);
    Abst_recursive_record,
      ("Abstract recursive record",
       map Encode.abst_rec_record);
    Inline_record_type,
      ("Inline record type",
       map inline_record_type);
    Encode_record,
      ("Encode record",
       map Encode.record);
    Encode_array,
      ("Encode array",
       map Encode.array);
    Merge_deref,
      ("Merge dereferences",
       map_option merge_deref);
    Abst_ref,
      ("Abstract ref",
       map Encode.abst_ref);
    Abst_object,
      ("Abstract objects",
       map Encode.abst_obj);
    Make_fun_tuple,
      ("Make fun tuple",
       if_ !Flag.Method.tupling @@
       map @@ Problem.map Ref_trans.make_fun_tuple);
    Ignore_non_termination,
      ("Ignore non termination",
       if_ !Flag.Method.ignore_non_termination @@
       map_term Trans.ignore_non_termination);
    Eliminate_redundant_arguments,
      ("Eliminate redundant arguments",
       if_ !Flag.Method.elim_redundant_arg @@
       map_term Trans.elim_redundant_arg);
    Recover_const_attr,
      ("Recover const attr",
       map_term Trans.recover_const_attr);
    Decomp_pair_eq,
      ("Decomp pair eq",
       map_term Trans.decomp_pair_eq);
    Add_preds,
      ("Add preds",
       map_option (add_preds Spec.get_abst_env));
    Replace_data_with_int_but_exn,
      ("Replace data with int except exceptions",
       if_ !Flag.Abstract.data_to_int_but_exn @@
       map replace_data_with_int_but_exn);
    Abstract_exn, (* TODO: trans env *)
      (* Must precede Encode_simple_variant, Replace_data_with_int *)
      ("Abstract exceptions",
       if_ !Flag.Abstract.exn_to_bool @@
       map_term Trans.abstract_exn);
    Ignore_data_arg,
      ("Ignore arguments of data type constructors",
       if_ !Flag.Abstract.ignore_data_arg @@
       map_term Encode.ignore_data_arg);
    Ignore_excep_arg,
      ("Ignore arguments of exceptions",
       if_ !Flag.Abstract.ignore_exn_arg @@
       map_term Encode.ignore_exn_arg);
    Ignore_excep_fun_arg,
      ("Ignore function arguments of exceptions",
       map_term Encode.ignore_exn_fun_arg);
    Ignore_excep_fun_arg,
      ("Ignore recursive arguments of exceptions",
       map_term Encode.ignore_rec_exn_arg);
    Make_ext_funs,
      ("Generate external functions",
       if_ (not !Flag.Method.encode_before_make_ext_fun) @@
       map make_ext_funs);
    Encode_enum_variant,
      ("Encode enum variant 1",
       map Encode.enum_variant);
    Encode_nonrec_variant,
      ("Encode non-recursive variant 1",
       map Encode.nonrec_variant);
    Replace_base_with_int,
      ("Replace base with int",
       if_ Flag.Abstract.(!base_to_int || !data_to_int) @@
       map replace_base_with_int);
    Inline_simple_types,
      ("Inline simple types 1",
       map inline_simple_types);
    Replace_list_with_int,
      ("Replace lists with int",
       if_ !Flag.Abstract.list_to_int @@
       map replace_list_with_int);
    Replace_data_with_int,
      ("Replace data with int",
       if_ !Flag.Abstract.data_to_int @@
       map replace_data_with_int);
    Replace_complex_data_with_int, (* TODO: trans env *)
      ("Replace non-regular data with int",
       if_ !Flag.Abstract.complex_data_to_int @@
       map_term Trans.replace_complex_data_with_int);
    Inline_simple_types,
      ("Inline simple types 2",
       map inline_simple_types);
    Ignore_mutual_data_arg,
      ("Ignore arguments of mutually recursive data",
       map_term Encode.ignore_mutual_data_arg);
    Encode_enum_variant, (* This can be removed? *)
      ("Encode enum variant 2",
       map Encode.enum_variant);
    Encode_nonrec_variant, (* This can be removed? *)
      ("Encode non-recursive variant 2",
       map Encode.nonrec_variant);
    Encode_recdata,
      ("Encode recdata",
       map Encode.recdata);
    Encode_option,
      ("Encode option",
       map Encode.option);
    Inline_type_decl,
      ("Inline type decl",
       map_term Trans.inline_type_decl);
    Abst_literal,
      ("Abstract literal",
       map_term Trans.abst_literal);
    Encode_list,
      ("Encode list",
       singleton Encode.list);
    Replace_abst_with_int,
      ("Replace abstract types with int",
       map replace_abst_with_int);
    Abst_div,
      ("Abstract division",
       map_term Trans.abst_div);
    Unify_pure_fun_app,
      ("Unify applications of pure functions",
       map_term Trans.unify_pure_fun_app);
    Ret_fun,
      ("Ret fun",
       if_ !Flag.Method.tupling @@
       singleton @@ Problem.map_on Focus.fst Ret_fun.trans);
    Ref_trans,
      ("Ref trans",
       if_ !Flag.Method.tupling @@
       singleton @@ Problem.map_on Focus.fst Ref_trans.trans);
    Tupling,
      ("Tupling",
       if_ !Flag.Method.tupling @@
       singleton @@ Problem.map_on Focus.fst Tupling.trans);
    Inline,
      ("Inline",
       map inline);
    Make_ext_funs,
      ("Generate external function",
       if_ !Flag.Method.encode_before_make_ext_fun @@
       map make_ext_funs);
    Reduce_rand,
      ("Reduce rand",
       map_term Trans.reduce_rand);
    Reduce_ignore,
      ("Reduce ignore",
       map_term Trans.reduce_ignore);
    Reduce_branch,
      ("Reduce branch",
       map_term Trans.reduce_branch);
    Split_assert,
      ("Split assert",
       if_ !Flag.Method.split_assert @@
       map_list split_assert);
    Mark_safe_fun_arg,
      ("Mark safe fun arg",
       if_ !Flag.PredAbst.shift_pred @@
       map @@ Problem.map Effect.mark_safe_fun_arg);
    Abst_polymorphic_comparison,
      ("Abstract polymorphic comparison",
       map Encode.abst_poly_comp);
    Variant_args_to_tuple,
      ("Replace variant arguments with tuples",
       map_term Trans.variant_args_to_tuple);
    Slice,
      ("Slice",
       if_ !Flag.Method.slice @@
       map_list ~op:Or Slice.slice_problem);
    CPS,
      ("CPS",
       if_ !Flag.Method.trans_to_CPS @@
       singleton CPS.trans);
    Remove_pair,
      ("Remove pair",
       if_ !Flag.Method.trans_to_CPS @@
       singleton Curry.remove_pair);
    Add_occurence_param,
      ("Add occurence parameters",
       if_ !Flag.Method.occurence_param @@
       map_term Trans.add_occurence_param);
    Replace_bottom_def,
      ("Replace bottom def",
       map_term Trans.replace_bottom_def);
    Add_preds_CPS,
      ("Add preds CPS",
       map_option (add_preds Spec.get_abst_cps_env));
    Eliminate_same_arguments,
      ("Eliminate same arguments",
       if_ !Flag.Method.elim_same_arg @@
       map @@ Problem.map Elim_same_arg.trans);
    Insert_unit_param,
      ("Insert unit param",
       if_ !Flag.Method.insert_param_funarg @@
       map_term Trans.insert_param_funarg);
    Alpha_rename,
      ("Alpha renaming",
       if_ Flag.(!mode <> Termination) @@
       singleton alpha_rename);
  ]

let pr () =
  if !!Debug_pp.check then
    Problem.pp
  else if !!Debug_ty.check || !!Debug_ty_wo_check.check then
    Problem.print_debug
  else
    Problem.print
let print s_id desc problem =
  Verbose.printf "%a###[%.3f]%s%t %a:@. @[%a@.@." Color.set Color.Green !!Time.get s_id Color.reset Color.s_red desc !!pr problem

let print_log_tree fm t =
  let rec pr indent first last t =
    let indent' =
      if last then
        indent ^ "  "
      else
        indent ^ "│ "
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
    | After {id; time; descr; result} ->
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
        Format.fprintf fm "%s%s[#%d %a@@ %.3f%t] %s@\n" indent head id Color.set Color.Green time Color.reset descr;
        List.iteri (fun i t -> pr indent' false (i=len-1) t) children
  in
  pr "" true true t


(* BUGGY *)
let write_debug_file label problem =
  let file = Filename.change_extension !!Flag.IO.temp "debug" in
  let debug =
    let debug_label = label in
    let debug_problem = problem in
    let debug_args = !Flag.Log.args in
    {debug_label; debug_problem; debug_args}
  in
  Marshal.to_file ~flag:[Marshal.Closures] file debug

let check_init ~ty ~fv ~lid ~descr problem =
  if !Flag.Preprocess.check_flag && (ty || fv || lid) then
    let before = Problem.safety Term_util.Term.unit in
    let after = problem in
    Color.printf Green {|### Check "%s"@.|} descr;
    if ty then Check.type_ problem;
    if fv then Check.fv ~force:true ~before ~after;
    if lid then Check.lid problem;
    Color.printf Green "### Check DONE@.@."

let check ~ty ~fv ~lid ~label ~descr ~before ~after ~write_debug =
  if !Flag.Preprocess.check_flag && (ty || fv || lid) then
    try
      Color.printf Green {|### Check "%s"@.|} descr;
      if ty then Check.type_ after;
      if fv then Check.fv ~force:true ~before ~after;
      if fv then Check.free_types ~before ~after;
      if lid then Check.lid after;
      Color.printf Green "### Check DONE@.@."
    with e when write_debug -> write_debug_file label before; raise e

let trans_and_print
      ?(id : int option)
      ?(write_debug = false)
      ((label,(descr,tr)) : t)
      (problem : Problem.t) =
  let s_id =
    match id with
    | None -> ""
    | Some id -> Format.sprintf "[#%d]" id
  in
  Debug.printf "START[%.3f]%s: %s@." !!Time.get s_id descr;
  let r = tr problem in
  match r with
  | None ->
      Debug.printf "END  [%.3f]%s (skipped): %s@.@." !!Time.get s_id descr;
      if label = Init then begin
          print s_id descr problem;
          check_init ~ty:!!Debug_ty.check ~fv:!!Debug_fv.check ~lid:!!Debug_lid.check ~descr problem;
          if !Flag.Preprocess.stop_after = "Init" then exit 0;
        end;
      None
  | Some(op,rs) ->
      match LazyList.next rs with
      | Cons(r,_) when label <> Init && problem = fst r ->
          Debug.printf "END  [%.3f]%s (without change): %s@.@." !!Time.get s_id descr;
          if descr = !Flag.Preprocess.stop_after then
            exit 0;
          if descr = !Flag.Preprocess.check_after then
            Flag.Preprocess.check_flag := true;
          None
      | _ ->
          Debug.printf "END  [%.3f]%s: %s@.@." !!Time.get s_id descr;
          if !!Verbose.check || !!Debug.check || !!Debug_ty.check then
            let pr (problem',_) =
              if problem <> problem' then
                print s_id descr problem';
              check ~ty:!!Debug_ty.check ~fv:!!Debug_fv.check ~lid:!!Debug_lid.check ~label ~descr ~before:problem ~after:problem' ~write_debug
            in
            if descr = !Flag.Preprocess.stop_after then
              (LazyList.iter pr rs;
               exit 0);
            if descr = !Flag.Preprocess.check_after then
              Flag.Preprocess.check_flag := true;
            Some(op, LazyList.map (fun r -> pr r; r) rs)
          else
            Some(op, rs)

let make_init problem = Before(problem, get_rtyp_id)

let rec map_before f t =
  match t with
  | Before problem -> f problem
  | After r ->
      let result = LazyList.map (map_before f) r.result in
      After {r with result}

(* BUGGY *)
let save_to_file ?num (label:label) (problem:problem) =
  let ext =
    match num with
    | None -> "pp.bin"
    | Some n -> "pp." ^ string_of_int n ^ ".bin"
  in
  let filename = Filename.change_extension !!Flag.IO.temp ext in
  Marshal.to_file ~flag:[ Marshal.No_sharing ;Marshal.Closures] filename (label,problem)

let load_from_file filename : (label * problem) =
  Marshal.from_file_exn filename

let run (pps:t list) (results:tree) : tree =
  let counter = ref 0 in
  let f (label,(descr,_) as pp) problem =
    incr counter;
    let id = !counter in
    let time = !!Time.get in
    let op, no_change, result =
      match trans_and_print ~id pp (fst problem) with
      | None -> And, true, LazyList.singleton (Before problem)
      | Some(op,rs) ->
          if !Flag.Preprocess.save_preprocess then save_to_file ~num:!counter label problem;
          op, false, LazyList.map (fun r -> Before r) rs
    in
    let problem =
      if !Flag.Preprocess.reduce_memory then
        None
      else
        Some problem
    in
    After {id; time; label; descr; no_change; problem; op; result}
  in
  let rec aux acc pps =
    match pps with
    | [] -> acc
    | ltr::pps' ->
        let acc' = map_before (f ltr) acc in
        aux acc' pps'
  in
  measure_time (aux results) pps

let restart pps =
  let label,problem = load_from_file !!Flag.IO.main in
  let pps = and_after label pps in
  fst problem, run pps (Before problem)

let check_duplicate pps =
  let ss = List.map (snd |- fst) pps in
  assert (List.length ss = List.length (List.sort compare ss))

let run_problem pps problem =
  if !!Debug.check then check_duplicate pps;
  run pps @@ make_init problem

let run_on_term pps t =
  t
  |> Problem.safety
  |> run_problem pps
  |> get
