open Util
open Mochi_util

module Debug_ty = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".ty") end)
module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type preprocess_label =
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
  | Make_ext_funs
  | Copy_poly
  | Ignore_non_termination
  | Beta_reduce_trivial
  | Eliminate_redundant_arguments
  | Recover_const_attr
  | Decomp_pair_eq
  | Add_preds
  | Replace_fail_with_raise
  | Ignore_excep_arg
  | Encode_simple_variant
  | Split_type_decls
  | Encode_recdata
  | Encode_option
  | Replace_base_with_int
  | Replace_data_with_int
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
  | Inline_module_var
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


type tr_result = Problem.t * ((Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t)
type tr = Problem.t -> tr_result list option
type result = preprocess_label * tr_result
type t = preprocess_label * tr

let string_of_label = function
  | Init -> "Init"
  | Ref_type_pred_type_check -> "Refinement type predicate type check"
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
  | Make_ext_funs -> "Make ext funs"
  | Copy_poly -> "Copy poly"
  | Ignore_non_termination -> "Ignore non termination"
  | Beta_reduce_trivial -> "Beta reduce trivial"
  | Eliminate_redundant_arguments -> "Eliminate redundant arguments"
  | Recover_const_attr -> "Recover const attr"
  | Decomp_pair_eq -> "Decomp pair eq"
  | Add_preds -> "Add preds"
  | Replace_fail_with_raise -> "Replace fail with raise"
  | Ignore_excep_arg -> "Ignore excep arg"
  | Encode_simple_variant -> "Encode simple variant"
  | Split_type_decls -> "Split type declaration"
  | Encode_recdata -> "Encode recdata"
  | Replace_base_with_int -> "Replace base with int"
  | Replace_data_with_int -> "Replace data with int"
  | Replace_complex_data_with_int -> "Replace non-regular data with int"
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
  | Inline_module_var -> "Inline module variables"
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

let get xs =
  match xs with
  | [x] -> x
  | _ -> unsupported "Multiple targets"

let last (acc:result list) = snd @@ List.hd acc
let last_problem (acc:result list) = fst @@ last acc
let last_get_rtyp (acc:result list) = snd @@ last acc
let take_result l (acc:result list) = fst @@ List.assoc l acc

let get_rtyp_id get_rtyp f = get_rtyp f

let if_ b (tr:tr) x : tr_result list option = if b then tr x else None
let map_trans_list (tr:Problem.t->Problem.t list) r : tr_result list option = Some (List.map (Pair.pair -$- get_rtyp_id) @@ tr r)
let map_trans tr = map_trans_list (tr |- List.singleton)

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

let all spec : t list =
  let open Trans_problem in
  [
    Init,
      map_trans Fun.id;
    Ref_type_pred_type_check,
      map_trans Ref_type_pred_typing.ref_type_pred_typing;
    Set_main,
      map_trans_list set_main;
    Extract_module,
      map_trans extract_module;
    Inline_module_var,
      map_trans inline_module_var;
    Instansiate_poly_types,
      map_trans instansiate_poly_types;
    Mark_fv_as_external,
      map_trans mark_fv_as_external;
    Eliminate_unused_let,
      map_trans @@ elim_unused_let ~leave_last:true;
    Insert_extra_param,
      if_ !Flag.Method.relative_complete @@
      map_trans insert_extra_param;
    Encode_bool_as_int,
      if_ !Flag.Encode.bool_to_int @@
      map_trans encode_bool_as_int;
    Replace_const,
      if_ !Flag.Method.replace_const @@
      map_trans CFA.replace_const;
    Lift_type_decl,
      map_trans lift_type_decl;
    Copy_poly,
      Option.some -| List.singleton -| copy_poly_funs;
    Encode_mutable_record,
      map_trans Encode.mutable_record;
    Inline_simple_types,
      map_trans inline_simple_types;
    Abst_recursive_record,
      map_trans Encode.abst_rec_record;
    Inline_record_type,
      map_trans inline_record_type;
    Encode_record,
      map_trans Encode.record;
    Encode_array,
      map_trans Encode.array;
    Abst_ref,
      map_trans Encode.abst_ref;
    Make_fun_tuple,
      if_ !Flag.Method.tupling @@
      map_trans @@ Problem.map Ref_trans.make_fun_tuple;
    Ignore_non_termination,
      if_ !Flag.Method.ignore_non_termination @@
      map_trans ignore_non_termination;
    Beta_reduce_trivial,
      map_trans beta_reduce_trivial;
    Eliminate_redundant_arguments,
      if_ !Flag.Method.elim_redundant_arg @@
      map_trans elim_redundant_arg;
    Recover_const_attr,
      map_trans recover_const_attr;
    Decomp_pair_eq,
      map_trans decomp_pair_eq;
    Add_preds,
      if_ (spec.Spec.abst_env <> [])
      (fun problem -> Some [Problem.map (Trans.replace_typ (Spec.get_abst_env spec @@ Problem.term problem)) problem, get_rtyp_id]);
    Ignore_excep_arg,
      if_ !Flag.Method.ignore_exn_arg @@
      map_trans ignore_exn_arg;
    Make_ext_funs,
      if_ (not !Flag.Method.encode_before_make_ext_fun) @@
      map_trans make_ext_funs;
    Encode_simple_variant,
      map_trans Encode.simple_variant;
    Replace_base_with_int,
      if_ (!Flag.Encode.base_to_int || !Flag.Encode.data_to_int) @@
      map_trans replace_base_with_int;
    Inline_simple_types,
      map_trans inline_simple_types;
    Replace_complex_data_with_int,
      if_ !Flag.Encode.complex_data_to_int @@
      map_trans replace_complex_data_with_int;
    Replace_data_with_int,
      if_ !Flag.Encode.data_to_int @@
      map_trans replace_data_with_int;
    Inline_simple_types,
      map_trans inline_simple_types;
    Split_type_decls,
      map_trans split_type_decls;
    Encode_recdata,
      map_trans Encode.recdata;
    Encode_option,
      map_trans Encode.option;
    Inline_type_decl,
      map_trans inline_type_decl;
    Abst_literal,
      map_trans abst_literal;
    Encode_list,
      Option.some -| List.singleton -| Encode.list;
    Unify_pure_fun_app,
      map_trans unify_pure_fun_app;
    Ret_fun,
      if_ !Flag.Method.tupling @@
      Option.some -| List.singleton -| Problem.map_on Focus.fst Ret_fun.trans;
    Ref_trans,
      if_ !Flag.Method.tupling @@
      Option.some -| List.singleton -| Problem.map_on Focus.fst Ref_trans.trans;
    Tupling,
      if_ !Flag.Method.tupling @@
      Option.some -| List.singleton -| Problem.map_on Focus.fst Tupling.trans;
    Inline,
      (fun prog -> Some [Problem.map (Trans.inlined_f (Spec.get_inlined_f spec @@ Problem.term prog)) prog, get_rtyp_id]);
    Make_ext_funs,
      if_ !Flag.Method.encode_before_make_ext_fun @@
      map_trans make_ext_funs;
    Reduce_rand,
      map_trans reduce_rand;
    Reduce_ignore,
      map_trans reduce_ignore;
    Reduce_branch,
      map_trans reduce_branch;
    Split_assert,
      if_ !Flag.Method.split_assert @@
      map_trans_list split_assert;
    Mark_safe_fun_arg,
      if_ !Flag.PredAbst.shift_pred @@
      map_trans @@ Problem.map Effect.mark_safe_fun_arg;
    Abst_polymorphic_comparison,
      map_trans Encode.abst_poly_comp;
    Variant_args_to_tuple,
      map_trans variant_args_to_tuple;
    Slice,
      if_ !Flag.Method.slice @@
      map_trans slice;
    CPS,
      if_ !Flag.Mode.trans_to_CPS @@
      Option.some -| List.singleton -| CPS.trans;
    Remove_pair,
      if_ !Flag.Mode.trans_to_CPS @@
      Option.some -| List.singleton -| Curry.remove_pair;
    Add_occurence_param,
      if_ !Flag.Method.occurence_param @@
      map_trans add_occurence_param;
    Replace_bottom_def,
      map_trans replace_bottom_def;
    Add_preds,
      if_ (spec.Spec.abst_cps_env <> [])
      (fun problem -> Some [Problem.map (Trans.replace_typ (Spec.get_abst_cps_env spec @@ Problem.term problem)) problem, get_rtyp_id]);
    Eliminate_same_arguments,
      if_ !Flag.Method.elim_same_arg @@
      map_trans @@ Problem.map Elim_same_arg.trans;
    Insert_unit_param,
      if_ !Flag.Method.insert_param_funarg @@
      map_trans insert_param_funarg;
    Alpha_rename,
      if_ Flag.Method.(!mode <> Termination) @@
      Option.some -| List.singleton -| alpha_rename;
  ]

let pr () = if !!Debug_ty.check then Problem.print_debug else Problem.print
let print desc problem = Verbose.printf "###[%.3f] %a:@. @[%a@.@." !!Time.get Color.s_red desc !!pr problem

let rec trans_and_print
          (tr : tr)
          (desc : string)
          (problem : Problem.t) =
  Debug.printf "START: %s@." desc;
  let r = tr problem in
  match r with
  | None ->
      Debug.printf "END (skipped): %s@.@." desc;
      None
  | Some rs ->
      let l = List.length rs in
      Debug.printf "END: %s@.@." desc;
      let aux r =
        let problem' = fst r in
        if desc = "Init" || l > 1 || problem <> problem' then
          print desc problem';
        if desc = !Flag.Debug.stop_after then
          exit 0;
        if !!Debug.check || !!Debug_ty.check then
          let t = Problem.term problem' in
          try
            Type_check.check t ~ty:t.Syntax.typ
          with e ->
            Format.eprintf "@.%s@." @@ Printexc.to_string e;
            Format.eprintf "%a@.@." Print.term' t;
            Format.eprintf "%a@.@." Syntax.pp_typ (t.Syntax.typ);
            assert false
      in
      List.iter aux rs;
      Some rs

let make_init problem = [[Init, (problem, get_rtyp_id)]]

let run (pps:t list) results =
  let aux1 (acc:result list list) (label,tr) : result list list =
    let aux2 rs =
      match rs with
      | [] -> assert false
      | (_,(problem,_))::_ ->
          match trans_and_print tr (string_of_label label) problem with
          | None -> [rs]
          | Some rs' -> List.map (fun r -> (label, r)::rs) rs'
    in
    List.flatten_map aux2 acc
  in
  Time.measure_and_add
    Flag.Log.Time.preprocess
    (List.fold_left aux1 results) pps

let run_problem pps problem = run pps @@ make_init problem

let run_on_term pps t =
  t
  |> Problem.safety
  |> run_problem pps
  |> List.map last_problem
  |> List.map Problem.term
