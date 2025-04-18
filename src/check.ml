open Util
open Type
open! Type_util
open Syntax
open! Term_util

exception Failed of string

let failed s = raise (Failed s)

(** Checks the non-existence of LDot and LApp
    Afther Module.extract, LDot and LApp (in Syntax and Type) must not occur in terms *)
let only_LId =
  let s = __FUNCTION__ in
  let msg fmt = Format.eprintf ("%a%s failed%t: " ^^ fmt) Color.set Red s Color.reset in
  let it = Iter.make () in
  let check_path path =
    match path with
    | Type.LId _ -> ()
    | _ ->
        msg "path = %a@." Path.print path;
        failed s
  in
  let check_ext (_, (_, ext)) = check_path ext.ext_row_path in
  it.lid <-
    (fun lid ->
      match lid with
      | LId _ -> ()
      | _ ->
          msg "lid = %a@." Print.lid lid;
          failed s);
  it.typ <-
    (fun ty ->
      it.typ_rec ty;
      match ty with
      | TConstr (path, _) -> check_path path
      | TModSig sgn -> List.iter check_ext (sig_exts sgn)
      | _ -> ());
  it.decl <-
    (fun decl ->
      it.decl_rec decl;
      match decl with
      | Type_ext (Ext_type ext) -> check_ext ext
      | Type_ext (Ext_rebind (_, path)) -> check_path path
      | _ -> ());
  it.term

(** Checks the consistency of AFV and PAFV *)
let check_afv =
  let col = Col2.make true ( && ) in
  let col_term fm t =
    let fv = get_fv ~force:true t in
    let fvs = List.filter_map (function AFV fv -> Some fv | _ -> None) t.attr in
    match fvs with
    | [ fv' ] ->
        if Id.List.Set.eq fv fv' && List.length fv = List.length fv' then col.term_rec fm t
        else
          let only_in_afv = Id.List.Set.(fv' - fv) in
          let only_in_fv = Id.List.Set.(fv - fv') in
          Format.fprintf fm "Inconsistent AFV@.";
          Format.fprintf fm "  t: %a@." Print.term t;
          Format.fprintf fm "  |afv|: %d@." (List.length fv');
          Format.fprintf fm "  |fv|: %d@." (List.length fv);
          Format.fprintf fm "  only in afv: %a@." Print.(list id) only_in_afv;
          Format.fprintf fm "  only in fv: %a@.@." Print.(list id) only_in_fv;
          false
    | _ ->
        if fvs = [] then Format.fprintf fm "AFV not found@."
        else Format.fprintf fm "Redundant AFV@.";
        Format.fprintf fm "  t: %a@." Print.term t;
        Format.fprintf fm "  fvs: %a@." Print.(list (list id)) fvs;
        false
  in
  let col_pat fm p =
    let fv = get_fv_pat ~force:true p in
    let fvs = List.filter_map (function PAFV fv -> Some fv | _ -> None) p.pat_attr in
    match fvs with
    | [ fv' ] ->
        if Id.List.Set.eq fv fv' && List.length fv = List.length fv' then col.pat_rec fm p
        else
          let only_in_afv = Id.List.Set.(fv' - fv) in
          let only_in_fv = Id.List.Set.(fv - fv') in
          Format.fprintf fm "Inconsistent PAFV@.";
          Format.fprintf fm "  p: %a@." Print.pattern p;
          Format.fprintf fm "  |afv|: %d@." (List.length fv');
          Format.fprintf fm "  |fv|: %d@." (List.length fv);
          Format.fprintf fm "  only in afv: %a@." Print.(list id) only_in_afv;
          Format.fprintf fm "  only in fv: %a@.@." Print.(list id) only_in_fv;
          false
    | _ ->
        if fvs = [] then Format.fprintf fm "PAFV not found@."
        else Format.fprintf fm "Redundant PAFV@.";
        Format.fprintf fm "  p: %a@." Print.pattern p;
        Format.fprintf fm "  fvs: %a@." Print.(list (list id)) fvs;
        false
  in
  col.term <- col_term;
  col.pat <- col_pat;
  fun ?(fm = Format.dummy_formatter) t -> col.term fm t

let assert_check_afv t =
  if not (check_afv ~fm:Format.err_formatter t) then (
    Color.eprintf Color.Red "AFV-check failed:@.";
    assert false)

let check_fv ~force ~before ~after =
  let get_fv' p =
    let fv_term = get_fv ~force @@ Problem.term p in
    let ext_funs = List.map fst (Problem.spec p).ext_ref_env in
    Id.List.Set.(fv_term - ext_funs)
  in
  let fv = Id.List.Set.(get_fv' after - get_fv' before) |> List.filter_out Id.is_external in
  assert_check_afv after.term;
  if fv <> [] then (
    Color.eprintf Color.Red "FV-check failed (new free variable occurs):@.";
    Format.eprintf "  fv: %a@.@." Print.(list id) @@ Id.List.unique fv;
    Format.eprintf "  %a@.@." Print.term_typ (Problem.term after);
    assert false)

let check_free_types ~before ~after =
  let get_free_types' p = Problem.term p |> get_free_types |> List.map fst in
  let ft_before = get_free_types' before in
  let ft_after = get_free_types' after in
  let ft = List.Set.diff ~eq:(Eq.on Path.to_string) ft_after ft_before in
  let check_for_extract_module ty p =
    (not (String.starts_with (Path.to_string ty) (Path.to_string p ^ ".")))
    && Path.to_string ty <> Path.to_string p
  in
  if List.exists (fun ty -> List.exists (check_for_extract_module ty) ft_before) ft then (
    Color.eprintf Color.Red "Free-type-check failed (new free type occurs):@.";
    Format.eprintf "  free types: %a@.@." Print.(list path) ft;
    Format.eprintf "  %a@.@." Print.term_typ (Problem.term after);
    assert false)

let check_type problem =
  let t = Problem.term problem |> Term_util.add_mark in
  let env = Tenv.env_of_ext_mod problem.ext_mod_typ in
  try Type_check.check ~force:true ~env ~ty:t.typ t with
  | Type_check.Failed loc ->
      let len = 3 * Format.pp_get_margin Format.err_formatter () / 2 in
      let pr_delim () =
        Format.eprintf "%a%s%t@.@." Color.set Color.Green (String.make len '=') Color.reset
      in
      Color.eprintf Color.Red "## Type-check failed [%s]@." loc;
      pr_delim ();
      Format.eprintf "%a@.@." Print.term_typ t;
      pr_delim ();
      Format.eprintf "%a@.@." Print.term' t;
      pr_delim ();
      Format.eprintf "%a@.@." Syntax.pp_typ t.typ;
      assert false
  | Sig_of_Lid m -> Format.eprintf "[%s] Sig_of_Lid failed: %a@." __FUNCTION__ Print.path m

let check_lid { Problem.attr; term; _ } =
  try if not (List.mem Problem.Module attr) then only_LId term
  with Failed _ ->
    Color.eprintf Color.Red "LId-check failed (LDot or LApply exist):@.";
    Format.eprintf "  %a@.@." Print.term_typ term;
    assert false

let check_trans ~trans ~check before =
  let after = trans before in
  check ~before ~after;
  after

let check_fv_term ~before ~after =
  let before = Problem.safety before in
  let after = Problem.safety after in
  check_fv ~before ~after

let type_ = check_type
let fv = check_fv
let fv_term = check_fv_term
let free_types = check_free_types
let lid = check_lid
let trans = check_trans
