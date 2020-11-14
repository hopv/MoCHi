open Util
open Syntax
open Term_util

type t =
    {assertion: (id * Ref_type.t) list;
     ref_env: (id * Ref_type.t) list;
     ext_ref_env: (id * string option * Ref_type.t) list;
     abst_env: env;
     abst_cps_env: env;
     abst_cegar_env: env;
     inlined: id list;
     inlined_f: id list;
     fairness: Fair_termination_type.fairness}

let init =
  {assertion = [];
   ref_env = [];
   ext_ref_env = [];
   abst_env = [];
   abst_cps_env = [];
   abst_cegar_env = [];
   inlined = [];
   inlined_f = [];
   fairness = []}

(* Printer *)

let pr_ref_env ppf (x,typ) =
  Format.fprintf ppf "%a: %a" Print.id x (Color.blue Ref_type.print) typ
let pr_ext_ref_env ppf (x,loc,typ) =
  match loc with
  | None -> Format.fprintf ppf "%a: %a" Print.id x (Color.blue Ref_type.print) typ
  | Some _s -> Format.fprintf ppf "%a: %a" Print.id x (Color.blue Ref_type.print) typ
let pr_env ppf (x,typ) = Format.fprintf ppf "%a: %a" Print.id x (Color.blue Print.typ) typ

let print_aux ppf s pr env =
  if env <> [] then
    begin
      Color.fprintf ppf Color.Red "@,@[[%s]@\n  @[" s;
      print_list pr "@\n" ppf env;
      Format.fprintf ppf "@]@]"
    end

let print_assert_ref_env ppf renv = print_aux ppf "refinement type assertions" pr_ref_env renv
let print_ref_env ppf renv = print_aux ppf "refinement type interfaces" pr_ref_env renv
let print_ext_ref_env ppf eenv = print_aux ppf "refinement type assumptions" pr_ext_ref_env eenv
let print_abst_env ppf aenv = print_aux ppf "abstraction type environment" pr_env aenv
let print_abst_cps_env ppf cpsenv = print_aux ppf "abstraction type environment for CPS transformed program" pr_env cpsenv
let print_abst_cegar_env ppf cegarenv = print_aux ppf "abstraction type environment for CEGAR-loop" pr_env cegarenv
let print_inlined ppf inlined = print_aux ppf "inlined functions" Print.id inlined
let print_inlined_f ppf inlined_f = print_aux ppf "force inlined functions" Print.id inlined_f


let print ppf {assertion; ref_env; ext_ref_env; abst_env; abst_cps_env; abst_cegar_env; inlined; inlined_f} =
  Format.fprintf ppf "@[";
  print_assert_ref_env ppf assertion;
  print_ref_env ppf ref_env;
  print_ext_ref_env ppf ext_ref_env;
  print_abst_env ppf abst_env;
  print_abst_cps_env ppf abst_cps_env;
  print_abst_cegar_env ppf abst_cegar_env;
  print_inlined ppf inlined;
  print_inlined_f ppf inlined_f;
  Format.fprintf ppf "@]"

let merge spec1 spec2 =
  {assertion = spec1.assertion @ spec2.assertion;
   ref_env = spec1.ref_env @ spec2.ref_env;
   ext_ref_env = spec1.ext_ref_env @ spec2.ext_ref_env;
   abst_env = spec1.abst_env @ spec2.abst_env;
   abst_cps_env = spec1.abst_cps_env @ spec2.abst_cps_env;
   abst_cegar_env = spec1.abst_cegar_env @ spec2.abst_cegar_env;
   inlined = spec1.inlined @ spec2.inlined;
   inlined_f = spec1.inlined_f @ spec2.inlined_f;
   fairness = spec1.fairness @ spec2.fairness}


(* Getters *)

let get_def_vars =
  let col = make_col2 [] (@@@) in
  let col_decl prefix decl =
    match decl with
    | Decl_let defs ->
        let xs = List.map fst defs in
        let vars = List.rev_flatten_map (snd |- col.col2_term prefix) defs in
        List.map prefix xs @@@ vars
    | _ -> []
  in
  let col_desc prefix desc =
    match desc with
    | Local(Decl_let[m,{desc=Module decls}], t) ->
        let prefix' x = Id.add_module_prefix (prefix x) ~m in
        List.rev_flatten_map (col.col2_decl prefix') decls @@@ col.col2_term prefix t
    | _ -> col.col2_desc_rec prefix desc
  in
  col.col2_decl <- col_decl;
  col.col2_desc <- col_desc;
  col.col2_term Fun.id


type kind =
  | Assertion
  | Ref_env
  | Ext_ref_env
  | Abst_env
  | Abst_cps_env
  | Abst_cegar_env
  | Inlined
  | Inlined_f

let rename_ids ks {assertion; ref_env; ext_ref_env; abst_env; abst_cps_env; abst_cegar_env; inlined; inlined_f; fairness} vars =
  let rename_id f = (* temporal implementation *)
    if CEGAR_syntax.is_randint_var (Id.name f) then
      f
    else
      try
        List.find_eq_on Id.to_string f vars
      with Not_found ->
        List.find_eq_on Id.name f vars

  in
  let aux_ref (f,typ) =
    try
      let f' = rename_id f in
      if not @@ can_unify (Id.typ f') (Ref_type.to_simple typ) then
        begin
          Format.eprintf "VAR: %a@." Id.print f;
          Format.eprintf "  Prog: %a@." Print.typ @@ Id.typ f';
          Format.eprintf "  Spec: %a@." Ref_type.print typ;
          fatal @@ Format.sprintf "The simple type of %s in the specification is wrong?" @@ Id.name f'
        end;
      Some (f', typ)
    with Not_found -> None
  in
  let aux_ext_ref (f,loc,typ) =
    match aux_ref (f,typ) with
    | None -> None
    | Some(f',typ') -> Some (f', loc, typ')
  in
  let aux_typ (f,typ) = Option.try_with (fun () -> rename_id f, typ) ((=) Not_found) in
  let aux_id f = Option.try_with (fun () -> rename_id f) ((=) Not_found) in
  {assertion = if List.mem Assertion ks then List.filter_map aux_ref assertion else assertion;
   ref_env = if List.mem Ref_env ks then List.filter_map aux_ref ref_env else ref_env;
   ext_ref_env = if List.mem Ext_ref_env ks then List.filter_map aux_ext_ref ext_ref_env else ext_ref_env;
   abst_env = if List.mem Abst_env ks then List.filter_map aux_typ abst_env else abst_env;
   abst_cps_env = if List.mem Abst_cps_env ks then List.filter_map aux_typ abst_cps_env else abst_cps_env;
   abst_cegar_env = if List.mem Abst_cegar_env ks then List.filter_map aux_typ abst_cegar_env else abst_cegar_env;
   inlined = if List.mem Inlined ks then List.filter_map aux_id inlined else inlined;
   inlined_f = if List.mem Inlined_f ks then List.filter_map aux_id inlined_f else inlined_f;
   fairness}

let get_vars t = get_def_vars t @ get_fv t
let get_vars_cegar prog = List.map (fun def -> Id.from_string def.CEGAR_syntax.fn Type.typ_unknown) prog.CEGAR_syntax.defs

let get_assertion spec t = (rename_ids [Assertion] spec @@ get_vars t).assertion
let get_ref_env spec t = (rename_ids [Ref_env] spec @@ get_vars t).ref_env
let get_ext_ref_env spec t = (rename_ids [Ext_ref_env] spec @@ get_vars t).ext_ref_env
let get_abst_env spec t = (rename_ids [Abst_env] spec @@ get_vars t).abst_env
let get_abst_cps_env spec t = (rename_ids [Abst_cps_env] spec @@ get_vars t).abst_cps_env
let get_abst_cegar_env spec prog = (rename_ids [Abst_cegar_env] spec @@ get_vars_cegar prog).abst_cegar_env
let get_inlined spec t = (rename_ids [Inlined] spec @@ get_vars t).inlined
let get_inlined_f spec t = (rename_ids [Inlined_f] spec @@ get_vars t).inlined_f

let get_all_ref_env ?(rename=false) spec t =
  let spec' =
    if rename then
      rename_ids [Assertion; Ref_env; Ext_ref_env] spec @@ get_vars t
    else
      spec
  in
  spec'.assertion @ spec'.ref_env @ List.map Triple.take13 spec'.ext_ref_env


(* Transformer *)

let map_ref_env f ({assertion; ref_env; ext_ref_env} as spec) =
  let assertion = List.map f assertion in
  let ref_env = List.map f ref_env in
  let ext_ref_env =
    let f' (x,loc,ty) =
      let x',ty' = f (x,ty) in
      x', loc, ty'
    in
    List.map f' ext_ref_env
  in
  {spec with assertion; ref_env; ext_ref_env}

let map_ref f spec = map_ref_env (Pair.map_snd f) spec


(* Normalizer *)

let set_typ_to_id ({assertion; ref_env; ext_ref_env; abst_env; abst_cps_env; abst_cegar_env} as m) =
  if abst_env @ abst_cps_env @ abst_cegar_env <> [] then
    unsupported "Spec.set_typ_to_id";
  let aux_ref (f,ty) = Id.set_typ f (Ref_type.to_simple ty), ty in
  let aux_ext_ref (f,loc,ty) = Id.set_typ f (Ref_type.to_simple ty), loc, ty in
  let assertion = List.map aux_ref assertion in
  let ref_env = List.map aux_ref ref_env in
  let ext_ref_env = List.map aux_ext_ref ext_ref_env in
  {m with assertion; ref_env; ext_ref_env}

let adt_to_prim = map_ref Ref_type.adt_to_prim


(* Parser *)

let parse parser lexer filename =
  if filename = "" then
    init
  else
    let lb = Lexing.from_channel @@ open_in filename in
    lb.Lexing.lex_curr_p <-
      {Lexing.pos_fname = Format.sprintf "File \"%s\"" @@ Filename.basename filename;
       Lexing.pos_lnum = 1;
       Lexing.pos_cnum = 0;
       Lexing.pos_bol = 0};
    parser lexer lb

let parse_comment parser lexer filename =
  let cin = open_in filename in
  let rec loop flag str =
    let s = try Some (input_line cin) with End_of_file -> None in
    match s with
    | None -> str
    | Some s when String.starts_with s "(*{SPEC}" -> loop true str
    | Some s when String.ends_with s "{SPEC}*)" -> loop false str
    | Some s when flag -> loop true (str ^ "\n" ^ s)
    | _ -> loop false str
  in
  let lb = Lexing.from_string @@ loop false "" in
    lb.Lexing.lex_curr_p <-
      {Lexing.pos_fname = Format.sprintf "Spec in file \"%s\"" @@ Filename.basename filename;
       Lexing.pos_lnum = 0;
       Lexing.pos_cnum = 0;
       Lexing.pos_bol = 0};
  parser lexer lb

let read parser lexer =
  Id.save_counter ();
  let spec1 =
    begin
      if !Flag.Method.use_spec && !Flag.Input.spec = ""
      then
        let spec = Filename.change_extension !!Flag.Input.main "spec" in
        if Sys.file_exists spec then Flag.Input.spec := spec
    end;
    parse parser lexer !Flag.Input.spec
  in
  let spec2 =
    if !Flag.Method.comment_spec && Sys.file_exists !!Flag.Input.main
    then parse_comment parser lexer !!Flag.Input.main
    else init
  in
  let spec =
    merge spec1 spec2
    |> adt_to_prim
  in
  Id.reset_counter ();
  set_typ_to_id spec
