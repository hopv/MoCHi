# 2 "parser_wrapper_4.08.ml"
open Util
open Asttypes
open Typedtree
open Types
open Syntax
open Term_util
open Type

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let () = Compmisc.init_path false

let print_location = Location.print_loc
let () = Syntax.print_location_ref := print_location
let add_load_path = Load_path.add_dir

let report_error e = Location.report_exception Format.err_formatter e

type env =
  {path : string list;
   id_env : id list;
   md_prefix : string;
   ty_decl : (string * typ) list;
   ty_decl_ext : (string * typ) list;
   tr_lazy : bool}

let init_env : env =
  {path = [];
   id_env = [];
   md_prefix = "";
   ty_decl = [];
   ty_decl_ext = [];
   tr_lazy = true}


let exc_init : (string * typ list) list = []
(*
  ["Assert_failure", [];
   "Not_found", []]
 *)
let exc_env = ref exc_init
let init_exc_env () = exc_env := exc_init
let add_exc_env name typs =
  if List.mem_assoc name !exc_env then
    if not @@ List.eq ~eq:Type.same_shape (List.assoc name !exc_env) typs then
      unsupported "Same name exception"
    else
      ()
  else
    exc_env := (name,typs) :: !exc_env
let exc_typ () = TVariant(false,!exc_env)


let prim_typs =
  ["unit", Ty.unit;
   "bool", Ty.bool;
   "int", Ty.int;
   "Stdlib.format", Ty.prim "string";
   "Stdlib.format4", Ty.prim "string";
   "Stdlib.format6", Ty.prim "string";
   "CamlinternalFormatBasics.fmt", Ty.prim "string";
   "CamlinternalFormatBasics.format6", Ty.prim "string";
   "exn", TData "exn"]
    @ List.map (fun s -> s, TBase (TPrim s)) prim_base_types


let from_mutable_flag = function
  | Asttypes.Mutable -> Mutable
  | Asttypes.Immutable -> Immutable


let prim_typ_constr =
  ["list", TList;
   "Stdlib.ref", TRef;
   "option", TOption;
   "array", TArray;
   "Lazy.t", TLazy]

let is_prim_constr constrs =
  match constrs with
  | ["[]", []; "::", ty::_] -> Some (Ty.list ty)
  | _ -> None

let from_list f env xs =
  let aux x (env,acc) =
    let env,x' = f env x in
    env, x'::acc
  in
  List.fold_right aux xs (env,[])

let update_env from env tenv s ty =
  if List.mem_assoc s prim_typs || List.mem_assoc s prim_typ_constr || List.mem_assoc s env.ty_decl || List.mem_assoc s env.ty_decl_ext then
    env
  else
    let env = {env with ty_decl_ext = (s,typ_unknown)::env.ty_decl_ext} in
    let env,ty = from env tenv ty in
    let ty_decl_ext =
      let aux ty' = assert (ty' = typ_unknown); ty in
      List.modify s aux env.ty_decl_ext
    in
    {env with ty_decl_ext}

(* for Types.type_declaration *)
(* TODO: merge with one for Typeedtree.type_declaration *)
let rec from_type_declaration env tenv (decl:Types.type_declaration) : env * typ =
  match decl.type_kind with
  | Type_abstract ->
      begin
        match decl.type_manifest with
        | None -> unsupported "Ttype_abstract"
        | Some ty -> from_type_expr env tenv ty
      end
  | Type_variant constrs ->
      let aux {cd_id;cd_args} (env,constrs) =
        match cd_args with
        | Cstr_tuple args ->
            let s = Ident.name cd_id in
            let env,tys = from_type_exprs env tenv args in
            env, (s,tys)::constrs
        | Cstr_record _ -> unsupported "Cstr_record"
      in
      let env',constrs = List.fold_right aux constrs (env,[]) in
      let ty' = Option.default (TVariant(false, constrs)) @@ is_prim_constr constrs in
      env', ty'
  | Type_record(fields, _) ->
      let aux {ld_id;ld_mutable;ld_type} (env,fields) =
        let s = Ident.name ld_id in
        let flag = from_mutable_flag ld_mutable in
        let env', ty = from_type_expr env tenv ld_type in
        env', (s, (flag, ty))::fields
      in
      let env',fields = List.fold_right aux fields (env,[]) in
      env', TRecord fields
  | Type_open -> env, TVar (ref None, None)
  | exception Not_found -> assert false

and from_type_exprs env tenv tys : env * typ list =
  let aux ty (env,tys) =
    let env',ty' = from_type_expr env tenv ty in
    env', ty'::tys
  in
  List.fold_right aux tys (env,[])

and venv = ref []

and from_type_expr env tenv ty0 : env * typ =
  let typ = Ctype.correct_levels ty0 in
  let typ' = (if false then Ctype.repr else Ctype.full_expand tenv) typ in
  Debug.printf "ty1: %a@." Printtyp.type_expr typ;
  Debug.printf "ty2: %a@." Printtyp.type_expr typ';
  Debug.printf "ty3: %a@.@." Printtyp.raw_type_expr typ';
  let env =
    try
      let p,_,ty = Ctype.extract_concrete_typedecl tenv typ' in
      let s = Path.name p in
      update_env from_type_declaration env tenv s ty
    with Not_found -> env
  in
  let env,ty =
    match typ'.Types.desc with
    | Tvar _ when env.tr_lazy ->
        let env' = {env with tr_lazy=false} in
        env, TVarLazy (fun () -> snd @@ from_type_expr env' tenv ty0)
    | Tvar _ ->
        let ty =
          try
            List.assoc typ'.Types.id !venv
          with Not_found ->
            let ty = TVar(ref None, Some (List.length !venv)) in
            venv := (typ'.Types.id, ty)::!venv;
            ty
        in
        env, ty
    | Tarrow(_, typ1, typ2, _) ->
        let env,typ1' = from_type_expr env tenv typ1 in
        let env,typ2' = from_type_expr env tenv typ2 in
        let x = Id.new_var typ1' in
        env, TFun(x, typ2')
    | Ttuple typs ->
        let env,tys' = from_type_exprs env tenv typs in
        env, make_ttuple tys'
    | Tconstr(path, _, _) when List.mem_assoc (Path.name path) prim_typs ->
        env, List.assoc (Path.name path) prim_typs
    | Tconstr(path, typs, _) when List.mem_assoc (Path.name path) prim_typ_constr ->
        let env,tys = from_type_exprs env tenv typs in
        env, TApp(List.assoc (Path.name path) prim_typ_constr, tys)
    | Tconstr(path, typs, _) ->
        let s = Path.name path in
        let env =
          typ
          |> Ctype.expand_head tenv
          |> update_env from_type_expr env tenv s
        in
        env, TData s
    | Tobject _ -> unsupported "Tobject"
    | Tfield _ -> unsupported "Tfield"
    | Tnil -> unsupported "Tnil"
    | Tlink _ -> unsupported "Tlink"
    | Tsubst _ -> unsupported "Tsubst"
    | Tvariant row_desc ->
        let from_row_desc env row_desc =
          let tr env (s,field) =
            match field with
            | Rpresent None -> env, (s,[])
            | Rpresent (Some type_expr) ->
                let env,ty = from_type_expr env tenv type_expr in
                let tys =
                  match ty with
                  | TTuple xs -> List.map Id.typ xs
                  | ty -> [ty]
                in
                env, (s,tys)
            | Reither(_,type_exprs,_,_) ->
                let env,tys = from_type_exprs env tenv type_exprs in
                env, (s, tys)
            | Rabsent -> assert false
          in
          let env,constrs1 = from_list tr env row_desc.row_fields in
          let env,constrs2 =
            if row_desc.row_more.desc = Tnil then
              env, []
            else
              let env',ty = from_type_expr env tenv row_desc.row_more in
              let constrs =
                match ty with
                | TVar _ -> []
                | TVariant(_,constrs) -> constrs
                | _ -> assert false
              in
              env, constrs
          in
          env, constrs1 @ constrs2
        in
        let env,constrs = from_row_desc env row_desc in
        env, TVariant(true, constrs)
    | Tunivar _ -> unsupported "Tunivar"
    | Tpoly(typ,[]) -> from_type_expr env tenv typ
    | Tpoly _ -> unsupported "Tpoly"
    | Tpackage _ -> unsupported "Tpackage"
  in
  env, ty

let from_type_expr env tenv ty = from_type_expr env tenv ty
let from_type_exprs env tenv ty = from_type_exprs env tenv ty

(* for Typedtree.type_declaration *)
(* TODO: merge with one for Types.type_declaration *)
let rec from_type_declaration tenv env (decl:Typedtree.type_declaration) : env * (string * typ) =
  Debug.printf "decl: %a@." (Printtyp.type_declaration (Ident.create_local "t")) decl.typ_type;
  let open Typedtree in
  let env,ty =
    match decl.typ_kind with
    | Ttype_abstract ->
        begin
          match decl.typ_manifest with
          | None -> env, TData "_abst"
          | Some ty -> from_type_expr env tenv ty.ctyp_type
        end
    | Ttype_variant constrs ->
        let aux {cd_id;cd_args} (env,constrs) =
          match cd_args with
          | Cstr_tuple args ->
              let s = Ident.name cd_id in
              let env',tys = from_type_exprs env tenv @@ List.map (fun arg -> arg.ctyp_type) args in
              env', (s,tys)::constrs
          | Cstr_record _ -> unsupported "Cstr_record"
        in
        let env',constrs = List.fold_right aux constrs (env,[]) in
        env', TVariant(false, constrs)
    | Ttype_record fields ->
        let aux {ld_id;ld_mutable;ld_type} (env,fields) =
          let s = Ident.name ld_id in
          let flag = from_mutable_flag ld_mutable in
          let env, ty = from_type_expr env tenv ld_type.ctyp_type in
          env, (s, (flag, ty))::fields
        in
        let env,fields = List.fold_right aux fields (env,[]) in
        env, TRecord fields
    | Ttype_open -> unsupported "Ttype_open"
    | exception Not_found -> assert false
  in
  env, (decl.typ_name.txt, ty)

let wrap_letters_with_sign s =
  if String.contains "!$%&*+-./:<=>?@^|~" s.[0] then
    "(" ^ s ^ ")"
  else
    s

let from_ident_aux name attr typ =
  let name = if name.[0] = '_' then "u" ^ name else name in
  let id = 0 in
  Id.make id name attr typ

let from_ident x typ =
  from_ident_aux (Ident.name x) [] typ

let rec string_of_path x =
  match x with
  | Path.Pident s -> Ident.name s
  | Path.Pdot(y, s) -> string_of_path y ^ "." ^ s
  | Path.Papply(y, z) -> Format.sprintf "%s(%s)" (string_of_path y) (string_of_path z)

let from_ident_path env path typ =
  let name = string_of_path path in
  try
    Id.set_typ (List.find (Id.name |- (=) name) env.id_env) typ
  with Not_found ->
    let attr = [] in
    from_ident_aux name attr typ

let get_constr_name desc typ env =
  match desc.cstr_tag with
  | Cstr_constant _ -> desc.cstr_name
  | Cstr_block _ -> desc.cstr_name
  | Cstr_extension(path, _) -> Path.name path
  | Cstr_unboxed -> unsupported "Cstr_unboxed"

let get_label_name label env =
  label.lbl_name

let add_exc_env_from_constr cstr_desc env tenv =
  match cstr_desc.cstr_res.Types.desc with
  | Tconstr(path,_,_) ->
      if Path.name path = "exn" then
        let name = get_constr_name cstr_desc cstr_desc.cstr_res env in
        let _,typs = from_type_exprs env tenv cstr_desc.cstr_args in
        add_exc_env name typs
  | _ -> assert false


let rec from_pattern env {pat_desc=desc; pat_loc=_; pat_type=typ; pat_env} : env * pattern =
  let env,typ' = from_type_expr env pat_env typ in
  let env,desc =
    match desc with
    | Tpat_any -> env, PAny
    | Tpat_var(x,_) -> env, PVar(from_ident x typ')
    | Tpat_alias({pat_desc=Tpat_any},x,_) -> env, PVar (from_ident x typ')
    | Tpat_alias(p,x,_) ->
        let env,p' = from_pattern env p in
        env, PAlias(p', from_ident x typ')
    | Tpat_constant(Const_int n) -> env, PConst {desc=Const(Int n);typ=typ'; attr=[]}
    | Tpat_constant(Const_char c) -> env, PConst {desc=Const(Char c);typ=typ'; attr=[]}
    | Tpat_constant(Const_string(s,None)) -> env, PConst {desc=Const(String s);typ=typ'; attr=[]}
    | Tpat_constant(Const_string(s,Some _)) -> env, PConst {desc=Const(String s);typ=typ'; attr=[]}
    | Tpat_constant(Const_float s) -> env, PConst {desc=Const(Float (float_of_string s));typ=typ'; attr=[]}
    | Tpat_constant(Const_int32 n) -> env, PConst {desc=Const(Int32 n);typ=typ'; attr=[]}
    | Tpat_constant(Const_int64 n) -> env, PConst {desc=Const(Int64 n);typ=typ'; attr=[]}
    | Tpat_constant(Const_nativeint n) -> env, PConst {desc=Const(Nativeint n);typ=typ'; attr=[]}
    | Tpat_tuple ps ->
        let env,ps' = from_list from_pattern env ps in
        env, PTuple ps'
    | Tpat_construct(_, cstr_desc, []) when get_constr_name cstr_desc typ env = "None" -> env, PNone
    | Tpat_construct(_, cstr_desc, [p]) when get_constr_name cstr_desc typ env = "Some" ->
        let env,p' = from_pattern env p in
        env, PSome p'
    | Tpat_construct(_, cstr_desc, []) when get_constr_name cstr_desc typ env = "()" -> env, PConst unit_term
    | Tpat_construct(_, cstr_desc, []) when get_constr_name cstr_desc typ env = "[]" -> env, PNil
    | Tpat_construct(_, cstr_desc, [p1;p2]) when get_constr_name cstr_desc typ env = "::" ->
        let env,p1' = from_pattern env p1 in
        let env,p2' = from_pattern env p2 in
        env, PCons(p1', p2')
    | Tpat_construct(_, cstr_desc, ps) when typ' = Ty.bool ->
        begin match get_constr_name cstr_desc typ env with
        | "true" -> env, PConst Term.true_
        | "false" -> env, PConst Term.false_
        | _ -> assert false
        end
    | Tpat_construct(_, cstr_desc, ps) ->
        add_exc_env_from_constr cstr_desc env pat_env;
        let name = get_constr_name cstr_desc typ env in
        let env,ps' = from_list from_pattern env ps in
        env, PConstr(name, ps')
    | Tpat_variant(name, pat, _) ->
        let env, ps =
          match pat with
          | None -> env, []
          | Some pat' ->
              let env,p = from_pattern env pat' in
              let ps =
                match p with
                | {pat_desc=PTuple ps} -> ps
                | pat -> [pat]
              in
              env, ps
        in
        env, PConstr(name, ps)
    | Tpat_record(ps,_) ->
        let aux (_,lbl,p) (env,ps) =
          let s = get_label_name lbl env in
          let env,p' = from_pattern env p in
          env, (s,p')::ps
        in
        let env,ps = List.fold_right aux ps (env,[]) in
        env, PRecord ps
    | Tpat_array _ -> unsupported "pattern match (array)"
    | Tpat_or(p1,p2,None) ->
        let env,p1' = from_pattern env p1 in
        let env,p2' = from_pattern env p2 in
        env, POr(p1', p2')
    | Tpat_or(_,_,Some _) -> unsupported "pattern match (or) where row = Some _"
    | Tpat_lazy _ -> unsupported "pattern match (lazy)"
    | Tpat_exception _ ->  unsupported "pattern match (exception)"
  in
  env, {pat_desc=desc; pat_typ=typ'}



let conv_primitive_app t ts typ loc =
  match t.desc,ts with
  | Var {Id.name="List.length"}, [t1] -> make_length t1
  | Var {Id.name="Stdlib.@@"}, [t1;t2] -> make_app t1 [t2]
  | Var {Id.name="Stdlib.="}, [t1;t2] -> make_eq t1 t2
  | Var {Id.name="Stdlib.<>"}, [t1;t2] -> make_neq t1 t2
  | Var {Id.name="Stdlib.<"}, [t1;t2] -> make_lt t1 t2
  | Var {Id.name="Stdlib.>"}, [t1;t2] -> make_gt t1 t2
  | Var {Id.name="Stdlib.<="}, [t1;t2] -> make_leq t1 t2
  | Var {Id.name="Stdlib.>="}, [t1;t2] -> make_geq t1 t2
  | Var {Id.name="Stdlib.&&"}, [t1;t2] -> make_and t1 t2
  | Var {Id.name="Stdlib.||"}, [t1;t2] -> make_or t1 t2
  | Var {Id.name="Stdlib.+"}, [t1;t2] -> make_add t1 t2
  | Var {Id.name="Stdlib.-"}, [t1;t2] -> make_sub t1 t2
  | Var {Id.name="Stdlib.*"}, [t1;t2] -> make_mul t1 t2
  | Var {Id.name="Stdlib./"}, [t1;t2] ->
      let t2' =
        let make_check t = make_seq (make_assert ~loc (make_neq t @@ make_int 0)) t in
        if has_no_effect t2 then
          make_check t2
        else
          let x = Id.new_var Ty.int in
          make_let [x,t2] @@ make_check @@ make_var x
      in
      make_div t1 t2'
  | Var {Id.name="Stdlib.~-"}, [t] -> make_neg t
  | Var {Id.name="Stdlib.not"}, [t] -> make_not t
  | Var {Id.name="Stdlib.fst"}, [t] -> make_fst t
  | Var {Id.name="Stdlib.snd"}, [t] -> make_snd t
  | Var {Id.name="Stdlib.raise"}, [t] -> make_raise t typ
  | Var {Id.name="Stdlib.ref"}, [t] -> make_ref t
  | Var {Id.name="Stdlib.read_int"}, [{desc=Const Unit}] ->
      let attr =
        if Flag.Method.(!mode = NonTermination || !mode = FairNonTermination) then
          AAbst_under::randint_term.attr
        else
          randint_term.attr in
      make_app {randint_term with attr} [unit_term]
  | Var {Id.name="Stdlib.!"}, [t] -> make_deref t
  | Var {Id.name="Stdlib.:="}, [t1;t2] -> make_setref t1 t2
  | Var {Id.name="Random.bool"}, [{desc=Const Unit}] -> randbool_unit_term
  | Var {Id.name="Random.int"}, [{desc=Const (Int 0)}] -> randint_unit_term
  | Var {Id.name="Random.int"}, [t] ->
      let x = Id.new_var ~name:"n" Ty.int in
      make_let [x, randint_unit_term] @@
        make_assume
          (make_and (make_leq (make_int 0) (make_var x)) (make_lt (make_var x) t))
          (make_var x)
  | Var {Id.name="Stdlib.open_in"}, [{desc=Const(Int _)}] -> make_event_unit "newr"
  | Var {Id.name="Stdlib.close_in"}, [{typ=TBase TUnit}] -> make_event_unit "close"
  | Var {Id.name="Stdlib.invalid_arg"}, [{desc=Const(String s)}] ->
      let c = "Invalid_argument" ^ "." ^ s in
      add_exc_env c [];
      make_raise (make_construct c [] !!exc_typ) typ
  | Var {Id.name="Stdlib.failwith"}, [{desc=Const(String s)}] ->
      let c = "Failure" ^ "." ^ s in
      add_exc_env c [];
      make_raise (make_construct c [] !!exc_typ) typ
  | Var {Id.name="Stdlib.invalid_arg"}, [_] ->
      unsupported "Stdlib.invalid_arg with non-constant"
  | Var {Id.name="event"}, [{desc=Const(String s)}] -> make_event_unit s
  | _ -> make_app t ts



let from_value_kind = function
  | Types.Val_reg -> Format.eprintf "Val_reg@."; assert false
  | Types.Val_prim prim_desc -> Id.new_var (prim_desc.Primitive.prim_name)
  | Types.Val_ivar _ -> Format.eprintf "Val_ivar@."; assert false
  | Types.Val_self _ -> Format.eprintf "Val_self@."; assert false
  | Types.Val_anc _ -> Format.eprintf "Val_anc@."; assert false
  | Types.Val_unbound _ -> Format.eprintf "Val_unbound@."; assert false

let from_constant = function
  | Const_int n -> Int n
  | Const_char c -> Char c
  | Const_string(s, None) -> String s
  | Const_string(s, Some _) -> String s
  | Const_float s -> Float (float_of_string s)
  | Const_int32 n -> Int32 n
  | Const_int64 n -> Int64 n
  | Const_nativeint n -> Nativeint n


let is_var_case case =
  match case with
  | {c_lhs={pat_desc=Tpat_var _}; c_guard=None} -> true
  | {c_lhs={pat_desc=Tpat_alias({pat_desc=Tpat_any},_,_)}; c_guard=None} -> true
  | _ -> false

(* TODO: fix to return attribute? *)
let from_attribute {Parsetree.attr_name; attr_payload} =
  if attr_name.txt = "mochi" then
    let open Parsetree in
    match attr_payload with
    | Parsetree.PStr [{pstr_desc=Pstr_eval({pexp_desc=Pexp_ident x},t)}] ->
        begin
          match Longident.flatten x.txt with
          | ["target"] -> Some ()
          | _ -> None
        end
    | Parsetree.PStr _ -> None
    | Parsetree.PSig _ -> None
    | Parsetree.PTyp _ -> None
    | Parsetree.PPat _ -> None
  else
    None
let from_attributes = List.filter_map from_attribute

let rec from_expression env {exp_desc; exp_loc; exp_type; exp_env=tenv; exp_attributes} : env * term =
  let env,typ = from_type_expr env tenv exp_type in
  let env,t =
    match exp_desc with
    | Texp_ident(path, _, ty_desc) ->
        let env,ty' = from_type_expr env tenv ty_desc.val_type in
        let env =
          match typ with
          | TData s when not @@ List.mem_assoc s env.ty_decl_ext -> {env with ty_decl_ext=(s, ty')::env.ty_decl_ext}
          | _ -> env
        in
        env, make_var @@ from_ident_path env path typ
    | Texp_constant c ->
        env, {desc = Const (from_constant c); typ; attr=const_attr}
    | Texp_let(rec_flag, [{vb_pat;vb_expr}], e2)
         when (function Tpat_var _ -> false | _ -> true) vb_pat.pat_desc ->
        let env,p' = from_pattern env vb_pat in
        let env,t1 = from_expression env vb_expr in
        let env,t2 = from_expression env e2 in
        env, make_single_match t1 p' t2
    | Texp_let(Asttypes.Recursive, pats, e) ->
        let env,ps = from_list (fun env {vb_pat} -> from_pattern env vb_pat) env pats in
        let env =
          let id_env = List.fold_right (fun p env -> get_bv_pat p @ env) ps env.id_env in
          {env with id_env}
        in
        let env,bindings =
          let aux env (p,{vb_expr}) =
            match p.pat_desc with
            | PVar x ->
                let env,t = from_expression env vb_expr in
                env, (x, t)
            | _ -> unsupported "Only variables are allowed as left-hand side of 'let rec ... and ...'"
          in
          from_list aux env (List.combine ps pats)
        in
        let env,t = from_expression env e in
        env, make_let bindings t
    | Texp_let(Asttypes.Nonrecursive, pats, e) ->
        let env,(ps,ts) =
          let env,psts =
            let aux env {vb_pat;vb_expr} =
              let env,pat = from_pattern env vb_pat in
              let env,t = from_expression env vb_expr in
              env, (pat,t)
            in
            from_list aux env pats
          in
          env, List.split psts
        in
        let p =
          match ps with
          | [p] -> p
          | _ -> make_ptuple ps
        in
        let t1 =
          match ts with
          | [t] -> t
          | _ -> make_tuple ts
        in
        let env,t2 =
          let env = {env with id_env=get_bv_pat p @ env.id_env} in
          from_expression env e
        in
        env, make_match t1 [p, t2]
    | Texp_function {cases=[case]; partial=Total} when is_var_case case ->
        begin
          let env,(p,t) = from_case env case in
          match p with
          | {pat_desc=PVar x} -> env, make_fun x t
          | _ -> assert false
        end
    | Texp_function {cases; partial} ->
        let env,x,typ2 =
          match typ with
          | TFun(x,typ2) ->
              let env,x' = (* for readable variable names *)
                let env,p = from_pattern env (List.hd cases).c_lhs in
                let x' =
                  match p with
                  | {pat_desc=PTuple ps} ->
                      let xs = List.map (function {pat_desc=PVar x} -> Some x | _ -> None) ps in
                      if List.for_all Option.is_some xs then
                        try
                          xs
                          |> List.map (Id.name -| Option.get)
                          |> String.join "__"
                          |> Id.set_name x
                        with Option.No_value -> assert false
                      else
                        x
                  | _ -> x
                in
                env, x'
              in
              env, x', typ2
          | _ -> assert false
        in
        let env,pats = from_list from_case env cases in
        let pats' =
          match partial with
          | Total -> pats
          | Partial -> pats @ [make_pvar (Id.new_var_id x), make_fail ~loc:exp_loc typ2]
        in
        let t =
          match pats' with
          | [{pat_desc=PAny},t'] -> make_fun x t'
          | [{pat_desc=PVar y},t'] -> make_fun x @@ subst_var y x t'
          | [{pat_desc=PConst{desc=Const Unit}},t'] -> make_fun x t'
          | _ -> make_fun x @@ make_match (make_var x) pats'
        in
        env, t
    | Texp_apply(e, es) ->
        let env,t = from_expression env e in
        let aux i (a,b) (env,acc) =
          let env,t =
            match a,b with
            | _, None -> unsupported "expression (optional)"
            | Optional _, Some e ->
                (* I don't know why, but the type environment of e is not appropriate for this context *)
                from_expression env {e with exp_env=tenv}
            | _, Some e ->
                from_expression env e
          in
          env, t::acc
        in
        let env,ts = List.fold_righti aux es (env,[]) in
        env, conv_primitive_app t ts typ exp_loc
    | Texp_match(e,pats,tp) ->
        let env,t = from_expression env e in
        let env,pats' = from_list from_case env pats in
        let pats'' =
          match tp with
          | Total -> pats'
          | Partial -> pats' @ [make_pvar (Id.new_var t.typ), make_fail ~loc:exp_loc typ]
        in
        env, make_match t pats''
    | Texp_try(e,pats) ->
        let typ_excep = TData "exn" in
        let x = Id.new_var ~name:"e" typ_excep in
        let env,pats' = from_list from_case env pats in
        let pats'' = pats' @ [make_pany typ_excep, {desc=Raise(make_var x); typ; attr=[]}] in
        let env,t = from_expression env e in
        env, {desc=TryWith(t, Term.(fun_ x (match_ (var x) pats''))); typ; attr=[]}
    | Texp_tuple es ->
        let env,ts = from_list from_expression env es in
        env, {desc=Tuple ts; typ; attr=[]}
    | Texp_construct(_,desc,es) ->
        let env,ts = from_list from_expression env es in
        let desc =
          match get_constr_name desc typ env, ts with
          | "()",[] -> Const Unit
          | "true",[] -> Const True
          | "false",[] -> Const False
          | "[]",[] -> Nil
          | "::",[t1;t2] -> Cons(t1, t2)
          | "None",[] -> TNone
          | "Some",[t] -> TSome t
          | "Format",_ -> Const (String "%some format%")
          | name,es ->
              add_exc_env_from_constr desc env tenv;
              Debug.printf "CONSTR: %s@." name;
              Debug.printf "   typ: %a@." Printtyp.type_expr exp_type;
              Constr(name, ts)
        in
        env, {desc; typ; attr=[]}
    | Texp_variant(name, expr) ->
        let env,ts =
          match expr with
          | None -> env, []
          | Some expr' ->
              let env,t = from_expression env expr' in
              let ts =
                match t with
                | {desc=Tuple ts} -> ts
                | _ -> [t]
              in
              env, ts
        in
        let desc = Constr(name, ts) in
        env, {desc; typ; attr=[]}
    | Texp_record({fields; extended_expression=None}) ->
        let fields' =
          fields
          |> Array.to_list
          |> List.sort (fun (lbl1,_) (lbl2,_) -> compare lbl1.lbl_pos lbl2.lbl_pos)
        in
        let env,fields'' =
          let aux env (label,lbl_def) =
            let env,t =
              match lbl_def with
              | Overridden(_,e) -> from_expression env e
              | _ -> assert false
            in
            env, (get_label_name label env, t)
          in
          from_list aux env fields'
        in
        env, {desc=Record fields''; typ; attr=[]}
    | Texp_record{fields; extended_expression=Some init} ->
        let labels = Array.to_list (fst fields.(0)).lbl_all in
        let r = Id.new_var ~name:"r" typ in
        let env,fields' =
          let aux env lbl =
            let name = get_label_name lbl env in
            let _,e = Array.find (fun (lbl',_) -> lbl.lbl_name = lbl'.lbl_name) fields in
            let env,t =
              match e with
              | Overridden(_,e) -> from_expression env e
              | Kept _ ->
                  let env,typ = from_type_expr env tenv lbl.lbl_arg in
                  env, {desc=Field(make_var r,name); typ; attr=[]}
            in
            env, (name, t)
          in
          from_list aux env labels
        in
        let env,t = from_expression env init in
        env, make_let [r, t] {desc=Record fields';typ; attr=[]}
    | Texp_field(e,_,label) ->
        let env,t = from_expression env e in
        env, {desc=Field(t, get_label_name label env); typ; attr=make_attr[t]}
    | Texp_setfield(e1,_,label,e2) ->
        let env,t1 = from_expression env e1 in
        let env,t2 = from_expression env e2 in
        env, {desc=SetField(t1, get_label_name label env, t2); typ; attr=[]}
    | Texp_array es ->
        let typ' = array_typ typ in
        let env,ts = from_list from_expression env es in
        let array_of_list = make_var @@ Id.new_var ~name:"Array.of_list" ~attr:[Id.External] @@ make_tfun (make_tlist typ') typ in
        env, Term.(array_of_list @ [list ~typ:typ' ts])
    | Texp_ifthenelse(e1,e2,e3) ->
        let env,t1 = from_expression env e1 in
        let env,t2 = from_expression env e2 in
        let env,t3 =
          match e3 with
          | None -> env, unit_term
          | Some e3 -> from_expression env e3
        in
        env, make_if t1 t2 t3
    | Texp_sequence(e1,e2) ->
        let env,t1 = from_expression env e1 in
        let env,t2 = from_expression env e2 in
        env, make_seq t1 t2
    | Texp_while(e1,e2) ->
        let env,t1 = from_expression env e1 in
        let env,t2 = from_expression env e2 in
        let x = Id.new_var Ty.unit in
        let f = Id.new_var ~name:"while" Ty.(fun_ unit unit) in
        let t2' = Term.(if_ t1 (seq t2 (var f @ [unit])) unit) in
        env, Term.(let_ [f, fun_ x t2'] (var f @ [unit]))
    | Texp_for(x, _, e1, e2, dir, e3) ->
        let env,t1 = from_expression env e1 in
        let env,t2 = from_expression env e2 in
        let env,t3 = from_expression env e3 in
        let x' = from_ident x Ty.int in
        if Type.can_unify t3.typ Ty.unit then
          Type.unify t3.typ Ty.unit
        else
          unsupported "The body of a for-expression must have type unit";
        let f = Id.new_var ~name:"for" Ty.(TFun(Id.new_var ~name:"i" int, unit)) in
        let init = Id.new_var ~name:"init" Ty.int in
        let last = Id.new_var ~name:"last" Ty.int in
        let t =
          if !Flag.Method.abst_for_loop then
            let op =
              match dir with
              | Upto -> Term.(<=)
              | Downto -> Term.(>=)
            in
            let asm =
              match dir with
              | Upto -> Term.(assume (var init <= var x' && var x' <= var last))
              | Downto -> Term.(assume (var last <= var x' && var x' <= var init))
            in
            Term.(if_ (op (var init) (var last)) (let_ [x', randi] (asm t3)) unit)
          else
            let t31 =
              match dir with
              | Upto -> Term.(var x' <= var last)
              | Downto -> Term.(var x' >= var last)
            in
            let t32 =
              let x'' =
                match dir with
                | Upto -> Term.(var x' + int 1)
                | Downto -> Term.(var x' - int 1)
              in
              Term.(seq t3 (var f @ [x'']))
            in
            Term.(let_ [f, fun_ x' (if_ t31 t32 unit)] (var f @ [var init]))
        in
        env, Term.(lets [init,t1; last,t2] t)
    | Texp_send _
      | Texp_new _ -> unsupported "expression (class)"
    | Texp_instvar _ -> unsupported "expression (instvar)"
    | Texp_setinstvar _ -> unsupported "expression (setinstvar)"
    | Texp_override _ -> unsupported "expression (override)"
    | Texp_letmodule(m, loc, _, mb_expr, e) ->
        let env, m', mdl = from_module_expr_top env m mb_expr in
        let env,t = from_expression env e in
        env, Term.(let_ [m',mdl] t)
    | Texp_letexception _ -> unsupported "expression (let exception)"
    | Texp_assert e ->
        let s = Format.asprintf "%a" print_location exp_loc in
        if !Flag.Print.assert_loc then Format.printf "Found assertion: %s@." s;
        let force = [] <> from_attributes exp_attributes || Flag.Method.(!target <> "" && String.exists s !target) in
        let env,t = from_expression env e in
        let t' =
          if t.desc = Const False
          then make_fail ~force ~loc:exp_loc typ
          else make_assert ~force ~loc:exp_loc t
        in
        env, t'
    | Texp_lazy e -> assert false
    | Texp_object _ -> unsupported "expression (class)"
    | Texp_pack _ -> unsupported "expression (pack)"
    | Texp_unreachable -> unsupported "Texp_unreachable"
    | Texp_extension_constructor _ -> unsupported "Texp_extension_constructor"
    | Texp_letop _ -> unsupported "Texp_letop"
    | Texp_open _ -> unsupported "Texp_open"
  in
  env, t

and from_case env {c_lhs;c_guard;c_rhs} : env * (pattern * term) =
  let env,p = from_pattern env c_lhs in
  let env,t =
    let env = {env with id_env=get_bv_pat p @ env.id_env} in
    from_expression env c_rhs
  in
  let env,p' =
    match c_guard with
    | None -> env, p
    | Some e ->
        let env,t = from_expression env e in
        env, Pat.when_ p t
  in
  env, (p', t)

and from_exception_declaration tdecls = List.map from_type_expr tdecls


and from_module_binding env tenv mb : env * (Asttypes.rec_flag * declaration) list =
  let env,m,mdl = from_module_expr_top env mb.mb_id mb.mb_expr in
  env, [Nonrecursive, Decl_let [m,mdl]]

and from_module_type env mty =
  match Mtype.scrape env mty with
  | Mty_ident path -> TData (Path.name path)
  | Mty_signature sgn -> TModule []
  | Mty_functor(id, None, mty2) -> unsupported "Mty_functor"
  | Mty_functor(id, Some mty1, mty2) -> TFun(from_ident id @@ from_module_type env mty1, from_module_type env mty2)
  | Mty_alias path -> TData (Path.name path)

and from_module_expr_top env mb_id mb_expr : env * id * term =
  let md_prefix_orig = env.md_prefix in
  let md_prefix = md_prefix_orig ^ Ident.name mb_id ^ "." in
  let env = {env with md_prefix} in
  let env,mdl = from_module_expr env mb_expr in
  let m = Id.add_attr Id.Module @@ from_ident mb_id mdl.typ in
  let ty_decl',ty_decl_ext' = List.partition (fun (s,_) -> String.contains s '.') env.ty_decl_ext in
  let ty_decl = ty_decl' @ env.ty_decl in
  let ty_decl_ext = ty_decl_ext' @ env.ty_decl_ext in
  let env = {env with ty_decl; ty_decl_ext; md_prefix=md_prefix_orig} in
  env, m, mdl

and from_module_expr env mb_expr : env * term =
  match mb_expr.mod_desc with
  | Tmod_structure struc ->
      let env, decls = from_structure env struc in
      let mdl = make_module @@ List.map snd decls in
      let id_env =
        let map =
          let aux (_,decl) =
            match decl with
            | Decl_let defs -> List.map fst defs
            | Decl_type _ -> []
          in
          List.flatten_map aux decls
        in
        map @ env.id_env
      in
      {env with id_env}, mdl
  | Tmod_ident(path,loc) ->
      let ty = from_module_type mb_expr.mod_env mb_expr.mod_type in
      env, make_var @@ Id.make 0 (Path.name path) [Id.Module] ty
  | Tmod_functor(id, loc, mty, expr) ->
      let ty =
        match mty with
        | None -> unsupported "Tmod_functor"
        | Some {mty_desc;mty_type;mty_env;mty_loc;mty_attributes} ->
            match mty_desc with
            | Tmty_ident(path,_) -> TData (Path.name path)
            | _ -> assert false
      in
      let m = from_ident id ty in
      let env,mdl = from_module_expr env expr in
      env, make_fun m mdl
  | Tmod_apply(e1,e2,_) ->
      let env,t1 = from_module_expr env e1 in
      let env,t2 = from_module_expr env e2 in
      env, make_app t1 [t2]
  | Tmod_constraint(expr, _, _, _) -> from_module_expr env expr
  | Tmod_unpack _ -> unsupported "Tmod_unpack"

and from_str_item env str_item : env * (Asttypes.rec_flag * declaration) list =
  let tenv = str_item.str_env in
  match str_item.str_desc with
  | Tstr_eval(e,_) ->
      let env,t = from_expression env e in
      env, [Nonrecursive, Decl_let[Id.new_var ~name:"u" t.typ, t]]
  | Tstr_value(Asttypes.Recursive,pats) ->
      let env,pats' =
        let aux env {vb_pat;vb_expr} =
          let env,p = from_pattern env vb_pat in
          let env,e = from_expression env vb_expr in
          match p.pat_desc with
          | PVar x -> env, (x, e)
          | _ -> fatal "Only variables are allowed as left-hand side of 'let rec'"
        in
        from_list aux env pats
      in
      env, [Recursive, Decl_let pats']
  | Tstr_value(Asttypes.Nonrecursive,pats) ->
      let env,decls =
        let aux env {vb_pat;vb_expr} =
          let env,p = from_pattern env vb_pat in
          let env,t = from_expression env vb_expr in
          let x,t =
            match p.pat_desc with
            | PVar x -> x, t
            | PConst {desc=Const Unit} -> Id.new_var ~name:"u" Ty.unit, t
            | PAny -> new_var_of_term t, t
            | _ -> unsupported "Only variables are allowed as left-hand side of 'let'"
          in
          env, (Nonrecursive, Decl_let [x,t])
        in
        from_list aux env pats
      in
      env, decls
  | Tstr_primitive _ -> env, []
  | Tstr_type(rec_flag,decls) ->
      if rec_flag = Nonrecursive then unsupported "Non recursive type declaration";
      let env,decls' = from_list (from_type_declaration tenv) env decls in
      let ty_decl = decls' @ env.ty_decl in
      {env with ty_decl}, [rec_flag, Decl_type decls']
  | Tstr_typext _ -> unsupported "typext"
  | Tstr_exception _ -> env, []
  | Tstr_module mb -> from_module_binding env tenv mb
  | Tstr_recmodule _
    | Tstr_modtype _ -> env, []
  | Tstr_open _ -> env, []
  | Tstr_class _
    | Tstr_class_type _ -> unsupported "class"
  | Tstr_include _ -> env, []
  | Tstr_attribute _ -> env, []

and from_structure env struc : env * (Asttypes.rec_flag * declaration) list =
  Debug.printf "struc: @[%a@." Printtyped.implementation struc;
  let aux (env,decls) str_item =
    let env,decls' = from_str_item env str_item in
    env, decls@decls'
  in
  List.fold_left aux (env,[]) struc.str_items

let from_top_level_phrase (tenv,(env,decls)) ptop : Env.t * (env * (Asttypes.rec_flag * declaration) list) =
  match ptop with
  | Parsetree.Ptop_dir _ -> unsupported "toplevel_directive"
  | Parsetree.Ptop_def struc ->
      let struc',_,_,tenv' = Typemod.type_structure tenv struc Location.none in
      let env,decls' = from_structure env struc' in
      tenv', (env, decls @ decls')

let alpha_rename_decls fdecls =
  let shadowed =
    let aux (flag,decl) =
      match flag, decl with
      | Nonrecursive, Decl_let defs ->
          let fs = List.map fst defs in
          let fv = List.flatten_map (snd |- get_fv) defs in
          List.filter (Id.mem -$- fv) fs
      | _ -> []
    in
    List.flatten_map aux fdecls
  in
  let rec aux (map,acc_rev) (flag,decl) =
    match flag, decl with
    | Nonrecursive, Decl_let defs ->
        let fs = List.map fst defs in
        let map_new =
          fs
          |> List.filter (Id.mem -$- shadowed)
          |> List.map (Pair.add_right Id.new_var_id)
        in
        let map' = map_new @ map in
        let defs' =
          let aux (x,t) =
            let x' =
              if Id.mem x shadowed then
                Id.set_typ (Id.assoc x map_new) (Id.typ x)
              else
                x
            in
            x', subst_var_map_without_typ map t
          in
          List.map aux defs
        in
        map', Decl_let defs'::acc_rev
    | _ -> map, decl::acc_rev
  in
  List.rev @@ snd @@ List.fold_left aux ([],[]) fdecls

let parse_lexbuf ?tenv ?env lb =
  let tenv =
    match tenv with
    | None ->
        let env = Compmisc.initial_env () in
        init_exc_env ();
        env
    | Some env -> env
  in
  let orig = Parse.use_file lb in
  let env = Option.default init_env env in
  let _,(env,fdecls) = List.fold_left from_top_level_phrase (tenv,(env,[])) orig in
  tenv, orig, env, alpha_rename_decls fdecls

let parse_file ?tenv ?env filename =
  IO.CPS.open_in filename (fun cin ->
    let lb = Lexing.from_channel cin in
    lb.Lexing.lex_curr_p <-
      {Lexing.pos_fname = filename;
       Lexing.pos_lnum = 1;
       Lexing.pos_cnum = 0;
       Lexing.pos_bol = 0};
    parse_lexbuf ?tenv ?env lb)

let make_tdecl tdecls t =
  let tdecls' =
    tdecls
    |> List.filter_out (fun (s,ty) -> TData s = ty)
    |> List.sort_unique (Compare.on fst)
  in
  Term.local (Decl_type tdecls') t

let remove_TVarLazy =
  let tr = make_trans () in
  let tr_typ ty =
    match ty with
    | TVarLazy f -> tr.tr_typ !!f
    | _ -> tr.tr_typ_rec ty
  in
  tr.tr_typ <- tr_typ;
  tr.tr_term

let parse_files filenames =
  Warnings.parse_options false "-3-10";
  let aux filename (origs,tenv,env,last_mod,cont) =
    let tenv,orig,env,decls = parse_file ?tenv ~env filename in
    let mod_var =
      let name =
        filename
        |> Filename.basename
        |> Filename.chop_extension_if_any
        |> String.capitalize
      in
      let ty = Type.TData name in
      Id.new_var ~name ty
    in
    let cont' =
      if filename = List.hd filenames then
        List.fold_right Term.local decls |- cont
      else
        Term.(let_ [mod_var, module_ decls] |- cont)
    in
    let env =
      let ty_decl_ext = List.filter_out (fst |- Id.is_in_module_string mod_var) env.ty_decl_ext in
      {env with ty_decl_ext}
    in
    orig::origs, Some tenv, env, false, cont'
  in
  let origs,_,env,_,cont =
    let dirs = Load_path.get_paths () in
    List.iter (Load_path.add_dir -| Filename.dirname) !Flag.Input.filenames;
    let r = List.fold_right aux filenames ([],None,init_env,true,Fun.id) in
    Load_path.init dirs;
    r
  in
  origs,
  cont Term.eod
  |> make_tdecl env.ty_decl_ext
  |> remove_TVarLazy
  |> subst_tdata "exn" !!exc_typ
