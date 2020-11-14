# 2 "parser_wrapper_4.09.ml"
open Util
open Asttypes
open Typedtree
open Types
open Syntax
open Term_util
open Type
open Parser_wrapper_common

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let () = Compmisc.init_path ()

let add_load_path = Load_path.add_dir

let report_error e = Location.report_exception Format.err_formatter e

let prim_typs =
  ["unit", Ty.unit;
   "bool", Ty.bool;
   "int", Ty.int;
   "format", Ty.prim "string";
   "format4", Ty.prim "string";
   "format6", Ty.prim "string";
   "CamlinternalFormatBasics.fmt", Ty.prim "string";
   "CamlinternalFormatBasics.format6", Ty.prim "string";
   "exn", TData "exn";
   "open_flag", TData "open_flag";
   "fpclass", TData "fpclass"]
    @ List.map (fun s -> s, TBase (TPrim s)) prim_base_types

let name_of_longident id =
  String.join "." @@ Longident.flatten id
let name_of_longident_loc loc =
  name_of_longident loc.txt

let from_mutable_flag = function
  | Asttypes.Mutable -> Mutable
  | Asttypes.Immutable -> Immutable

let from_rec_flag = function
  | Asttypes.Recursive -> Recursive
  | Asttypes.Nonrecursive -> Nonrecursive

let stdlib_prefix = "Stdlib."

let prim_typ_constr =
  ["list", "list";
   "ref", "ref";
   "option", "option";
   "array", "array";
   "lazy_t", "lazy_t"]
let prim_typ_constr = List.map (Pair.map_fst ((^) stdlib_prefix)) prim_typ_constr @ prim_typ_constr

let is_prim_constr constrs =
  match constrs with
  | ["[]", []; "::", ty::_] -> Some (Ty.list ty)
  | _ -> None

let add_tconstr ty_desc env =
  match ty_desc with
  | Tconstr(path, _, _) ->
      let tconstrs = List.cons_unique path env.tconstrs in
      {env with tconstrs}
  | _ -> env

let wrap_letters_with_sign s =
  let ss,s' = Id.decomp_prefixes_string s in
  let s'' =
    if String.contains "!$%&*+-./:<=>?@^|~" s'.[0] then
      "(" ^ s' ^ ")"
    else
      s'
  in
  String.join "." (ss@[s''])

let string_of_path path =
  let s = Path.name path in
  let s = wrap_letters_with_sign s in
  let prefix = "Stdlib__" in
  if false && String.starts_with s stdlib_prefix then
    String.lchop ~n:(String.length stdlib_prefix) s
  else if String.starts_with s prefix then
    String.lchop ~n:(String.length prefix) s
    |> String.capitalize
    |> (^) "Stdlib."
  else
    s

let prefix_of_string s =
  try
    s
    |> String.rsplit ~by:"."
    |> fst
    |> (-$-) (^) "."
  with Not_found -> ""

let prefix_of_path = string_of_path |- prefix_of_string

let add_mod_prefix_exc ~before ~after m =
  let exc_env =
    let prefix = Id.prefix_for_module m in
    let map =
      match Id.typ m with
      | TModule sgn ->
          sgn
          |> types_in_signature
          |> List.fold_right (fun (s,_) ty -> subst_tdata_typ s (TData (prefix ^ s)) ty)
      | TFun _ -> Fun.id
      | _ ->
          Format.printf "m: %a@." Print.id_typ m;
          assert false
    in
    let env_diff = List.Set.diff ~eq:(Compare.eq_on fst) after.exc_env before.exc_env in
    let add (s,tys) =
      if List.mem_assoc s Predef.builtin_idents || String.starts_with s "Stdlib" then
        s, tys
      else
        s, List.map map tys
    in
    List.map add env_diff @ before.exc_env
  in
  {after with exc_env}

let from_list f env xs =
  let aux x (env,acc) =
    let env,x' = f env x in
    env, x'::acc
  in
  List.fold_right aux xs (env,[])

let rec from_types_type_declaration env tenv ?(prefix="") s (decl:Types.type_declaration) : env * typ =
  match decl.type_kind with
  | Type_abstract ->
      begin
        match decl.type_manifest with
        | None -> env, TData s
        | Some ty -> from_type_expr env tenv ty
      end
  | Type_variant constrs ->
      let aux {cd_id;cd_args} (env,constrs) =
        match cd_args with
        | Cstr_tuple args ->
            let s = Ident.name cd_id in
            let env,tys = from_type_exprs env tenv args in
            env, (prefix^s,tys)::constrs
        | Cstr_record _ -> unsupported "Cstr_record"
      in
      let env,constrs = List.fold_right aux constrs (env,[]) in
      let ty' = Option.default (TVariant(false, constrs)) @@ is_prim_constr constrs in
      env, ty'
  | Type_record(fields, _) ->
      let aux {ld_id;ld_mutable;ld_type} (env,fields) =
        let s = Ident.name ld_id in
        let flag = from_mutable_flag ld_mutable in
        let env, ty = from_type_expr env tenv ld_type in
        env, (prefix^s, (flag, ty))::fields
      in
      let env,fields = List.fold_right aux fields (env,[]) in
      env, TRecord fields
  | Type_open -> env, !!new_tvar
  | exception Not_found -> assert false

and from_type_exprs env tenv tys : env * typ list =
  let aux ty (env,tys) =
    let env,ty' = from_type_expr env tenv ty in
    env, ty'::tys
  in
  List.fold_right aux tys (env,[])

and from_row_desc env tenv row_desc =
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
      let env,ty = from_type_expr env tenv row_desc.row_more in
      let constrs =
        match ty with
        | TVar _ -> []
        | TVariant(_,constrs) -> constrs
        | _ -> assert false
      in
      env, constrs
  in
  env, constrs1 @ constrs2

and from_type_expr env tenv ty0 : env * typ =
  let typ = Ctype.correct_levels ty0 in
  let typ' = (if false then Ctype.repr else Ctype.full_expand tenv) typ in
(*
  Debug.printf "%sty1: %a@." space Printtyp.type_expr typ;
  Debug.printf "%sty2: %a@." space Printtyp.type_expr typ';
  Debug.printf "%sty3: %a@.@." space Printtyp.raw_type_expr typ';
 *)
  let env = add_tconstr typ'.Types.desc env in
  match typ'.Types.desc with
  | Tvar _ ->
      let env,ty =
        match List.assoc_opt typ'.Types.id env.tvar_env with
        | None ->
            let ty = !!new_tvar in
            let tvar_env = (typ'.Types.id, ty)::env.tvar_env in
            {env with tvar_env}, ty
        | Some ty -> env, ty
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
  | Tconstr(path, _, _) when List.mem_assoc (string_of_path path) prim_typs ->
      env, List.assoc (string_of_path path) prim_typs
  | Tconstr(path, typs, _) when List.mem_assoc (string_of_path path) prim_typ_constr ->
      let env,tys = from_type_exprs env tenv typs in
      env, TApp(List.assoc (string_of_path path) prim_typ_constr, tys)
  | Tconstr(path, _typs, _) ->
      let s = string_of_path path in
      env, TData s
  | Tobject _ -> unsupported "Tobject"
  | Tfield _ -> unsupported "Tfield"
  | Tnil -> unsupported "Tnil"
  | Tlink _ -> unsupported "Tlink"
  | Tsubst _ -> unsupported "Tsubst"
  | Tvariant row_desc ->
      let env,constrs = from_row_desc env tenv row_desc in
      env, TVariant(true, constrs)
  | Tunivar _ -> unsupported "Tunivar"
  | Tpoly(typ,[]) -> from_type_expr env tenv typ
  | Tpoly _ -> unsupported "Tpoly"
  | Tpackage _ -> unsupported "Tpackage"

let from_typedtree_type_declaration tenv env (decl:Typedtree.type_declaration) : env * (string * typ) =
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
              let env,tys = from_type_exprs env tenv @@ List.map (fun arg -> arg.ctyp_type) args in
              env, (s,tys)::constrs
          | Cstr_record _ -> unsupported "Cstr_record"
        in
        let env,constrs = List.fold_right aux constrs (env,[]) in
        env, TVariant(false, constrs)
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

let from_ident_aux name attr typ =
  let name = if name.[0] = '_' then "u" ^ name else name in
  let id = 0 in
  Id.make id name attr typ

let from_ident x typ =
  from_ident_aux (Ident.name x) [] typ

let from_ident_path ?loc env path typ =
  let name = string_of_path path in
  let x =
    try
      Id.set_typ (List.find (Id.name |- (=) name) env.id_env) typ
    with Not_found ->
      let attr = [] in
      from_ident_aux name attr typ
  in
  match loc with
  | None -> x
  | Some loc -> Id.(add_attr (Loc loc) x)

let get_constr_name desc _typ _env =
  match desc.cstr_tag with
  | Cstr_constant _ -> desc.cstr_name
  | Cstr_block _ -> desc.cstr_name
  | Cstr_extension(path, _) -> string_of_path path
  | Cstr_unboxed -> unsupported "Cstr_unboxed"

let get_label_name prefix label =
  prefix ^ label.lbl_name

let add_exc_env_from_constr cstr_desc env tenv =
  match cstr_desc.cstr_res.Types.desc with
  | Tconstr(path,_,_) ->
      if string_of_path path = "exn" then
        let name = get_constr_name cstr_desc cstr_desc.cstr_res env in
        let _,typs = from_type_exprs env tenv cstr_desc.cstr_args in
        add_exc_env name typs env
      else
        env
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
    | Tpat_construct(loc, _, []) when name_of_longident_loc loc = "None" -> env, PNone
    | Tpat_construct(loc, _, [p]) when name_of_longident_loc loc = "Some" ->
        let env,p' = from_pattern env p in
        env, PSome p'
    | Tpat_construct(loc, _, []) when name_of_longident_loc loc = "()" -> env, PConst unit_term
    | Tpat_construct(loc, _, []) when name_of_longident_loc loc = "[]" -> env, PNil
    | Tpat_construct(loc, _, [p1;p2]) when name_of_longident_loc loc = "::" ->
        let env,p1' = from_pattern env p1 in
        let env,p2' = from_pattern env p2 in
        env, PCons(p1', p2')
    | Tpat_construct(loc, _, []) when typ' = Ty.bool ->
        begin match name_of_longident_loc loc with
        | "true" -> env, PConst Term.true_
        | "false" -> env, PConst Term.false_
        | _ -> assert false
        end
    | Tpat_construct(loc, cstr_desc, ps) ->
        let env = add_exc_env_from_constr cstr_desc env pat_env in
        let name = name_of_longident_loc loc in
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
        let aux (loc,_,p) (env,ps) =
          let s = name_of_longident_loc loc in
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



let conv_primitive_app env t ts typ loc =
  let is x s = Id.name x = s || Id.name x = stdlib_prefix ^ s in
  match t.desc,ts with
  | Var x, [t1] when is x "List.length" -> env, Term.(length t1)
  | Var x, [t1;t2] when is x "(@@)" -> env, Term.(t1 @@ [t2])
  | Var x, [t1;t2] when is x "(=)" -> env, Term.(t1 = t2)
  | Var x, [t1;t2] when is x "(<>)" -> env, Term.(t1 <> t2)
  | Var x, [t1;t2] when is x "(<)" -> env, Term.(t1 < t2)
  | Var x, [t1;t2] when is x "(>)" -> env, Term.(t1 > t2)
  | Var x, [t1;t2] when is x "(<=)" -> env, Term.(t1 <= t2)
  | Var x, [t1;t2] when is x "(>=)" -> env, Term.(t1 >= t2)
  | Var x, [t1;t2] when is x "(&&)" -> env, Term.(t1 && t2)
  | Var x, [t1;t2] when is x "(||)" -> env, Term.(t1 || t2)
  | Var x, [t1;t2] when is x "(+)" -> env, Term.(t1 + t2)
  | Var x, [t1;t2] when is x "(-)" -> env, Term.(t1 - t2)
  | Var x, [t1;t2] when is x "(*)" -> env, Term.(t1 * t2)
  | Var x, [t1;t2] when is x "(/)" ->
      let t2' =
        let make_check t = Term.(seq (assert_ ~loc (t <> int 0)) t) in
        if has_no_effect t2 then
          make_check t2
        else
          let x = Id.new_var Ty.int in
          Term.(let_ [x,t2] (make_check (var x)))
      in
      env, Term.(t1 / t2')
  | Var x, [t] when is x "(~-)" -> env, Term.(~- t)
  | Var x, [t] when is x "not" -> env, Term.(not t)
  | Var x, [t] when is x "fst" -> env, Term.(fst t)
  | Var x, [t] when is x "snd" -> env, Term.(snd t)
  | Var x, [t] when is x "raise" -> env, make_raise t typ
  | Var x, [t] when is x "ref" -> env, Term.(ref t)
  | Var x, [{desc=Const Unit}] when is x "read_int" ->
      let attr =
        if Flag.(List.mem !mode [NonTermination; FairNonTermination]) then
          AAbst_under::randint_term.attr
        else
          randint_term.attr in
      env, Term.({randint_term with attr} @@ [unit])
  | Var x, [t] when is x "(!)" -> env, Term.(!t)
  | Var x, [t1;t2] when is x "(:=)" -> env, Term.(t1 := t2)
  | Var x, [{desc=Const Unit}] when is x "Random.bool" -> env, Term.randb
  | Var x, [{desc=Const (Int 0)}] when is x "Random.int" -> env, Term.randi
  | Var x, [t] when is x "Random.int" ->
      let x = Id.new_var ~name:"n" Ty.int in
      env,
      Term.(let_ [x, randi]
            (assume (int 0 <= var x && var x < t)
            (var x)))
  | Var x, [{desc=Const(Int _)}] when is x "open_in" -> env, make_event_unit "newr"
  | Var x, [{typ=TBase TUnit}] when is x "close_in" -> env, make_event_unit "close"
  | Var x, [{desc=Const(String s)}] when is x "event" -> env, make_event_unit s
  | Var x, [t] when is x "failwith" ->
      let s = stdlib_prefix ^ "Failure" in
      let env = add_exc_env s [t.typ] env in
      env, make_raise (make_construct s [t] (TData "exn")) typ
  | Var x, [t] when is x "invalid_arg" ->
      let s = stdlib_prefix ^ "Invalid_argument" in
      let env = add_exc_env s [t.typ] env in
      env, make_raise (make_construct s [t] (TData "exn")) typ
  | _ -> env, make_app t ts



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
    match attr_payload with
    | Parsetree.PStr [{pstr_desc=Pstr_eval({pexp_desc=Pexp_ident x},_)}] when name_of_longident_loc x = "target" ->
        Some ()
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
    | Texp_ident(path, _, _) ->
        let x = from_ident_path ~loc:exp_loc env path typ in
        if !Flag.Print.id_loc <> "" && String.exists (Id.to_string x) !Flag.Print.id_loc then
          Format.printf "Found variable %a: %a@." Print.id x Print.location exp_loc;
        env, make_var x
    | Texp_constant c ->
        env, {desc = Const (from_constant c); typ; attr=const_attr}
    | Texp_let(_, [{vb_pat;vb_expr}], e2)
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
        let aux (a,b) (env,acc) =
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
        let env,ts = List.fold_right aux es (env,[]) in
        conv_primitive_app env t ts typ exp_loc
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
    | Texp_construct(loc,desc,es) ->
        let env,ts = from_list from_expression env es in
        let env,desc =
          match name_of_longident_loc loc, ts with
          | "()",[] -> env, Const Unit
          | "true",[] -> env, Const True
          | "false",[] -> env, Const False
          | "[]",[] -> env, Nil
          | "::",[t1;t2] -> env, Cons(t1, t2)
          | "None",[] -> env, TNone
          | "Some",[t] -> env, TSome t
          | "CamlinternalFormatBasics.Format",_ -> env, Const (String "%some format%")
          | name,_ ->
              let env = add_exc_env_from_constr desc env tenv in
              Debug.printf "CONSTR: %s@." name;
              Debug.printf "   typ: %a@." Printtyp.type_expr exp_type;
              env, Constr(name, ts)
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
        let env,fields'' =
          let aux env (_,lbl_def) =
            let name,(env,t) =
              match lbl_def with
              | Overridden(loc,e) ->
                  name_of_longident_loc loc,
                  from_expression env e
              | _ -> assert false
            in
            env, (name, t)
          in
          fields
          |> Array.to_list
          |> List.sort (fun (lbl1,_) (lbl2,_) -> compare lbl1.lbl_pos lbl2.lbl_pos)
          |> from_list aux env
        in
        env, {desc=Record fields''; typ; attr=[]}
    | Texp_record{fields; extended_expression=Some init} ->
        let labels = Array.to_list (fst fields.(0)).lbl_all in
        let r = Id.new_var ~name:"r" typ in
        let env,fields' =
          let aux env lbl =
            let prefix =
              match Array.find (function (_, Overridden _) -> true | _ -> false) fields with
              | _, Overridden(loc,_) -> prefix_of_string @@ name_of_longident_loc loc
              | _ -> assert false
              | exception Not_found -> assert false
            in
            let _,e = Array.find (fun (lbl',_) -> lbl.lbl_name = lbl'.lbl_name) fields in
            let name,(env,t) =
              match e with
              | Overridden(loc,e) ->
                  name_of_longident_loc loc,
                  from_expression env e
              | Kept _ ->
                  let env,typ = from_type_expr env tenv lbl.lbl_arg in
                  let name = get_label_name prefix lbl in
                  name, (env, {desc=Field(make_var r,name); typ; attr=[]})
            in
            env, (name, t)
          in
          from_list aux env labels
        in
        let env,t = from_expression env init in
        env, make_let [r, t] {desc=Record fields'; typ; attr=[]}
    | Texp_field(e,loc,_) ->
        let name = name_of_longident_loc loc in
        let env,t = from_expression env e in
        env, {desc=Field(t, name); typ; attr=make_attr[t]}
    | Texp_setfield(e1,loc,_,e2) ->
        let name = name_of_longident_loc loc in
        let env,t1 = from_expression env e1 in
        let env,t2 = from_expression env e2 in
        env, {desc=SetField(t1, name, t2); typ; attr=[]}
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
        if can_unify t3.typ Ty.unit then
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
    | Texp_letmodule(m, _loc, _, mb_expr, e) ->
        let env', m', mdl = from_module_expr_top env m mb_expr in
        let env = add_mod_prefix_exc ~before:env ~after:env' m' in
        let env,t = from_expression env e in
        env, Term.(let_ [m',mdl] t)
    | Texp_letexception _ -> unsupported "expression (let exception)"
    | Texp_assert e ->
        let s = Format.asprintf "%a" Print.location exp_loc in
        if !Flag.Print.assert_loc then Format.printf "Found assertion: %s@." s;
        let force = [] <> from_attributes exp_attributes || List.exists (String.exists s) !Flag.Method.targets in
        Ref.map (List.filter_out (String.exists s)) Flag.Method.targets;
        let env,t = from_expression env e in
        let t' =
          if t.desc = Const False
          then make_fail ~force ~loc:exp_loc typ
          else make_assert ~force ~loc:exp_loc t
        in
        env, t'
    | Texp_lazy _e -> assert false
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

and from_module_binding env _tenv mb =
  from_module_expr_top env mb.mb_id mb.mb_expr

and from_signature env tenv (sgn:Types.signature) =
  let aux item (env,items) =
    let env,item' = from_signature_item env tenv item in
    env, item'::items
  in
  let env,items = List.fold_right aux sgn (env,[]) in
  let sig_types = List.filter_map (function `Type (s, ty) -> Some (s, ty) | _ -> None) items in
  let sig_values = List.filter_map (function `Val x -> Some x | _ -> None) items in
  env, {sig_types; sig_values}

and from_signature_item env tenv sig_item =
  match sig_item with
  | Sig_value(id, val_desc, _) ->
      let env,ty = from_type_expr env tenv val_desc.val_type in
      env, `Val (from_ident id ty)
  | Sig_type(id, ty_decl, _, _) ->
      let s = Ident.name id in
      let env,ty = from_types_type_declaration env tenv s ty_decl in
      env, `Type (s, ty)
  | Sig_typext(_id,_,_,_) -> env, `Unsupported
  | Sig_module(m,_,mod_decl,_,_) ->
      let env,ty = from_module_type env tenv mod_decl.md_type in
      env, `Val (from_ident m ty)
  | Sig_modtype _ -> unsupported "Sig_modtype"
  | Sig_class _ -> unsupported "Sig_class"
  | Sig_class_type _ -> unsupported "Sig_class_type"


and from_module_type env tenv mty =
  match Mtype.scrape tenv mty with
  | Mty_ident path -> env, TData (string_of_path path)
  | Mty_signature sgn ->
      let env, sgn = from_signature env tenv sgn in
      env, TModule sgn
  | Mty_functor(_id, None, _mty2) -> unsupported "Mty_functor"
  | Mty_functor(id, Some mty1, mty2) ->
      let env, ty1 = from_module_type env tenv mty1 in
      let env, ty2 = from_module_type env tenv mty2 in
      env, TFun(from_ident id ty1, ty2)
  | Mty_alias _ ->
      from_module_type env tenv @@ Mtype.scrape_for_functor_arg tenv mty

and from_module_expr_top env mb_id mb_expr : env * id * term =
  let md_prefix_orig = env.md_prefix in
  let md_prefix = md_prefix_orig ^ Ident.name mb_id ^ "." in
  let env = {env with md_prefix} in
  let env,mdl = from_module_expr env mb_expr in
  let m = from_ident mb_id mdl.typ in
  let env = {env with md_prefix=md_prefix_orig} in
  env, m, mdl

and from_module_expr env mb_expr : env * term =
  match mb_expr.mod_desc with
  | Tmod_structure struc ->
      let env, fdecls = from_structure env struc in
      let decls = alpha_rename_decls fdecls in
      let mdl = make_module decls in
      let id_env =
        let map = List.flatten_map (function Decl_let defs -> List.map fst defs | _ -> []) decls in
        map @ env.id_env
      in
      {env with id_env}, mdl
  | Tmod_ident(path,_loc) ->
      let env, ty = from_module_type env mb_expr.mod_env mb_expr.mod_type in
      env, Term.var (Id.make 0 (string_of_path path) [] ty)
  | Tmod_functor(id, _loc, mty, expr) ->
      let ty =
        match mty with
        | None -> unsupported "Tmod_functor"
        | Some {mty_desc} ->
            match mty_desc with
            | Tmty_ident(path,_) -> TData (string_of_path path)
            | _ -> assert false
      in
      let m = from_ident id ty in
      let env,mdl = from_module_expr env expr in
      env, Term.fun_ m mdl
  | Tmod_apply(e1,e2,_) ->
      let env,t1 = from_module_expr env e1 in
      let env,t2 = from_module_expr env e2 in
      env, Term.(t1 @ [t2])
  | Tmod_constraint(expr, _, _, _) -> from_module_expr env expr
  | Tmod_unpack _ -> unsupported "Tmod_unpack"

and from_str_item env str_item : env * (rec_flag * Syntax.declaration) list =
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
      if rec_flag = Asttypes.Nonrecursive then unsupported "Non recursive type declaration";
      let flag = from_rec_flag rec_flag in
      let env,decls' = from_list (from_typedtree_type_declaration tenv) env decls in
      env, [flag, Decl_type decls']
  | Tstr_typext _ -> unsupported "typext"
  | Tstr_exception _ -> env, []
  | Tstr_module mb ->
      let env',m,mdl = from_module_binding env tenv mb in
      let env = add_mod_prefix_exc ~before:env ~after:env' m in
      env, [Nonrecursive, Decl_let [m,mdl]]
  | Tstr_recmodule _
  | Tstr_modtype _ -> env, []
  | Tstr_open {open_expr={mod_desc; mod_type}} ->
      begin
        match mod_desc with
        | Tmod_ident(path,_) ->
            let env,ty = from_module_type env tenv mod_type in
            let m = from_ident_path env path ty in
            env, [Nonrecursive, Open m]
        | _ -> unsupported "Tstr_open"
      end
  | Tstr_class _
  | Tstr_class_type _ -> unsupported "class"
  | Tstr_include _ -> env, []
  | Tstr_attribute _ -> env, []

and from_structure env struc : env * (rec_flag * Syntax.declaration) list =
  Debug.printf "struc: @[%a@." Printtyped.implementation struc;
  let aux (env,decls) str_item =
    let env,decls' = from_str_item env str_item in
    env, decls@decls'
  in
  List.fold_left aux (env,[]) struc.str_items

let from_top_level_phrase (tenv,(env,decls)) ptop : Env.t * (env * (rec_flag * Syntax.declaration) list) =
  match ptop with
  | Parsetree.Ptop_dir _ -> unsupported "toplevel_directive"
  | Parsetree.Ptop_def struc ->
      let struc',_,_,tenv' = Typemod.type_structure tenv struc Location.none in
      let env,decls' = from_structure env struc' in
      tenv', (env, decls @ decls')

let parse_lexbuf ?tenv ?env lb =
  let tenv = Option.default_delayed Compmisc.initial_env tenv in
  let orig = Parse.use_file lb in
  let env = Option.default init_env env in
  let tenv,(env,fdecls) = List.fold_left from_top_level_phrase (tenv,(env,[])) orig in
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
  t
  |> Term.local (Decl_type tdecls')
  |> Trans.split_type_decls

let rec col_typ_def env tenv acc rest =
  match rest with
  | [] -> env, acc
  | path::rest' ->
      let s = string_of_path path in
      let prefix = prefix_of_path path in
      let env,acc',rest'' =
        if List.mem_assoc s acc then
          env, acc, rest
        else
          let env',ty' = from_types_type_declaration env tenv ~prefix s @@ Env.find_type path tenv in
          let rest'' = List.Set.(env'.tconstrs - env.tconstrs) @ rest' in
          env', ((s,ty')::acc), rest''
      in
      col_typ_def env tenv acc' rest''

let parse_files filenames =
  Warnings.parse_options false "-3-10";
  let init_tenv = !!Compmisc.initial_env in
  let origs,tenv,env,cont =
    let dirs = Load_path.get_paths () in
    List.iter (Load_path.add_dir -| Filename.dirname) !Flag.Input.filenames;
    let aux filename (origs,tenv,env,cont) =
      let tenv,orig,env,decls = parse_file ~tenv ~env filename in
      let mod_var =
        let name =
          filename
          |> Filename.basename
          |> Filename.chop_extension_if_any
          |> String.capitalize
        in
        let ty = Type.TData name in
        let id = 0 in
        let attr = [] in
        Id.make id name attr ty
      in
      let cont' =
        if filename = List.hd filenames then
          List.fold_right Term.local decls |- cont
        else
          Term.(let_ [mod_var, module_ decls] |- cont)
      in
      orig::origs, tenv, env, cont'
    in
    let r = List.fold_right aux filenames ([],init_tenv,init_env,Fun.id) in
    Load_path.init dirs;
    r
  in
  let parsed =
    cont Term.eod
    |> subst_tdata "exn" (exc_typ env)
  in
  if not (List.for_all (fun s -> List.exists (fst |- (=) s) env.exc_env) !Flag.Method.target_exn) then
    (Format.eprintf "Invalid argument of -target-exn"; exit 1);
  let builtin_tys = List.map fst Predef.builtin_idents in
  let _env,ty_decl =
    env.tconstrs
    |> List.filter (Path.heads |- List.hd |- Ident.global)
    |> List.filter_out (string_of_path |- List.mem -$-  builtin_tys)
    |> List.filter_out (string_of_path |- List.mem_assoc -$- prim_typ_constr)
    |> List.filter_out (string_of_path |- String.starts_with -$- "CamlinternalFormatBasics.")
    |@> Debug.printf "tcontrs: %a@." Print.(list string) -| List.map string_of_path
    |> col_typ_def env tenv []
  in
  if !Flag.Method.targets <> [] then
    (Format.eprintf "Unused target: %a@." (print_list Format.pp_print_string ", ") !Flag.Method.targets; assert false);
  origs,
  make_tdecl ty_decl parsed
  |> Module.complete_prefix
