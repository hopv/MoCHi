open Util
open Type
open Type_util
open Syntax
open Term_util

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let abst_first_class_module_term,abst_first_class_module_typ =
  let tr = Tr2.make () in
  let make_bind used t1 =
    Flag.Abstract.use "First class module";
    let name = "FirstClassModule" in
    let t1' = tr.term used t1 in
    let f = gen_fresh_name_var_int !used @@ (Id.new_var ~name t1'.typ) in
    used := f :: !used;
    f, Term.let_ [f, t1']
  in
  tr.term <- (fun used t ->
    match t.desc with
    | Pack t1 ->
        let _,def = make_bind used t1 in
        let t =
          if has_fail t1 then
            Term.fail
          else
            Term.unit
        in
        let u = Id.new_var Ty.unit in
        def Term.(fun_ u t)
    | Unpack t1 ->
        let f,def = make_bind used t1 in
        let ty = tr.typ used t.typ in
        let t = Term.(var f @ [unit])in
        def Term.(seq t (rand ~expand:false ty))
    | _ -> set_afv_shallowly @@ tr.term_rec used t);
  tr.typ <- (fun used ty ->
    match ty with
    | TPackage _ -> Ty.(fun_ unit unit)
    | _ -> tr.typ_rec used ty);
  (fun t -> tr.term (ref (col_modules t)) t),
  tr.typ (ref [])

let abst_first_class_module (problem : Problem.t) =
  let term = abst_first_class_module_term problem.term in
  let ext_typ = Fmap.(list (snd (snd abst_first_class_module_typ))) problem.ext_typ in
  {problem with term; ext_typ}

(* TODO: ad-hoc *)
let subst_tconstr_label_by_name venv =
  let venv = List.filter (fst |- is_mod_var) venv in
  let is_delimiter = List.mem -$- ['.'; '('; ')'] in
  let replace str (by, sub) =
    let ss = String.split_on_string str ~by in
    if List.for_all (fun s -> s = "" || is_delimiter (String.last s) && is_delimiter s.[0]) ss then
      String.join sub ss
    else
      str
  in
  let map = List.map (Pair.map_same Id.name) venv in
  let f_str = List.fold_left replace -$- map in
  let f_path = Path.map_name f_str in
  let f_ty = map_path f_path in
  let tr = Tr.make () in
  tr.typ <- f_ty;
  tr.term

(* substitute ext_row_path in Type_ext *)
let subst_ext_path_map =
  let tr = Tr2.make () in
  let sbst = List.subst ~eq:Path.eq in
  let tr_desc map desc =
    match desc with
    | Local(Type_ext (Ext_type (path,(params,row))), t) when not (Path.eq path row.ext_row_path) (* ??? *) ->
        let row' = {row with ext_row_path = sbst map row.ext_row_path} in
        Local(Type_ext (Ext_type (path,(params,row'))), tr.term map t)
    | Local(Type_ext (Ext_rebind (c, path)), t) ->
        let path' = sbst map path in
        let map' = List.filter_out (fst |- Path.eq (Type.LId c)) map in
        Local(Type_ext (Ext_rebind (c, path')), tr.term map' t)
    | Module decls ->
        decls
        |> trans_decls_as_term (tr.term map)
        |> _Module
    | _ -> tr.desc_rec map desc
  in
  tr.desc <- tr_desc;
  tr.term

type env =
  {venv : (id * id) list;           (* value environment *)
   tenv : (tconstr * tconstr) list; (* type environment *)
   cenv : (path * path) list}       (* constructor environment *)

let subst' {venv; tenv; cenv} t =
  Dbg.printf "venv: %a@." Print.(list (id * id)) venv;
  Dbg.printf "tenv: %a@." Print.(list (tconstr * tconstr)) tenv;
  Dbg.printf "cenv: %a@." Print.(list (path * path)) cenv;
  Dbg.printf "t: %a@." Print.term t;
  t
  |> subst_var_map_without_typ @@ Fmap.(list (snd _LId)) venv
  |@> Dbg.printf "t1: %a@." Print.term
  |> subst_tconstr_label_map tenv
  |@> Dbg.printf "t2: %a@." Print.term
  |> subst_tconstr_label_by_name venv (* TODO: too ad-hoc *)
  |@> Dbg.printf "t3: %a@." Print.term
  |> subst_ext_path_map cenv
  |@> Dbg.printf "t': %a@.@." Print.term
let subst'_typ env ty = trans_typ_as_term (subst' env) ty

(* All variables must be unique *)
let extract_path path =
  let name = Path.to_string path in
  let attr = (if Path.is_primitive path then [Id.Primitive] else []) @ (if Path.is_external path then [Id.External] else []) in
  Type.LId (Id.make name () ~attr)

let add_prefix m env decl =
  let prefix = Id.name m ^ "." in
  let add x = Id.add_name_before prefix x in
  let adds xs =
    let xs' = Fmap.(list (fst add)) xs in
    xs', List.map2 (fun (x,_) (x',_) -> x, x') xs xs'
  in
  let sbst env = trans_decl_as_term (subst' env) in
  match decl with
  | Decl_let defs ->
      let defs,map = adds defs in
      let env = {env with venv = map @ env.venv} in
      let defs' = Fmap.(list (pair (Id.map_typ (subst'_typ env)) (subst' env))) defs in
      env, Decl_let defs'
  | Decl_type decls ->
      let decls,map = adds decls in
      let env = {env with tenv = map @ env.tenv} in
      env, sbst env (Decl_type decls)
  | Type_ext (Ext_type (path,(params,row))) ->
      let ext_row_path =
        if C.is_exn path then (* WORKAROUND: for the consistency with tr.term *)
          extract_path row.ext_row_path
        else
          extract_path @@ Path.cons m row.ext_row_path
      in
      let env = {env with cenv = (row.ext_row_path,ext_row_path)::env.cenv} in
      env, sbst env (Type_ext (Ext_type (path,(params,row))))
  | Type_ext (Ext_rebind (c, path)) ->
      let path = extract_path path in
      let c' = add c in
      {env with cenv = (LId c, LId c')::env.cenv},
      sbst env (Type_ext (Ext_rebind (c', path)))
  | Include _ -> [%unsupported]
  | Decl_multi _ -> [%unsupported]

let extract_term, extract_typ, extract_var =
  let tr = Tr2.make () in
  (* TODO: Are tr_id_aux & tr_lid OK? *)
  let tr_id_aux lid ty =
    let x =
      match lid with
      | LId x -> Id.set_typ x ty
      | LDot _ ->
          let name = Lid.to_string lid in
          let attr = if Id.is_external (Lid.head lid) then [Id.External] else [] in
          Id.make name ~attr ty
      | LApp _ -> unsupported "%s" __FUNCTION__
    in
    LId x
  in
  let add_prefix_exn (prefix,penv,_) c =
    match c, prefix, Id.List.assoc_opt (Path.head c) penv with
    | _, _, Some (Some prefix') ->
        Type.LDot(prefix', Path.name c)
    | LId _, Some p, _ -> Type.LDot(p, Path.name c)
    | _ -> c
  in
  tr.lid <- (fun env lid ->
    Lid.typ lid
    |> tr.typ env
    |> tr_id_aux lid);
  tr.term <- (fun (prefix,penv,menv as env) t ->
    match t.desc with
    | Var lid -> (* This case is needed for recovering the types of external functions *)
        let ty = tr.typ env t.typ in
        Term.var_lid (tr_id_aux lid ty)
    | Local(Decl_let[m, {desc=Module decls}], t2) ->
        let id = Id.set_typ m () in
        let _,decls' =
          let prefix' =
            match prefix with
            | None -> Type.LId id
            | Some lid -> LDot(lid, Id.name m)
          in
          decls
          |> trans_decls_as_term (tr.term (Some prefix',penv,menv))
          |> List.fold_left_map (add_prefix m) {venv=[];tenv=[];cenv=[]}
        in
        let menv = (m,(decls'))::menv in
        let penv = (id,prefix)::penv in
        let t2' = tr.term (prefix,penv,menv) t2 in
        let decl = Decl_let [m, Term.dummy (Id.typ m)] in (* This is used only for making venv in add_prefix *)
        Term.locals (decl::decls') t2'
    | Local(Decl_let[m, ({desc=Var _} as t1)], t2) when is_mod_var m ->
        let t2' = subst ~b_ty:true m t1 t2 in
        tr.term env t2'
    | Local(Decl_let[m, t1], t2) when is_module t1 -> (* for first-class modules *)
        let decls,_t1' = decomp_locals t1 in
        assert (is_rand_unit _t1');
        let t_decls = Term.(locals decls unit) in (* to preserve side-effects *)
        let t1 = Term.rand ~expand:true t1.typ in
        tr.term env [%term ignore `t_decls; let m = `t1 in `t2]
    | Local(Decl_let defs, _) when List.exists (snd |- is_module) defs -> [%unsupported]
    | Local(Type_ext Ext_type(p, ([], ({ext_row_path = LId c} as row))), t1) when C.is_exn p ->
        let ext_row_path = Path.append_opt prefix (LId c) |> extract_path in
        let env = prefix, (c,prefix)::penv, menv in
        let t1' = tr.term env t1 in
        let desc = Local(Type_ext (Ext_type(p, ([], {row with ext_row_path}))), t1') in
        make desc (tr.typ env t.typ)
    | Local(Type_ext Ext_type(p, (_, {ext_row_path = LId c})), _) when C.is_exn p ->
        let penv' = (c,prefix)::penv in
        tr.term_rec (prefix,penv',menv) t
    | Local(Type_ext Ext_rebind(c, _), _) ->
        let penv' = (c,prefix)::penv in
        tr.term_rec (prefix,penv',menv) t
    | Constr(b, c, ts) ->
        let c =
          c
          |& (t.typ = Ty.exn) &> add_prefix_exn env
          |> extract_path
        in
        let desc = Constr(b, c, List.map (tr.term env) ts) in
        let typ = tr.typ env t.typ in
        make desc typ
    | _ -> tr.term_rec env t |> set_afv_shallowly);
  tr.decl <- (fun env decl ->
    match decl with
    | Decl_type decls ->
        let decls' = List.filter_out (snd |- snd |- is_mod_typ) decls in
        if decls' = [] then
          Decl_multi []
        else
          tr.decl_rec env (Decl_type decls')(* ???
    | Type_ext(Ext_rebind(s, path)) ->
        let s' =
          match prefix with
          | None -> s
          | Some p -> Id.add_name_before Path.(to_string p) s
        in
        Type_ext(Ext_rebind(s', extract_path path))
    | Type_ext(Ext_type(path, (params, row))) ->
        let ext_row_path =
          match prefix with
          | None -> row.ext_row_path
          | Some p -> Path.append p row.ext_row_path
        in
        let row' = {row with ext_row_path} in
        tr.decl_rec env @@ Type_ext(Ext_type(path, (params, row')))*)
    | _ -> tr.decl_rec env decl);
  tr.pat <- (fun env p ->
    let p' = tr.pat_rec env p in
    let desc =
      match p'.pat_desc with
      | PConstr(b, c, ps) ->
          let c =
            c
            |& (p.pat_typ = Ty.exn) &> add_prefix_exn env
            |> extract_path
          in
          PConstr(b, c, ps)
      | _ -> p'.pat_desc
    in
    make_pattern desc p'.pat_typ);
  tr.typ <- (fun env ty ->
    match ty with
    | TConstr(path, tys) -> Parser_wrapper.assoc_prim_typ (extract_path path) (List.map (tr.typ env) tys)
    | TModSig _
    | TModLid _ -> Ty.unit
    | _ -> tr.typ_rec env ty);
  let init_env = (None,[],[]) in
  tr.term init_env,
  tr.typ init_env,
  tr.var init_env

let remove_signature_declaration =
  let tr = Tr.make () in
  let tr_desc desc =
    match desc with
    | Local(Decl_type decl, t) ->
        let decl' = List.filter_out (snd |- snd |- is_module_or_functor_typ) decl in
        let t' = tr.term t in
        if decl' = [] then
          tr.desc t'.desc
        else
          Local(Decl_type decl', t')
    | _ -> tr.desc_rec desc
  in
  tr.desc <- tr_desc;
  tr.term

let remove_module_dummy =
  let tr = Tr.make () in
  tr.decl <- (fun decl ->
    match decl with
    | Decl_let [_, {desc = Const (Dummy ty)}] when is_mod_typ ty -> Decl_multi []
    | _ -> tr.decl_rec decl);
  tr.term


let rec decls_of_module_var env m ty =
  let sgn =
    try
      Tenv.sig_of_mod_typ ~env ty
    with e ->
      Format.eprintf "e: %s@." (Printexc.to_string e);
      Format.eprintf "m: %a@." Lid.print m;
      Format.eprintf "ty: %a@." Print.typ ty;
      Format.eprintf "env: %a@." Print.(list (tconstr * typ)) env;
      [%invalid_arg]
  in
  let types =
    let make (s,(params,_)) =
      let c = Type.LDot(path_of_lid m, string_of_constr s) in
      let ty = Parser_wrapper.assoc_prim_typ c params in
      s, (params, ty)
    in
    sgn.sig_types
    |> List.flatten_map (List.map make)
    |> List.map (_Decl_type -| List.singleton)
  in
  let append_m x = Lid.append m @@ Lid._LId x in
  let values =
    sgn.sig_values
    |> List.map (fun x -> x, Term.var_lid ~typ:(Id.typ x) @@ append_m x)
    |> List.map (fun (x,t) -> x, if is_mod_var x then make_extracted_module_of_var env (append_m x) t else t)
    |> List.map (fun def -> Decl_let [def])
  in
  let exts = List.map (_Type_ext -| _Ext_type) sgn.sig_ext in
  types @ exts @ values

and make_extracted_module_of_var env m t =
  make_module ~typ:t.typ (decls_of_module_var env m t.typ)

let extract_module_var : (unit Id.t * typ) list -> term -> term =
  let tr = Tr2.make () in
  tr.desc <- (fun env desc ->
    match desc with
    | Local(Decl_let[m, ({desc=Var m'} as t1)], t2) when is_mod_var m ->
        let t1' = make_extracted_module_of_var env m' t1 in
        let t2' = tr.term env t2 in
        Local(Decl_let[m, t1'], t2')
    | Module decls ->
        decls
        |> trans_decls_as_term (tr.term env)
        |> _Module
    | _ -> tr.desc_rec env desc);
  tr.term <- set_afv_shallowly --| tr.term_rec;
  tr.term


(** Alpha-renaming of local modules *)
let alpha_rename_local : term -> term =
  let tr = Tr2.make () in
  tr.desc <- (fun bv desc ->
    match desc with
    | Local(Decl_let defs, t) ->
        let map =
          defs
          |> List.filter_map (fun (x,_) ->
                 if is_mod_var x && List.mem ~eq:(Eq.on Id.name) x !bv then
                   Some (x, gen_fresh_name_var_int !bv x)
                 else
                   None)
        in
        let path_map =
          let aux = Id.set_typ -$- () in
          List.map (Pair.map aux (Type._LId -| aux)) map
        in
        let sbst = subst_var_map map -| Trans.map_typ (subst_path_head_map path_map) in
        bv := List.rev_map_append fst defs @@ List.rev_map_append snd map !bv;
        let t = tr.term bv @@ sbst t in
        let defs = Fmap.(list (Id.List.subst map * (sbst -| tr.term bv))) defs in
        Local(Decl_let defs, t)
    | _ -> tr.desc_rec bv desc);
  fun t -> tr.term (ref (col_modules t)) t

let extract_path_ext_rebind =
  let tr = Tr.make() in
  tr.decl <- (fun decl ->
    match decl with
    | Type_ext(Ext_rebind(c,path)) -> Type_ext(Ext_rebind(c, extract_path path))
    | _ -> tr.decl_rec decl);
  tr.term

(* ASSUME: the module names are distinct from each other *)
let extract (problem:Problem.t) =
  let kind : Problem.kind =
    match problem.kind with
    | Safety -> Safety
    | Ref_type_check targets -> Ref_type_check Fmap.(list (fst extract_var) targets)
  in
  let pr s t = Dbg.printf "##[Module] %s:@.  @[%a@.@." s Print.term t in
  let term =
    problem.term
    |@> pr "INPUT"
    |> alpha_rename_local
    |@> pr "alpha_rename_local"
    |> extract_module_var problem.ext_mod_typ
    |@> pr "extract_module_var"
    |> extract_term
    |@> pr "extract_term"
    |> remove_signature_declaration
    |@> pr "remove_signature_declaration"
    |> remove_module_dummy
    |> extract_path_ext_rebind
    |> Trans.elim_unused_let ~leave_last:true
    |@!!Dbg.check&> Check.only_LId
  in
  let attr = List.remove_all problem.attr Module in
  let ext_typ =
    problem.ext_typ
    |> Fmap.(list (extract_path * snd extract_typ))
    |> List.filter_out (snd |- snd |- is_mod_typ)
  in
  let ext_exc = Fmap.(list (extract_path * list extract_typ)) problem.ext_exc in
  if !!Dbg.check then begin
    let normalize = List.map (fst |- Path.to_string) |- List.sort compare in
    let used_exn1 = col_exn_constr problem.term |> normalize in
    let used_exn2 = col_exn_constr term         |> normalize in
    Dbg.printf "used_exn1: %a@." Print.(list string) used_exn1;
    Dbg.printf "used_exn2: %a@." Print.(list string) used_exn2;
    assert (used_exn1 = used_exn2);
    end;
  let ext_mod_typ = [] in
  {problem with term; kind; attr; ext_typ; ext_exc; ext_mod_typ}

(** N.B.: Type definition can be shadowed by [include], e.g.,
```
struct X =
  type t = int
end
struct Y =
  include X
  type 'a t = string
end
```
 *)
let removed_hidden_types decls : Syntax.declaration list =
  List.L.fold_right decls
    ~init:([],[])
    ~f:(fun decl (acc,tconstrs) ->
      let decl',tconstrs' =
        match decl with
        | Decl_type decls ->
            let decls' = List.filter_out (fst |- Id.List.mem -$- tconstrs) decls in
            Decl_type decls',
            List.rev_map_append fst decls tconstrs
        | _ -> decl, tconstrs
      in
      decl'::acc, tconstrs')
  |> fst

let extract_include_term : (tconstr * typ) list -> term -> term =
  let tr = Tr2.make() in
  tr.desc <- (fun env desc ->
      match desc with
      | Module decls ->
          let decls' =
            decls
            |> trans_decls_as_term (tr.term env)
            |> removed_hidden_types
          in
          Module decls'
      | Local(Include t1, t2) ->
          let decls =
            match tr.desc env t1.desc with
            | Var m -> decls_of_module_var env m t1.typ
            | Module decls -> decls
            | _ -> assert false
          in
          let t2' = tr.term env t2 in
          (Term.locals decls t2').desc
      | _ -> tr.desc_rec env desc);
  tr.term <- set_afv_shallowly --| tr.term_rec;
  tr.term

let extract_include (problem : Problem.t) =
  let term = extract_include_term problem.ext_mod_typ problem.term in
  {problem with term}
