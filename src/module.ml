open Util
open Type
open Type_util
open Syntax
open Term_util

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

let abst_first_class_module_term, abst_first_class_module_typ =
  let tr = Tr2.make () in
  let make_bind used t1 =
    Flag.Abstract.over "First class module";
    let name = "FirstClassModule" in
    let t1' = tr.term used t1 in
    let f = gen_fresh_name_var_int !used @@ Id.new_var ~name t1'.typ in
    used := f :: !used;
    (f, Term.let_ [ (f, t1') ])
  in
  tr.term <-
    (fun used t ->
      match t.desc with
      | Pack t1 ->
          let _, def = make_bind used t1 in
          let t = if has_fail t1 then Term.fail else Term.unit in
          let u = Id.new_var Ty.unit in
          def Term.(fun_ u t)
      | Unpack t1 ->
          let f, def = make_bind used t1 in
          let ty = tr.typ used t.typ in
          let t = Term.(var f @ [ unit ]) in
          def Term.(seq t (rand ~expand:false ty))
      | _ -> set_afv_shallowly @@ tr.term_rec used t);
  tr.typ <-
    (fun used ty -> match ty with TPackage _ -> Ty.(fun_ unit unit) | _ -> tr.typ_rec used ty);
  ((fun t -> tr.term (ref (col_modules t)) t), tr.typ (ref []))

let abst_first_class_module (problem : Problem.t) =
  let term = abst_first_class_module_term problem.term in
  let ext_mod_typ = Fmap.(list (snd abst_first_class_module_typ)) problem.ext_mod_typ in
  { problem with term; ext_mod_typ }

(* TODO: ad-hoc *)
let subst_tconstr_label_by_name venv =
  if venv = [] then Fun.id
  else
    let replace str (by, sub) =
      try match String.split str ~by with "", s when s.[0] = '.' -> sub ^ s | _ -> str
      with _ -> str
    in
    let map = List.map (Pair.map_same Id.name) venv in
    Trans.map_typ @@ map_path (Path.map ~f:(Id.map_name (List.fold_left replace -$- map)))

(* substitute ext_row_path in Type_ext *)
let subst_ext_path_map =
  let tr = Tr2.make () in
  let sbst = List.subst ~eq:Path.eq in
  let tr_desc map desc =
    match desc with
    | Local (Type_ext (Ext_type (path, (params, row))), t)
      when not (Path.eq path row.ext_row_path) (* ??? *) ->
        let row' = { row with ext_row_path = sbst map row.ext_row_path } in
        Local (Type_ext (Ext_type (path, (params, row'))), tr.term map t)
    | Local (Type_ext (Ext_rebind (c, path)), t) ->
        let path' = sbst map path in
        let map' = List.filter_out (fst |- Path.eq (Type.LId c)) map in
        Local (Type_ext (Ext_rebind (c, path')), tr.term map' t)
    | Module decls -> decls |> trans_decls_as_term (tr.term map) |> _Module
    | _ -> tr.desc_rec map desc
  in
  tr.desc <- tr_desc;
  fun map t -> if map = [] then t else tr.term map t

let dbg = true

type env = {
  prefix : string;  (** prefix of the current module *)
  penv : (unit Id.t * string) list;  (** path/prefix environment *)
  cenv : (unit Id.t * string) list;  (** type-constructor/prefix environment *)
  tenv : term Tenv.t;  (** type environment *)
}

let extract_path (path : path) : path =
  let x =
    match path with
    | LId c -> c
    | LDot _ ->
        let name = Path.to_string path in
        let attr =
          (if Path.is_primitive path then [ Id.Primitive ] else [])
          @ if Path.is_external path then [ Id.External ] else []
        in
        Id.make name () ~attr
    | LApp _ -> assert false
  in
  LId x

let extract_and_complete_path env (path : path) : path =
  let prefix =
    match path with
    | LId c -> Id.List.assoc_default "" c env.cenv
    | LDot _ -> Id.List.assoc_default "" (Path.head path) env.penv
    | LApp _ -> assert false
  in
  match extract_path path with LId c -> LId (Id.add_name_prefix prefix c) | _ -> assert false

let prefix_of_string s = String.rsplit ~by:"." s |> fst

let prefix_of_path (p : Path.t) =
  match p with LId _ -> "" | LDot (p, _) -> Path.to_string p ^ "." | _ -> [%invalid_arg]

let rec find_constr_prefix env path =
  match Tenv.assoc_type_opt path env with
  | Some ({ prefix }, (_, (TVariant _ | TRecord _))) ->
      Path.string_of_option prefix ^ prefix_of_path path
  | Some ({ env }, (_, TConstr (path', _))) -> find_constr_prefix env path'
  | Some _ -> assert false
  | None -> assert false

let extract_and_complete_constr_path typ env (path : path) : path =
  let prefix =
    match (path, typ) with
    | LId _, TConstr (path, _) -> find_constr_prefix env.tenv path
    | LId _, TVariant _ -> ""
    | LId _, TRecord _ -> ""
    | LDot _, _ -> Id.List.assoc_default "" (Path.head path) env.penv
    | _ -> assert false
  in
  match extract_path path with LId c -> LId (Id.add_name_prefix prefix c) | _ -> assert false

let extract_lid (tr : env Tr2.t) env (lid : lid) ty : lid =
  let x =
    match lid with
    | LId c -> Id.map_typ (tr.typ env) c
    | LDot _ ->
        let prefix = Id.List.assoc_default "" (Id.set_typ (Lid.head lid) ()) env.penv in
        let name = prefix ^ Lid.to_string lid in
        let attr = if Id.is_external (Lid.head lid) then [ Id.External ] else [] in
        Id.make name ty ~attr
    | LApp _ -> assert false
  in
  LId x

let extract_decl (tr : env Tr2.t) env (decl : declaration) : env * declaration =
  let add x = Id.add_name_prefix env.prefix x in
  let add_typ typ =
    match typ with
    | TVariant (k, rows) ->
        let rows' = List.map (fun row -> { row with row_constr = add row.row_constr }) rows in
        TVariant (k, rows')
    | TRecord fields ->
        let fields' = List.map (Pair.map_fst add) fields in
        TRecord fields'
    | _ -> typ
  in
  match decl with
  | Decl_let defs -> (env, Decl_let (List.map (Pair.map (add -| tr.var env) (tr.term env)) defs))
  | Decl_type decls ->
      let env' =
        let cenv = List.fold_left (fun acc (c, _) -> (c, env.prefix) :: acc) env.cenv decls in
        let cenv =
          List.L.fold_left decls ~init:cenv ~f:(fun cenv (_, (_, ty)) ->
              match ty with
              | TVariant (_, rows) ->
                  List.rev_map_append (fun { row_constr } -> (row_constr, env.prefix)) rows cenv
              | _ -> cenv)
        in
        { env with cenv }
      in
      let decls' =
        List.map (fun (c, (params, ty)) -> (add c, (params, tr.typ env' @@ add_typ ty))) decls
      in
      (env', Decl_type decls')
  | Type_ext (Ext_type (path, (params, { ext_row_path; ext_row_args; ext_row_ret }))) ->
      let path' : path = extract_and_complete_path env path in
      let ext_row_path : path =
        match ext_row_path with LId c -> LId (add c) | _ -> [%unsupported]
      in
      let ext_row_args = List.map (tr.typ env) ext_row_args in
      let ext_row_ret = Option.map (tr.typ env) ext_row_ret in
      (env, Type_ext (Ext_type (path', (params, { ext_row_path; ext_row_args; ext_row_ret }))))
  | Type_ext (Ext_rebind (c, path)) ->
      (env, Type_ext (Ext_rebind (add c, extract_and_complete_path env path)))
  | Include _ -> assert false
  | Decl_multi _ -> assert false

let extract_term, extract_typ, extract_var =
  let tr = Tr2.make () in
  tr.term <-
    (fun ({ prefix; penv; tenv } as env) t ->
      match t.desc with
      | Var x ->
          let typ = tr.typ env t.typ in
          let x' = extract_lid tr env x typ in
          make_var_lid ~typ x'
      | Local ((Decl_let [ (m, { desc = Module decls }) ] as decl), t2) ->
          let m' = Id.set_typ m () in
          let decls' =
            let env = { env with prefix = prefix ^ Id.name m ^ "." } in
            trans_decls_as_term (tr.term env) decls
          in
          let t2' =
            let env = { env with penv = (m', prefix) :: penv; tenv = Tenv.add_decl decl tenv } in
            tr.term env t2
          in
          Term.locals decls' t2'
      | Local ((Decl_let [ (m, { desc = Var _ }) ] as decl), t2) when is_mod_var m ->
          let env' =
            { env with penv = (Id.set_typ m (), prefix) :: penv; tenv = Tenv.add_decl decl tenv }
          in
          tr.term env' t2
      | Local ((Decl_let [ (m, t1) ] as decl), t2) when is_module t1 (* for first-class modules *)
        ->
          let decls, _t1' = decomp_locals t1 in
          assert (is_rand_unit _t1');
          let t_decls = Term.(locals decls unit) in
          (* to preserve side-effects *)
          let t1 = Term.rand ~expand:true t1.typ in
          let env =
            { env with penv = (Id.set_typ m (), prefix) :: penv; tenv = Tenv.add_decl decl tenv }
          in
          tr.term env
            [%term
              ignore `t_decls;
              let m = `t1 in
              `t2]
      | Local (Decl_let defs, _) when List.exists (snd |- is_module) defs -> [%unsupported]
      | Local (decl, t1) ->
          let env, decl' = extract_decl tr env decl in
          let env = { env with tenv = Tenv.add_decl decl tenv } in
          let t1' = tr.term env t1 in
          make_local decl' t1'
      | Constr (b, c, ts) ->
          let typ = tr.typ env t.typ in
          let c' = extract_and_complete_constr_path t.typ env c in
          let ts' = List.map (tr.term env) ts in
          make_construct ~poly:b c' ts' typ
      | Record fields ->
          let ty = tr.typ env t.typ in
          let complete label =
            Type.ValE._LId @@ extract_and_complete_constr_path t.typ env (LId label)
          in
          let fields' = List.map (Pair.map complete (tr.term env)) fields in
          make_record fields' ty
      | Field (t1, f) ->
          let f' = Type.ValE._LId @@ extract_and_complete_constr_path t1.typ env (LId f) in
          let t1' = tr.term env t1 in
          let ty = tr.typ env t.typ in
          make_field ~ty t1' f'
      | _ -> tr.term_rec env t |> set_afv_shallowly);
  tr.typ <-
    (fun env ty ->
      match ty with
      | TModSig _ | TModLid _ -> Ty.unit
      | TConstr (c, tys) -> TConstr (extract_and_complete_path env c, List.map (tr.typ env) tys)
      | _ -> tr.typ_rec env ty);
  tr.lid <- (fun _ _ -> assert false);
  tr.path <- extract_and_complete_path;
  tr.pat <-
    (fun env p ->
      let p' = tr.pat_rec env p in
      match p'.pat_desc with
      | PConstr (b, c, ps) ->
          let c' = extract_and_complete_constr_path p.pat_typ env c in
          let pat_desc = PConstr (b, c', ps) in
          (set_pat_desc p' pat_desc [@alert "-unsafe"])
      | PRecord fields ->
          let complete label =
            Type.ValE._LId @@ extract_and_complete_constr_path p.pat_typ env (LId label)
          in
          let fields' = List.map (Pair.map_fst complete) fields in
          let pat_desc = PRecord fields' in
          (set_pat_desc p' pat_desc [@alert "-unsafe"])
      | _ -> p');

  let init_env = { prefix = ""; penv = []; cenv = []; tenv = !!Tenv.init } in
  (tr.term init_env, tr.typ init_env, tr.var init_env)

let remove_signature_declaration =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match tr.desc_rec desc with
      | Local (Decl_type decl, t) ->
          let decl' = List.filter_out (snd |- snd |- is_module_or_functor_typ) decl in
          if decl' = [] then t.desc else Local (Decl_type decl', t)
      | desc' -> desc');
  tr.typ <- Fun.id;
  tr.term

let remove_module_dummy =
  let tr = Tr.make () in
  tr.decl <-
    (fun decl ->
      match decl with
      | Decl_let [ (_, { desc = Const (Dummy ty) }) ] when is_mod_typ ty -> Decl_multi []
      | _ -> tr.decl_rec decl);
  tr.typ <- Fun.id;
  tr.term

let rec decls_of_module_var env m ty =
  let sgn =
    try Tenv.sig_of_mod_typ ~env ty
    with e ->
      Format.eprintf "e: %s@." (Printexc.to_string e);
      Format.eprintf "m: %a@." Lid.print m;
      Format.eprintf "ty: %a@." Print.typ ty;
      Format.eprintf "env: %a@." Print.(list (tconstr * typ)) env;
      [%invalid_arg]
  in
  sgn
  |> List.flatten_map (function
       | Sig_type decl ->
           decl
           |> List.map (fun (s, (params, _)) ->
                  let c = Type.LDot (path_of_lid m, string_of_constr s) in
                  let ty = TConstr (c, params) in
                  Decl_type [ (s, (params, ty)) ])
       | Sig_value x ->
           let append_m x = Lid.append m @@ Lid._LId x in
           let t = Term.var_lid ~typ:(Id.typ x) @@ append_m x in
           let t = if is_mod_var x then make_extracted_module_of_var env (append_m x) t else t in
           [ Decl_let [ (x, t) ] ]
       | Sig_ext ext -> [ Type_ext (Ext_type ext) ])

and make_extracted_module_of_var env m t = make_module ~typ:t.typ (decls_of_module_var env m t.typ)

let extract_module_var : (unit Id.t * typ) list -> term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun env desc ->
      match desc with
      | Local (Decl_let [ (m, ({ desc = Var m' } as t1)) ], t2) when is_mod_var m ->
          let t1' = make_extracted_module_of_var env m' t1 in
          let t2' = tr.term env t2 in
          Local (Decl_let [ (m, t1') ], t2')
      | Module decls -> decls |> trans_decls_as_term (tr.term env) |> _Module
      | _ -> tr.desc_rec env desc);
  tr.term <- set_afv_shallowly --| tr.term_rec;
  tr.term

(** Alpha-renaming of local modules *)
let alpha_rename_local : term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun bv desc ->
      match desc with
      | Local (Decl_let defs, t) ->
          let map =
            defs
            |> List.filter_map (fun (x, _) ->
                   if is_mod_var x && List.mem ~eq:(Eq.on Id.name) x !bv then
                     Some (x, gen_fresh_name_var_int !bv x)
                   else None)
          in
          let path_map =
            let aux = Id.set_typ -$- () in
            let map = List.map (Pair.map aux (Type._LId -| aux)) map in
            Id.List.assoc_opt -$- map
          in
          let sbst = subst_var_map map -| Trans.map_typ (subst_path_head_map path_map) in
          bv := List.rev_map_append fst defs @@ List.rev_map_append snd map !bv;
          let t = tr.term bv @@ sbst t in
          let defs = Fmap.(list (Id.List.subst map * (sbst -| tr.term bv))) defs in
          Local (Decl_let defs, t)
      | _ -> tr.desc_rec bv desc);
  fun t -> tr.term (ref []) t (* TODO: Should we collect the names of external modules? *)

let extract_path_typ =
  let tr = Tr.make () in
  tr.decl <-
    (fun decl ->
      match decl with
      | Type_ext (Ext_type (path, (params, row))) ->
          let ext_row_path = extract_path row.ext_row_path in
          let ext_row_args = List.map extract_typ row.ext_row_args in
          let ext_row_ret = Option.map extract_typ row.ext_row_ret in
          let row' = { ext_row_path; ext_row_args; ext_row_ret } in
          Type_ext (Ext_type (path, (params, row')))
      | Type_ext (Ext_rebind (c, path)) -> Type_ext (Ext_rebind (c, extract_path path))
      | _ -> tr.decl_rec decl);
  tr.typ <-
    (fun ty ->
      match ty with
      | TConstr (c, tys) ->
          let tys' = List.map tr.typ tys in
          let c' = extract_path c in
          TConstr (c', tys')
      | _ -> tr.typ_rec ty);
  tr.term

let rec mod_of_typ env ty =
  match ty with
  | TModSig sgn ->
      sgn
      |> List.filter_map (function
           | Sig_type decl -> Some (Decl_type decl)
           | Sig_value m when is_mod_var m -> Some (Decl_let [ (m, mod_of_typ env @@ Id.typ m) ])
           | Sig_value _ -> None
           | Sig_ext ext -> Some (Type_ext (Ext_type ext)))
      |> make_module
  | TModLid m -> mod_of_typ env @@ Tenv.assoc_value m ~env
  | _ -> [%invalid_arg]

let add_ext_mod ext_mod_typ t =
  let env =
    List.fold_left
      (fun env (x, ty) -> Tenv.add_module (Id.set_typ x ty) ty ~env)
      !!Tenv.init ext_mod_typ
  in
  let fv = get_fv_all t |> Id.List.unique in
  List.L.fold_right ext_mod_typ ~init:(fv, t) ~f:(fun (x, ty) (fv, t) ->
      if List.exists Id.(( = ) x) fv then
        let fv' = get_fv_typ' ty @@@ fv in
        let mt = mod_of_typ env ty in
        (fv', Term.let_ [ (Id.set_typ x ty, mt) ] t)
      else (fv, t))
  |> snd

let extract (problem : Problem.t) =
  let kind : Problem.kind =
    match problem.kind with
    | Safety -> Safety
    | Ref_type_check targets -> Ref_type_check Fmap.(list (fst extract_var) targets)
  in
  let pr s t = Dbg.printf "##[Module] %s:@.  @[%a@.@." s Print.term t in
  let term =
    problem.term
    |@> pr "INPUT"
    |> add_ext_mod problem.ext_mod_typ
    |@> pr "add_ext_mod"
    |> extract_term
    |@> pr "extract_term"
    |@> !!Dbg.check @> Check.only_LId
    |> Trans.elim_unused_let ~leave_last:true
    |> Trans.remove_unused_exception
    |> Trans.remove_unused_type_decl
    |@> pr "Trans.remove_unused_decls"
  in
  let attr = List.remove_all problem.attr Module in
  let ext_mod_typ = [] in
  { problem with term; kind; attr; ext_mod_typ }

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
  List.L.fold_right decls ~init:([], []) ~f:(fun decl (acc, tconstrs) ->
      let decl', tconstrs' =
        match decl with
        | Decl_type decls ->
            let decls' = List.filter_out (fst |- Id.List.mem -$- tconstrs) decls in
            (Decl_type decls', List.rev_map_append fst decls tconstrs)
        | _ -> (decl, tconstrs)
      in
      (decl' :: acc, tconstrs'))
  |> fst

let extract_include_term : (tconstr * typ) list -> term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun env desc ->
      match desc with
      | Module decls ->
          let decls' = decls |> trans_decls_as_term (tr.term env) |> removed_hidden_types in
          Module decls'
      | Local (Include t1, t2) ->
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
  Problem.map (extract_include_term problem.ext_mod_typ) problem
