open Util
open Syntax
open Term_util
open Type

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let make_map_constr m decls =
  constrs_in_declaration decls
  |> List.map (Pair.add_right @@ Id.add_module_prefix_string ~m)

let make_map_field m decls =
  fields_in_declaration decls
  |> List.map (Pair.add_right @@ Id.add_module_prefix_string ~m)

let make_map_tdata m decls =
  decls
  |> List.map (fun (s,_) -> s, Id.add_module_prefix_string ~m s)
  |> List.map (Pair.map_snd (fun s -> TData s))

let make_map_var m map_tdata xs =
  let aux x =
    x
    |> Id.add_module_prefix ~m
    |> Id.map_typ @@ subst_tdata_map_typ map_tdata
  in
  List.map (Pair.add_right aux) xs

let filter_map_tdata sgn = List.filter_out (fst |- List.mem_assoc -$- types_in_signature sgn)
let filter_map_constr sgn = List.filter_out (fst |- List.mem -$- constrs_in_signature sgn)
let filter_map_field sgn = List.filter_out (fst |- List.mem -$- fields_in_signature sgn)
let filter_map_var sgn = List.filter_out (fst |- Id.mem -$- values_in_signature sgn)

type map =
  {map_constr : (string * string) list;
   map_field : (string * string) list;
   map_tdata : (string * typ) list;
   map_var : (id * id) list}

let init_map map_exn_constr = {map_constr=map_exn_constr; map_field=[]; map_tdata=[]; map_var=[]}

let rename_let m defs {map_constr; map_field; map_tdata; map_var} =
  let sgn = {sig_values=List.map fst defs; sig_types=[]} in
  let map_constr = filter_map_constr sgn map_constr in
  let map_field = filter_map_field sgn map_field in
  let map_tdata = filter_map_tdata sgn map_tdata in
  let map_var = make_map_var m map_tdata (List.map fst defs) @ filter_map_var sgn map_var in
  let sbst (x,t) =
    List.assoc x map_var,
    t
    |> subst_constr_map map_constr
    |> subst_field_map map_field
    |> subst_tdata_map map_tdata
    |> subst_var_map_without_typ map_var
  in
  List.map sbst defs,
  {map_constr; map_field; map_tdata; map_var}

let rename_type m decls {map_constr; map_field; map_tdata; map_var} =
  let sgn = {sig_values=[]; sig_types=decls} in
  let map_constr = make_map_constr m decls @ filter_map_constr sgn map_constr in
  let map_field = make_map_field m decls @ filter_map_field sgn map_field in
  let map_tdata = make_map_tdata m decls @ filter_map_constr sgn map_tdata in
  let map_var = filter_map_var sgn map_var in
  let sbst (s,ty) =
    let ty' =
      let add_prefix (s,x) = Id.add_module_prefix_string ~m s, x in
      match ty with
      | TVariant(false, labels) -> TVariant(false, List.map add_prefix labels)
      | TRecord fields -> TRecord (List.map add_prefix fields)
      | _ -> ty
    in
    decomp_tdata @@ List.assoc s map_tdata,
    ty'
    |> subst_tdata_map_typ map_tdata
  (* TODO: for variables in predicates
                      |> subst_var_typ_map map_var
   *)
  in
  List.map sbst decls,
  {map_constr; map_field; map_tdata; map_var}

let add_module_prefix ~m decl =
  match decl with
  | Decl_let defs -> Decl_let (List.map (Pair.map_fst (Id.add_module_prefix ~m)) defs)
  | Decl_type decls -> Decl_type (List.map (Pair.map_fst (Id.add_module_prefix_string ~m)) decls)
  | Open _ -> assert false

let rec decomp_module menv t =
  match t.desc with
  | Var m -> decomp_module menv (Id.assoc m menv)
  | Module decls -> decls
  | _ ->
      Format.printf "%a@." Print.term t;
      assert false

let remove_functor =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(Decl_let [_,t1], t2) when is_functor t1 ->
        tr.tr_desc t2.desc
    | Module decls ->
        let is_functor' decl =
          match decl with
          | Decl_let [_,t] -> is_functor t
          | _ -> false
        in
        Module (List.filter_out is_functor' decls)
    | _ -> tr.tr_desc_rec desc
  in
  let tr_typ ty =
    match ty with
    | TModule sgn ->
        let sig_values =
          let is_functor' x =
            let xs,ty' = decomp_tfun (Id.typ x) in
            xs <> [] && (match ty' with TModule _ -> true | _ -> false)
          in
          List.filter_out is_functor' sgn.sig_values
        in
        TModule {sgn with sig_values}
    | _ -> tr.tr_typ_rec ty
  in
  tr.tr_desc <- tr_desc;
  tr.tr_typ <- tr_typ;
  tr.tr_term

let rec add_to_env m t (menv,fenv) =
  if is_module t then
    match decomp_module menv t with
    | decls ->
        let aux (map,(menv,fenv),acc_rev) decl =
          match decl with
          | Decl_let defs ->
              let defs,map = rename_let m defs map in
              let env =
                match defs with
                | [m,t] when is_module t || is_functor t -> add_to_env m t (menv,fenv)
                | _ -> menv, fenv
              in
              map, env, Decl_let defs::acc_rev
          | Decl_type decls ->
              let decls,map = rename_type m decls map in
              map, (menv, fenv), Decl_type decls::acc_rev
          | Open _ -> assert false
        in
        let _,(menv,fenv),decls_rev = List.fold_left aux (init_map [],(menv,fenv),[]) decls in
        let t' = {t with desc = Module (List.rev decls_rev)} in
        (m,t')::menv, fenv
    | exception Not_found -> menv, fenv
  else if is_functor t then
    let ms,t' = decomp_funs t in
    let decls = decomp_module menv t' in
    menv, (m,(ms,decls))::fenv
  else
    assert false

let inline_functor =
  let tr = make_trans2 () in
  let tr_term env t =
    match t.desc with
    | Local(Decl_let [m, ({desc=App({desc=Var f}, ts)} as t1)], t2) when is_module t1 && Id.mem_assoc f (snd env) ->
        let ts' = List.map (tr.tr2_term env) ts in
        let t1 =
          let ms,decls = Id.assoc f (snd env) in
          let ms' = List.map2 (fun m t -> Id.set_typ m t.typ) ms ts' in (* just for type-check? *)
          let decls_arg = List.map2 (fun x t -> Decl_let [x,t]) ms' ts' in
          Term.module_ (decls_arg @ decls)
        in
        let m' = Id.set_typ m t1.typ in
        let t2' = tr.tr2_term env t2 in
        Term.let_ [m', t1] t2'
    | Local(Decl_let [_, ({desc=App({desc=Var _}, ts)} as t1)], t2) when is_module t1 ->
        if List.exists (not -| has_no_effect) ts then unsupported "Module.inline_functor";
        tr.tr2_term env t2
    | Local(Decl_let [m,t1], t2) when is_module t1 || is_functor t1 ->
        let t1' = tr.tr2_term env t1 in
        let env = add_to_env m t1' env in
        let t2' = tr.tr2_term env t2 in
        Term.let_ [m,t1'] t2'
    | Module decls -> Term.module_ (trans_decls_by_term (tr.tr2_term env) decls)
    | _ -> tr.tr2_term_rec env t
  in
  tr.tr2_term <- tr_term;
  tr.tr2_term ([],[])
  |- remove_functor

let get_exn_constrs t =
  match find_exn_typ t with
  | None -> []
  | Some ty -> constrs_in_declaration ["exn",ty]

let remove_open =
  let tr = make_trans2 () in
  let tr_desc exn_constrs desc =
    match tr.tr2_desc_rec exn_constrs desc with
    | Local(Open m, t) ->
        let sgn = decomp_tmodule @@ Id.typ m in
        let map_constr = make_map_constr m sgn.sig_types in
        let map_field = make_map_field m sgn.sig_types in
        let map_tdata = make_map_tdata m sgn.sig_types in
        let map_var = make_map_var m map_tdata sgn.sig_values in
        t
        |> subst_constr_map map_constr
        |> subst_field_map map_field
        |> subst_tdata_map map_tdata
        |> subst_var_map map_var
        |> Syntax.desc
    | Module decls ->
        let decls' =
          let aux decl acc =
            match decl with
            | Open m ->
                let sgn = decomp_tmodule @@ Id.typ m in
                let map_constr =
                  let map_exn_constr =
                    let exn_constrs_in_m = List.filter (Id.is_in_module_string ~m) exn_constrs in
                    let exn_constrs_in_m' = List.map (Id.remove_module_prefix_string ~m) exn_constrs_in_m in
                    List.combine exn_constrs_in_m' exn_constrs_in_m
                  in
                  make_map_constr m sgn.sig_types @ map_exn_constr
                in
                let map_field = make_map_field m sgn.sig_types in
                let map_tdata = make_map_tdata m sgn.sig_types in
                let map_var = make_map_var m map_tdata sgn.sig_values in
                acc
                |> subst_constr_map_decls map_constr
                |> subst_field_map_decls map_field
                |> subst_tdata_map_decls map_tdata
                |> subst_var_map_decls map_var
            | _ -> decl::acc
          in
          List.fold_right aux decls []
        in
        Module decls'
    | desc -> desc
  in
  tr.tr2_desc <- tr_desc;
  fun t ->
    let exn_constrs = get_exn_constrs t in
    tr.tr2_term exn_constrs t

(* TODO: complete other labels *)
let complete_prefix =
  let tr = make_trans () in
  let prefix_of_tdata s =
    let prefix,_ = String.rsplit ~by:"." s in
    prefix ^ "."
  in
  let replace_prefix ~prefix s =
    s
    |> Id.decomp_prefixes_string
    |> snd
    |> (^) prefix
  in
  let complete_record l ty =
    try
      let prefix = prefix_of_tdata @@ decomp_tdata ty in
      replace_prefix ~prefix l
    with Not_found -> l
  in
  let complete_constr c ty =
    match elim_tattr ty with
    | TData s ->
        begin
          try
            let prefix,_ = String.rsplit ~by:"." s in
            replace_prefix ~prefix:(prefix^".") c
          with Not_found -> c
        end
    | TVariant(_,labels) ->
        let check (s,_) =
          try
            let s1,s2 = String.rsplit s ~by:c in
            (s1 = "" || String.ends_with s1 ".") && s2 = ""
          with Not_found -> false
        in
        let c',_ = List.find check labels in
        c'
    | _ -> assert false
  in
  let tr_term t =
    let t' = tr.tr_term_rec t in
    let desc =
      match t'.desc with
      | Constr(c,ts) ->
          let c' = complete_constr c t.typ in
          Constr(c', ts)
      | Field(t1,l) ->
          let l' = complete_record l t1.typ in
          Field(t1, l')
      | Record fields ->
          begin
            try
              let prefix = prefix_of_tdata @@ decomp_tdata t'.typ in
              Record (List.map (Pair.map_fst (replace_prefix ~prefix)) fields)
            with Not_found -> t'.desc
          end
      | _ -> t'.desc
    in
    {t' with desc}
  in
  let tr_pat p =
    let p' = tr.tr_pat_rec p in
    match p'.pat_desc with
    | PConstr(c,ps) ->
        let c' = complete_constr c p'.pat_typ in
        let pat_desc = PConstr(c',ps) in
        {p with pat_desc}
    | _ -> p'
  in
  tr.tr_term <- tr_term;
  tr.tr_pat <- tr_pat;
  tr.tr_typ <- Fun.id;
  tr.tr_term

let rename =
  let tr = make_trans2 () in
  let rn (m1,m2) s =
    if String.starts_with s (Id.name m1) then
      Id.rename_module_string ~m_after:m2 s
    else
      s
  in
  let tr_var (m1,m2) x =
    if Id.(m1 = x) then
      m2
    else if Id.is_in_module ~m:m1 x then
      Id.rename_module ~m_after:m2 x
    else
      x
  in
  let tr_typ mm ty =
    match ty with
    | TData s -> TData (rn mm s)
    | TRecord fields ->
        let fields' = List.map (Pair.map_fst (rn mm)) fields in
        TRecord fields'
    | TVariant(b, labels) ->
        let labels' = List.map (Pair.map_fst (rn mm)) labels in
        TVariant(b, labels')
    | _ -> tr.tr2_typ_rec mm ty
  in
  let tr_desc (x,y) desc =
    match desc with
    | Local(Decl_let bindings, _) when List.exists (fst |- Id.eq x) bindings -> desc
    | _ -> tr.tr2_desc_rec (x,y) desc
  in
  tr.tr2_var <- tr_var;
  tr.tr2_typ <- tr_typ;
  tr.tr2_desc <- tr_desc;
  Fun.curry tr.tr2_term

let inline_var =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(Decl_let [x, ({desc=Var y} as t1)], t) when is_module t1 ->
        (rename x y @@ tr.tr_term t).desc
    | Module decls ->
        let decls' = trans_decls_by_term tr.tr_term decls in
        Module decls'
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let extract =
  let tr = make_trans2 () in
  let tr_desc exn_constrs desc =
    match desc with
    | Local(Open _, _) -> assert false
    | Local(Decl_let[m,{desc=Module decls}], t) ->
        let map_exn_constr =
          exn_constrs
          |> List.filter (Id.is_in_module_string ~m)
          |> List.map (Pair.add_left (Id.remove_module_prefix_string ~m))
        in
        let decls' =
          let aux (map,decls_rev) decl =
            match decl with
            | Decl_let defs ->
                let defs,map = rename_let m defs map in
                map, Decl_let defs::decls_rev
            | Decl_type decls ->
                let decls,map = rename_type m decls map in
                map, Decl_type decls::decls_rev
            | Open _ -> assert false
          in
          decls
          |> trans_decls_by_term (tr.tr2_term exn_constrs)
          |> List.fold_left aux (init_map map_exn_constr,[])
          |> snd
          |> List.rev
        in
        let t' = tr.tr2_term exn_constrs t in
        (List.fold_right Term.local decls' t').desc
    | Local(Decl_let[_,t], _) when is_module t -> assert false
    | _ -> tr.tr2_desc_rec exn_constrs desc
  in
  tr.tr2_desc <- tr_desc;
  fun t ->
    let exn_constrs = get_exn_constrs t in
    t
    |> inline_var
    |@> Debug.printf "INLINE_VAR: %a@." Print.term
    |> tr.tr2_term exn_constrs
