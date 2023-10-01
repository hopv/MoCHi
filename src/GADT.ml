open Util
open Type
open Syntax
open Type_util
open Term_util

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let init_env = !!Tenv.empty

let rec is_gadt env ty =
  match ty with
  | TVariant(_, rows) -> List.exists (row_ret |- Option.is_some) rows
  | TConstr(c, _) ->
      begin match Tenv.assoc_type_opt c env with
      | Some (_, ty') when ty <> ty' (* ??? *) -> is_gadt env ty'
      | _ -> false
      end
  | _ -> false

let use_gadt env =
  Type.make_find (fun _ -> is_gadt env)
  |- Option.is_some

let set_abst_flag () = Flag.Abstract.use "GADT"

let abst_term,abst_typ =
  let tr = Tr2.make () in
  tr.term <- (fun (env,recs as arg) t ->
    match t.desc with
    | Fun _ when use_gadt env t.typ ->
        set_abst_flag ();
        let fv =
          get_fv t
          |> List.filter_out (Id.List.mem -$- recs)
          |> List.map (tr.var arg)
        in
        tr.typ arg t.typ
        |> Term.rand
        |> List.fold_right make_use_var fv
        |> set_afv_shallowly
    | Local(Decl_type decls, _) ->
        t
        |> tr.term_rec (Tenv.add_typ_decl decls env, recs)
        |> set_afv_shallowly
    | Match _ ->
        Trans.trans_match_with_recover_pat_bv ~tr_desc_rec:(tr.desc_rec arg) ~tr_typ:(tr.typ arg) t
    | Constr(false,c,ts) when is_gadt env t.typ ->
        let ts' = List.map (tr.term arg) ts in
        let typ' = tr.typ arg t.typ in
        make ~attr:t.attr (Constr(false,c,[])) typ'
        |> add_attrs pure_attr
        |> List.fold_right make_use ts'
        |> set_afv_shallowly
    | _ -> set_afv_shallowly @@ tr.term_rec arg t);

  tr.typ <- (fun (env,_ as arg) ty ->
    match ty with
    | TVariant(VNonPoly, rows) ->
        let rows =
          rows
          |> List.map (fun row -> {row with row_args = List.map (tr.typ arg) row.row_args})
          |> List.map (fun row ->
                 Option.iter (col_tvars |- List.iter (Ref.set -$- Some Ty.unit)) row.row_ret;
                 let row_args = if row.row_ret <> None then [] else row.row_args in
                 {row with row_args; row_ret = None})
        in
        TVariant(VNonPoly, rows)
    | TConstr(c, _) when is_gadt env ty -> TConstr(c, [])
    | _ -> tr.typ_rec arg ty);

  tr.decl <- (fun (env,recs as arg) decl ->
    match decl with
    | Decl_let defs ->
        let recs = List.rev_map fst defs @@@ recs in
        tr.decl_rec (env,recs) decl
    | Decl_type decls ->
        let decls =
          decls
          |> List.map (fun (c,(params,ty)) ->
                 let ty' = tr.typ arg ty in
                 let params' = if is_gadt env ty then [] else params in
                 c, (params', ty'))
        in
        Decl_type decls
    | _ -> tr.decl_rec arg decl);

  (fun ?(env=init_env) -> tr.term (env,[]) |- Trans.remove_tpoly),
  (fun ?(env=init_env) -> tr.typ (env,[]))

let abst_ext_typ env ext_typ =
  ext_typ
  |> List.map (fun (c,(params,ty)) ->
      let ty' = abst_typ ~env ty in
      let params' = if is_gadt env ty then [] else params in
      c, (params', ty'))

let abstract problem =
  let open Problem in
  let env = List.fold_right (Fun.uncurry Tenv.add_external_type) problem.ext_typ init_env in
  let term = abst_term ~env problem.term in
  let ext_typ = abst_ext_typ env problem.ext_typ in
  {problem with term; ext_typ}
