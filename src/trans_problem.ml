open Util
open Problem

module Debug = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

let make_trans_cex_single p : Preprocess_common.trans_cex = function
  | [ (_, _, (lazy (ce, main))) ] ->
      let p' =
        match main with
        | None -> p
        | Some main -> Problem.map (Trans.replace_main ~force:true ~main) p
      in
      (Eval.trans ce p', main)
  | [] -> assert false
  | _ -> [%invalid_arg]

(** Remove annotations for the counterexample translation and generate a counterexample translater *)
let make_trans_cex p : Problem.t * Preprocess_common.trans_cex =
  (Problem.map Trans.remove_info_trans p, make_trans_cex_single p)

let copy_poly_values problem =
  assert (List.mem Set_main problem.attr);
  let map, eq, term, make_get_rtyp = Trans.copy_poly_values problem.term in
  let ref_env =
    map
    |> List.filter_map (fun (f, f') ->
           (* TODO: See the code for ext_ref_env below *)
           problem.spec.ref_env
           |> List.assoc_opt ~eq f
           |> Option.map (fun rty ->
                  let map, sty = Type.copy_tvar_typ @@ Ref_type.to_simple rty in
                  Type_util.unify sty (Id.typ f');
                  let map' = Fmap.(list (snd Ref_type.of_simple)) map in
                  let rty' = Ref_type.subst_tvar map' rty in
                  (f', rty')))
  in
  let ext_ref_env =
    (Syntax.get_fv term
    |> List.filter_map (fun f' ->
           problem.spec.ext_ref_env
           |> List.assoc_opt ~eq f'
           |> Option.map (fun (loc, rty) ->
                  let map, sty = Type.copy_tvar_typ @@ Ref_type.to_simple rty in
                  Type_util.unify sty (Id.typ f');
                  let map' = Fmap.(list (snd Ref_type.of_simple)) map in
                  let rty' = Ref_type.subst_tvar map' rty in
                  (f', (loc, rty')))))
    @ (map
      |> List.filter_map (fun (f, f') ->
             problem.spec.ext_ref_env
             |> List.assoc_opt ~eq f
             |> Option.map (fun (loc, rty) ->
                    let map, sty = Type.copy_tvar_typ @@ Ref_type.to_simple rty in
                    Type_util.unify sty (Id.typ f');
                    let map' = Fmap.(list (snd Ref_type.of_simple)) map in
                    let rty' = Ref_type.subst_tvar map' rty in
                    (f', (loc, rty')))))
  in
  let spec = { problem.spec with ref_env; ext_ref_env } in
  ({ problem with term; spec }, make_get_rtyp)

let add_preds get_env problem =
  let env = get_env problem.spec problem.term in
  if env = [] then None else Some (Problem.map (Trans.replace_typ env) problem)

let inline problem =
  let inlined_f = Spec.get_inlined_f problem.spec problem.term in
  map (Trans.inlined_f inlined_f) problem

let instansiate_poly_types_with_env ({ term; spec } as problem) =
  let env' =
    let ref_env = Spec.get_all_ref_env spec term in
    List.map (Pair.map_snd Ref_type.to_simple) ref_env
  in
  let term = Trans.instansiate_poly_types_with_env env' term in
  { problem with term }

let inline_simple_types problem =
  let map, term = Trans.inline_simple_types problem.term in
  let term =
    if Term_util.is_exn_free term then
      Term_util.Term.type_ [ (Type.(Path.id_of C.exn), ([], Type_util.Ty.unit)) ] term
    else term
  in
  let spec =
    let map' = List.map (fun (s, (_, ty)) -> (Type.LId s, Ref_type.of_simple ty)) map in
    let tr = List.fold_right (Fun.uncurry Ref_type.subst_constr) map' in
    Spec.map_ref tr problem.spec
  in
  { problem with term; spec }

let replace_base_with_int = map ~tr_ref:Ref_type.replace_base_with_int Trans.replace_base_with_int
let replace_data_with_int = map ~tr_ref:Ref_type.replace_constr_with_int Trans.replace_data_with_int
let replace_list_with_int = map ~tr_ref:Ref_type.replace_list_with_int Trans.replace_list_with_int

let replace_data_with_int_but_exn problem =
  let ty_exn, constrs =
    match Term_util.find_exn_typ problem.term with
    | None -> ([], [])
    | Some (Type.TVariant (_, rows) as ty) ->
        ([ ty; Type_util.typ_exn ], List.map (Type.row_constr |- Type.Path._LId) rows)
    | Some _ -> assert false
  in
  map
    ~tr_ref:(Ref_type.replace_constr_with_int_but_exn constrs)
    (Trans.replace_data_with_int_but ty_exn)
    problem

let split_assert problem =
  let update_info loc info =
    match loc with
    | None -> info
    | Some loc -> Format.asprintf "@[<h>Target assertion: %a@]" Location.print_loc loc :: info
  in
  problem.term
  |> Trans.split_assert
  |> List.map (fun (term, loc) -> { problem with term; info = update_info loc problem.info })

let expand_let_val problem =
  assert (List.mem CPS problem.attr);
  let term = Trans.expand_let_val problem.term in
  { problem with term }

let beta_reduce problem =
  assert (List.mem CPS problem.attr);
  let term = Trans.expand_let_val problem.term in
  { problem with term }

type Syntax.prep_info += Info_main of Syntax.lid option

let set_main problem =
  let attr = List.cons_unique Set_main problem.attr in
  match problem.kind with
  | Safety ->
      assert (problem.spec.assertion = []);
      let term, main = Trans.set_main problem.term in
      LazyList.singleton (Info_main main, { problem with term; attr })
  | Ref_type_check targets ->
      let open Term_util in
      let catch_all = make_catch_all problem.term in
      targets
      |> LazyList.of_list
      |> LazyList.map (fun (x, ty) ->
             let env, term = Trans.set_assert_ref_typ ~catch_all x ty problem.term in
             let env' = List.map (fun (x, ty) -> (x, (None, ty))) env in
             let ext_ref_env = env' @ problem.spec.ext_ref_env in
             let spec = { problem.spec with ext_ref_env } in
             (Info_main (Some (LId x)), { problem with term; spec; kind = Safety; attr }))

let rename_target_ext_funs problem =
  let spec = problem.spec in
  let ext_ref_env = spec.ext_ref_env in
  let map =
    List.filter_map
      (function _, (None, _) -> None | f, (Some loc, _) -> Some (f, (loc, Id.new_var_id f)))
      ext_ref_env
  in
  let ext_ref_env =
    let aux (f, (loc, ty)) =
      let f' =
        match loc with
        | None -> f
        | Some loc -> snd @@ snd @@ List.find (fun (g, (loc', _)) -> f = g && loc = loc') map
      in
      (f', (None, ty))
    in
    List.map aux ext_ref_env
  in
  let term = Trans.rename_target_ext_funs map problem.term in
  let spec = { spec with ext_ref_env } in
  let attr = List.cons_unique Set_main problem.attr in
  { problem with term; spec; attr }

let make_ext_funs problem =
  let env = List.map (Pair.map_snd snd) problem.spec.ext_ref_env in
  let term = Trans.make_ext_funs ~annot:true env problem.term in
  let spec = { problem.spec with ext_ref_env = [] } in
  { problem with term; spec } |> make_trans_cex

let alpha_rename problem =
  let map_rtyp _ get_rtyp f = get_rtyp f in
  let term = Trans.alpha_rename ~whole:true ~set_counter:true problem.term in
  let map = [] in
  (* TODO *)
  ({ problem with term }, map_rtyp map)

let split_by_ref_type problem =
  let spec = problem.spec in
  let ref_env = spec.ref_env in
  if ref_env = [] then None
  else
    let ext_ref_env = List.map (fun (f, ty) -> (f, (None, ty))) ref_env @ spec.ext_ref_env in
    match problem.kind with
    | Safety ->
        let aux (target, term) =
          match target with
          | None ->
              (* rest *)
              let spec = { spec with ext_ref_env; ref_env = [] } in
              LazyList.singleton { problem with term; spec }
          | Some (f, ty) ->
              (* target is `f` *)
              let spec =
                let ext_ref_env = List.filter_out (fun (g, _) -> Id.(f = g)) ext_ref_env in
                let ref_env = [] in
                { spec with ext_ref_env; ref_env }
              in
              let kind = Ref_type_check [ (f, ty) ] in
              let info =
                Format.asprintf "@[<h>Check %a: %a@]" Print.id f Ref_type.print ty :: problem.info
              in
              { problem with term; spec; kind; info } |> set_main |> LazyList.map snd
        in
        problem.term
        |> Trans.split_by_ref_type ref_env
        |> LazyList.of_list
        |> LazyList.concat_map aux
        |> Option.some
    | Ref_type_check _ -> assert false

let inline_record_type problem =
  let tr_ref =
    let open Term_util in
    let adts =
      Spec.get_all_ref_env problem.spec problem.term |> List.flatten_map (snd |- Ref_type.col_constr)
    in
    let declss, _ = split_type_decl_and_body problem.term in
    let aux decls map =
      (* TODO: Support recursive declaration *)
      let decls' = List.filter (function _, (_, Type.TRecord _) -> true | _ -> false) decls in
      List.map (Pair.map_snd @@ subst_tconstr_map_typ decls') map
    in
    let map =
      adts
      |> List.map (fun s -> (s, Type.TConstr (s, [])))
      |> List.fold_right aux declss
      |> List.filter_out (fun (s, ty) -> Type.TConstr (s, []) = ty)
      |> List.map (Pair.map_snd Ref_type.of_simple)
    in
    List.fold_right (Fun.uncurry Ref_type.subst_constr) map
  in
  map ~tr_ref Trans.inline_record_type problem

let elim_unused_assumption problem =
  let spec =
    let fv = Syntax.get_fv problem.term in
    let ext_ref_env = List.filter (fst |- Id.List.mem -$- fv) problem.spec.ext_ref_env in
    { problem.spec with ext_ref_env }
  in
  { problem with spec }

let elim_unused_let problem =
  let fs : (Syntax.term -> Syntax.term) list = [ Trans.elim_unused_let ~leave_last:true ] in
  let fs : (Syntax.term -> Syntax.term) list =
    if !Flag.Method.use_elim_may_div then
      Trans.elim_unused_let ~leave_last:true ~elim_may_div:true :: fs
    else fs
  in
  fs |> LazyList.of_list |> LazyList.map (map -$- problem)

let merge_deref problem =
  if Term_util.has_deref problem.term then
    match Trans.merge_deref problem.term with
    | None -> None
    | Some term -> Some { problem with term }
  else None

let lift_type_decl problem =
  let term = Trans.lift_type_decl problem.term in
  { problem with term }

let replace_abst_with_int = map ~tr_ref:Ref_type.replace_abst_with_int Trans.replace_abst_with_int

let fail_free problem =
  let has_precondition =
    let raise_if_has_precondition ty = if Ref_type.has_precondition ty then raise Found in
    let it = Syntax.Iter2.make () in
    it.desc <-
      (fun env desc ->
        match desc with
        | Var (LId x) -> Id.List.assoc_opt x env |> Option.iter raise_if_has_precondition
        | Var _ -> [%unsupported]
        | _ -> it.desc_rec env desc);
    Exception.does_raise ~exn:Found -| it.term
  in
  let has_fail_or_raise env = Term_util.has_fail ||| Term_util.has_raise ||| has_precondition env in
  problem.term
  |> Trans.elim_unused_let ~leave_last:true
  |> has_fail_or_raise problem.spec.ref_env
  |> not

let reduce_fail_free problem =
  match problem.kind with
  | Safety when fail_free problem -> Some { problem with term = Term_util.Term.unit }
  | _ -> None

let reduce_rand p = Problem.map (Trans.reduce_rand ~annot:true) p |> make_trans_cex

let add_ref_check p =
  let term = Trans.add_ref_check p.spec.ref_env p.term in
  let spec = { p.spec with ref_env = [] } in
  { p with term; spec } |> make_trans_cex

let reduce_external p =
  let fs = List.map fst p.spec.ext_ref_env in
  let term = Trans.reduce_external fs p.term in
  { p with term }
