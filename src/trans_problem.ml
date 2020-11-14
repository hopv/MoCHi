open Util
open Problem

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let copy_poly_funs problem =
  assert (List.mem Set_main problem.attr);
  map_on Focus.fst Trans.copy_poly_funs problem

let add_preds get_env problem =
  let env = get_env problem.spec problem.term in
  if env = [] then
    None
  else
    Some (Problem.map (Trans.replace_typ env) problem)

let inline problem =
  let inlined_f = Spec.get_inlined_f problem.spec problem.term in
  map (Trans.inlined_f inlined_f) problem

let instansiate_poly_types_with_env ({term; spec} as problem) =
  let env' =
    let ref_env = Spec.get_all_ref_env spec term in
    List.map (Pair.map_snd Ref_type.to_simple) ref_env
  in
  let term = Trans.instansiate_poly_types_with_env env' term in
  {problem with term}

let inline_simple_types problem =
  let map,term = Trans.inline_simple_types problem.term in
  let spec =
    let map' = List.map (Pair.map_snd Ref_type.of_simple) map in
    let tr = List.fold_right (Fun.uncurry Ref_type.subst_adt) map' in
    Spec.map_ref tr problem.spec
  in
  {problem with term; spec}

let replace_base_with_int =
  map
    ~tr_ref:Ref_type.replace_base_with_int
    Trans.replace_base_with_int

let replace_data_with_int =
  map
    ~tr_ref:Ref_type.replace_data_with_int
    Trans.replace_data_with_int

let replace_list_with_int =
  map
    ~tr_ref:Ref_type.replace_list_with_int
    Trans.replace_list_with_int

let replace_data_with_int_but_exn problem =
  let ty_exn,constrs =
    match Term_util.find_exn_typ problem.term with
    | None -> None, []
    | Some (Type.TVariant(_, labels) as ty) -> Some ty, List.map fst labels
    | Some _ -> assert false
  in
  map
    ~tr_ref:(Ref_type.replace_data_with_int_but_exn constrs)
    (Trans.replace_data_with_int_but ty_exn) problem

let split_assert problem =
  let update_info loc info =
    match loc with
    | None -> info
    | Some loc -> Format.asprintf "@[<h>Target assertion: %a@]" Location.print_loc loc :: info
  in
  problem.term
  |> Trans.split_assert
  |> List.map (fun (term,loc) -> {problem with term; info=update_info loc problem.info})
  |> LazyList.of_list

let expand_let_val problem =
  assert (List.mem ACPS problem.attr);
  let term = Trans.expand_let_val problem.term in
  {problem with term}

let beta_reduce problem =
  assert (List.mem ACPS problem.attr);
  let term = Trans.expand_let_val problem.term in
  {problem with term}

let set_main problem =
  match problem.kind with
  | Safety ->
      assert (problem.spec.assertion = []);
      let term = Trans.set_main problem.term in
      LazyList.singleton {problem with term}
  | Ref_type_check targets ->
      let open Term_util in
      let catch_all = make_catch_all problem.term in
      let make_check (x, ty) =
        let env,term = Trans.set_assert_ref_typ ~catch_all x ty problem.term in
        let env' = List.map (fun (x,ty) -> x, None, ty) env in
        let ext_ref_env = env' @ problem.spec.ext_ref_env in
        let spec = {problem.spec with ext_ref_env} in
        {problem with term; spec; kind=Safety}
      in
      targets
      |> LazyList.of_list
      |> LazyList.map make_check

let rename_target_ext_funs problem =
  let spec = problem.spec in
  let ext_ref_env = spec.ext_ref_env in
  let map = List.filter_map (function (_,None,_) -> None | (f,Some loc,_) -> Some (f,loc,Id.new_var_id f)) ext_ref_env in
  let ext_ref_env =
    let aux (f,loc,ty) =
      let f' =
        match loc with
        | None -> f
        | Some loc -> Triple.trd @@ List.find (fun (g,loc',_) -> f = g && loc = loc') map
      in
      f', None, ty
    in
    List.map aux ext_ref_env
  in
  let term = Trans.rename_target_ext_funs map problem.term in
  let spec = {spec with ext_ref_env} in
  let attr = Set_main::problem.attr in
  {problem with term; spec; attr}

let make_ext_funs problem =
  let env = List.map Triple.take13 problem.spec.ext_ref_env in
  let term = Trans.make_ext_funs env problem.term in
  let spec = {problem.spec with ext_ref_env=[]} in
  {problem with term; spec}

let alpha_rename problem =
  let map_rtyp _ get_rtyp f = get_rtyp f in
  let term = Trans.alpha_rename ~whole:true ~set_counter:true problem.term in
  let map = [] in (* TODO *)
  {problem with term}, map_rtyp map

let split_by_ref_type problem =
  let spec = problem.spec in
  let ref_env = spec.ref_env in
  if ref_env = [] then
    None
  else
    let ext_ref_env = List.map (fun (f,ty) -> f, None, ty) ref_env @ spec.ext_ref_env in
    match problem.kind with
    | Safety ->
        let aux (target, term) =
          match target with
          | None -> (* rest *)
              let spec = {spec with ext_ref_env; ref_env=[]} in
              LazyList.singleton {problem with term; spec}
          | Some (f,ty) -> (* target is `f` *)
              let spec =
                let ext_ref_env = List.filter_out (fun (g,_,_) -> Id.(f = g)) ext_ref_env in
                let ref_env = [] in
                {spec with ext_ref_env; ref_env}
              in
              let kind = Ref_type_check [f,ty] in
              let info = Format.asprintf "@[<h>Check %a: %a@]" Print.id f Ref_type.print ty :: problem.info in
              set_main {problem with term; spec; kind; info}
        in
        problem.term
        |> Trans.split_by_ref_type ref_env
        |> LazyList.of_list
        |> LazyList.concat_map aux
        |> Option.some
    | Ref_type_check _ -> assert false

let slice_top_fun ?(num = !Flag.Method.slice_num) problem =
  let unsafe_ext_funs =
    problem.spec.ext_ref_env
    |> List.filter_out (Ref_type.is_safe_fun -| Triple.trd)
    |> List.map Triple.fst
  in
  let slice = Slice.slice_top_fun unsafe_ext_funs problem.Problem.term in
  let make i =
    let p = float (i+1) /. float num in
    let term = slice p in
    let info = Format.sprintf "Slice %.3f" p :: problem.info in
    let attr = Sliced :: List.filter_out ((=) Set_main) problem.attr in
    {problem with term; info; attr}
  in
  if !Flag.Method.slice_i < 0 then (* for debug/experiments *)
    LazyList.init num make
  else
    LazyList.singleton (make !Flag.Method.slice_i)

let set_main_for_slice problem =
  assert (List.mem Sliced problem.attr);
  let target =
    let open Term_util in
    let main = get_main problem.term in
    match main.desc with
    | Tuple [] -> None
    | Tuple ts -> Some (List.map (Option.get -| decomp_var) ts)
    | _ -> assert false
  in
  let attr = Set_main :: List.filter_out ((=) Sliced) problem.attr in
  match target with
  | None ->
      let term = Trans.set_main problem.term in
      LazyList.singleton {problem with term; attr}
  | Some target ->
      let aux f =
        let term = Trans.set_main_for ~force:true [f] problem.term in
        let info = Format.asprintf "Target %a" Print.id f :: problem.info in
        {problem with term; info; attr}
      in
      target
      |&(!Flag.Method.slice_target <> "")&> List.filter (fun x -> Id.to_string x = !Flag.Method.slice_target)
      |> LazyList.of_list
      |> LazyList.map aux

let inline_record_type problem =
  let tr_ref =
    let open Term_util in
    let adts =
      Spec.get_all_ref_env problem.spec problem.term
      |> List.flatten_map (snd |- Ref_type.col_adt)
    in
    let declss,_ = split_type_decl_and_body problem.term in
    let aux decls map = (* TODO: Support recursive declaration *)
      let decls' = List.filter (function (_,Type.TRecord _) -> true | _ -> false) decls in
      List.map (Pair.map_snd @@ subst_tdata_map_typ decls') map
    in
    let map =
      adts
      |> List.map (fun s -> s, Type.TData s)
      |> List.fold_right aux declss
      |> List.filter_out (fun (s,ty) -> Type.TData s = ty)
      |> List.map (Pair.map_snd Ref_type.of_simple)
    in
    List.fold_right (Fun.uncurry Ref_type.subst_adt) map
  in
  map ~tr_ref Trans.inline_record_type problem

let elim_unused_assumption problem =
  let spec =
    let fv = Term_util.get_fv problem.term in
    let ext_ref_env = List.filter (Triple.fst |- Id.mem -$- fv) problem.spec.ext_ref_env in
    {problem.spec with ext_ref_env}
  in
  {problem with spec}

let elim_unused_let problem =
  let fs : (Syntax.term -> Syntax.term) list =
    [Trans.elim_unused_let ~leave_last:true]
  in
  let fs : (Syntax.term -> Syntax.term) list =
    if !Flag.Method.use_elim_may_div then
      Trans.elim_unused_let ~leave_last:true ~elim_may_div:true :: fs
    else
      fs
  in
  fs
  |> LazyList.of_list
  |> LazyList.map (map -$- problem)
