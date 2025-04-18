open Util
open Type

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

module Print = struct
  include Print_
  include Print_typ

  let typ = typ_init
  let decl = decl_init
end

type 'a t = {
  menv : (tconstr * ('a env * 'a Type.t)) list;  (** module environment *)
  tenv : (tconstr * ('a env * ('a params * 'a Type.t))) list;  (** type environment *)
  rebind : (tconstr * ('a env * path)) list;
      (** rebind (exception A = B) environment ([type t += A = B] is not yet supported) *)
}

and 'a env = { env : 'a t; prefix : prefix }
and prefix = Path.t option [@@deriving show]

let empty = { menv = []; tenv = []; rebind = [] }

let init () =
  {
    menv = [];
    tenv = [ (Path.id_of C.exn, ({ env = empty; prefix = None }, ([], TVariant (VNonPoly, [])))) ];
    rebind = [];
  }

let env_of_ext_mod menv =
  let menv = List.map (fun (x, y) -> (x, ({ env = empty; prefix = None }, y))) menv in
  { !!init with menv }

let print_length = ref (-1)
let set_print_length length = print_length := length

let print_init fm { menv; tenv; rebind } =
  let rebind = List.map (Pair.map_snd snd) rebind in
  let print_params fm params =
    match params with
    | [] -> ()
    | [ ty ] -> Format.fprintf fm "%a " Print.typ ty
    | _ -> Format.fprintf fm "(%a) " (print_list Print.typ ",") params
  in
  let pr_list pr xs = List.print ~limit:!print_length pr xs in
  let pr_decl fm (c, ({ prefix }, (ps, ty))) =
    Format.fprintf fm "[%s] %a%a = %a" (Path.string_of_option prefix) print_params ps Print.tconstr
      c Print.typ ty
  in
  let pr_rebind fm (s1, s2) =
    Format.fprintf fm "exception %a = %a" Print.tconstr s1 Print.path s2
  in
  let pr_mod fm (m, ({ prefix }, ty)) =
    Format.fprintf fm "[%s] %a = %a" (Path.string_of_option prefix) Id.print m Print.typ ty
  in
  Format.fprintf fm "@[@[menv: %a;@]@ @[tenv: %a;@]@ @[rebind: %a;@]@]" (pr_list pr_mod) menv
    (pr_list pr_decl) tenv (pr_list pr_rebind) rebind

let constr_of_path p = Id.make (Path.to_string p) ()
let tconstr_of_path p = Id.make (Path.to_string p) ()

let update_typ (s : path) pt ~env =
  match s with
  | LId c ->
      let tenv = List.modify_def pt c (fun _ -> pt) env.tenv in
      { env with tenv }
  | _ -> env (* WORKAROUND *)

let rec add_typ ?prefix constr (params, typ) env =
  let tenv = (constr, ({ env; prefix }, (params, typ))) :: env.tenv in
  { env with tenv }

and add_exn ext_row_path ext_row_args env =
  let row = { ext_row_path; ext_row_args; ext_row_ret = None } in
  add_extension_type C.exn ([], row) env

and add_ext_rebind ?prefix s1 s2 env =
  { env with rebind = (s1, ({ env; prefix }, s2)) :: env.rebind }

and add_ext (ext : 'a extension) env =
  match ext with
  | Ext_type (s, (params, row)) -> add_extension_type s (params, row) env
  | Ext_rebind (s, s') -> add_ext_rebind s s' env

(* TODO: treat mutual definition properly *)
and add_typ_decl ?prefix decls env = List.fold_right (Fun.uncurry (add_typ ?prefix)) decls env

(* TODO: treat mutual definition properly *)
and add_typ_decls ?prefix decls env = List.fold_right (add_typ_decl ?prefix) decls env

and add_external_type path (params, ty) env =
  let c = constr_of_path path in
  add_typ c (params, ty) env

(* TODO: Respect the order *)
and typ_is_in_sig { menv } sgn p =
  let env = List.map (Pair.map_snd snd) menv in
  sgn
  |> types_in_signature ~env
  |> List.exists (fun (prefix, (c, _)) -> Path.eq (add_prefix_opt prefix (LId c)) p)

(* TODO: Respect the order *)
and extensions_in_signature env sgn =
  sig_exts sgn
  @@@ (sig_values sgn
      |> List.filter is_mod_var
      |> List.rev_flatten_map (extensions_in_module ~add_prefix:true env))

(* TODO: Respect the order *)
and extensions_in_module ?(add_prefix = false) env m =
  (* BUGGY: assumed that type constructors are unique *)
  try
    let menv = List.map (Pair.map_snd snd) env.menv in
    let sgn = sig_of_id ~env:menv m in
    let m' = Id.set_typ m () in
    let map =
      sgn
      |> types_in_signature ~env:menv
      |> List.rev_map (fun (prefix, (c, _)) ->
             let prefix' = match prefix with None -> LId m' | Some p -> Path.cons m' p in
             (c, LDot (prefix', Id.name c)))
    in
    let aux_head p = if add_prefix && typ_is_in_sig env sgn p then Path.cons m' p else p in
    let aux_body { ext_row_path; ext_row_args; ext_row_ret } =
      let ext_row_path = if add_prefix then Path.cons m' ext_row_path else ext_row_path in
      let ext_row_args = List.map (subst_tconstr map) ext_row_args in
      { ext_row_path; ext_row_args; ext_row_ret }
    in
    sgn |> extensions_in_signature env |> Fmap.(list (aux_head * snd aux_body))
  with Invalid_argument _ -> [%invalid_arg]

(* This must be fixed (extension types must be managed by adding another field to ['a t]? ) *)
and add_extension_type s (params, row) env =
  match assoc_type s env with
  | env', (params', TVariant (VNonPoly, rows)) ->
      let row_constr = constr_of_path row.ext_row_path in
      let params'', row_ret, row_args =
        let tys = Option.to_list row.ext_row_ret @ row.ext_row_args in
        let _, params'', tys' = copy_tconstr_params_list params tys in
        if row.ext_row_ret = None then (params'', None, tys')
        else (params'', Some (List.hd tys'), List.tl tys')
      in
      List.iter2 instantiate params' params'';
      let typ = TVariant (VNonPoly, { row_constr; row_args; row_ret } :: rows) in
      update_typ s (env', (params', typ)) ~env
  | env', (params', _) ->
      (* WORKAROUND *)
      let rows = [] in
      let row_constr = constr_of_path row.ext_row_path in
      let params'', row_ret, row_args =
        let tys = Option.to_list row.ext_row_ret @ row.ext_row_args in
        let _, params'', tys' = copy_tconstr_params_list params tys in
        if row.ext_row_ret = None then (params'', None, tys')
        else (params'', Some (List.hd tys'), List.tl tys')
      in
      List.iter2 instantiate params' params'';
      let typ = TVariant (VNonPoly, { row_constr; row_args; row_ret } :: rows) in
      update_typ s (env', (params', typ)) ~env
  | exception Not_found ->
      Format.eprintf "@.Not found: %a@." Print.path s;
      [%invalid_arg]

(* TODO: support recursive modules *)
and add_module ?prefix (x : _ Id.t) ty ~env : _ t =
  match ty with
  | TModSig _ | TModLid _ ->
      let exts = extensions_in_module env ~add_prefix:true (Id.set_typ x ty) in
      let m = Id.set_typ x () in
      let env = { env with menv = (m, ({ env; prefix }, ty)) :: env.menv } in
      List.fold_right (Fun.uncurry add_extension_type) exts env
  | _ -> env

and add_sig_item ?prefix (x : _ sig_elem) (env : _ t) : _ t =
  match x with
  | Sig_type decl -> add_typ_decl ?prefix decl env
  | Sig_value c -> add_module ?prefix c (Id.typ c) ~env
  | Sig_ext (s, pty) -> add_extension_type s pty env

and assoc_item_in_sig inc_self ?prefix (env : _ t) (sgn : _ signature) (f : _ sig_elem -> bool) :
    _ t * _ =
  match
    List.fold_left
      (fun envr item ->
        match envr with
        | Either.Right _ -> envr
        | Left env ->
            let env' () = add_sig_item ?prefix item env in
            if f item then
              let env'' = if inc_self then !!env' else env in
              Right (env'', item)
            else Left !!env')
      (Left env) sgn
  with
  | Left _ -> raise Not_found
  | Right r -> r

and assoc_value_in_sig ?prefix (env : _ t) (sgn : _ signature) (s : string) : _ t * _ =
  match
    assoc_item_in_sig false ?prefix env sgn (function Sig_value c -> Id.name c = s | _ -> false)
  with
  | env, Sig_value c -> (env, Id.typ c)
  | _ -> assert false

and assoc_type_in_sig ?prefix (env : _ t) (sgn : _ signature) (s : string) : _ t * _ =
  let ch (c, _) = Id.name c = s in
  match
    assoc_item_in_sig true ?prefix env sgn (function
      | Sig_type decls -> List.exists ch decls
      | _ -> false)
  with
  | env, Sig_type decls -> (env, snd @@ List.find ch decls)
  | _ -> assert false

and assoc_module env p =
  let env, mty = assoc_value p ~env in
  ( env,
    sig_of_mod_typ
      ~env:(List.map (Pair.map_snd snd) env.env.menv)
      mty (* TODO: must use sig_of_mod below? *) )

(** Returns the type of the value of [path] *)
and assoc_value (path : path) ~env : _ env * _ Type.t =
  match
    match path with
    | LId constr -> Id.List.assoc constr env.menv
    | LDot (p, s) ->
        let { env; prefix }, sgn = assoc_module env p in
        let env, ty = assoc_value_in_sig ~prefix:p env sgn s in
        ({ env; prefix }, ty)
    | LApp (path1, path2) ->
        let arg, ty = ValE'._TFun @@ snd @@ assoc_value path1 ~env in
        (assert false, subst_path_head (Id.set_typ arg ()) path2 ty)
  with
  | r ->
      Dbg.printf "Tenv.assoc_value %a: %a@." Path.print path Print.typ (snd r);
      r
  | exception Not_found when !!Dbg.check ->
      Dbg.printf "Tenv.assoc_value %a: Not found@." Path.print path;
      raise Not_found

(** Returns the type declaration of [path] *)
and assoc_type ?(copy = true) (path : path) env : _ env * (_ params * _ Type.t) =
  match
    let prefix, pty =
      match path with
      | LId constr -> Id.List.assoc constr env.tenv
      | _ when Id.List.mem_assoc (tconstr_of_path path) env.tenv ->
          (* WORKAROUND: for Problem.ext_typ *)
          Id.List.assoc (tconstr_of_path path) env.tenv
      | LDot (p, s) ->
          let { env; prefix }, sgn = assoc_module env p in
          let env, (params, ty) = assoc_type_in_sig ~prefix:p env sgn s in
          ({ env; prefix }, (params, ty))
      | LApp (_, _) -> [%invalid_arg]
    in
    (prefix, if copy then snd @@ copy_tconstr_params pty else pty)
  with
  | r ->
      Dbg.printf "Tenv.assoc_type %a: %a@." Path.print path Print.typ (snd (snd r));
      r
  | exception Not_found ->
      Dbg.printf "Tenv.assoc_type %a: Not found@." Path.print path;
      raise Not_found

let assoc_type_opt path env = Option.try_with_not_found (assoc_type path) env
let assoc_value_opt path env = Option.try_with_not_found (fun env -> assoc_value path ~env) env
let mem_assoc_type path env = Exception.not_raise ~exn:Not_found (assoc_type path) env

let mem_assoc_value path env =
  Exception.not_raise ~exn:Not_found (fun env -> assoc_value path ~env) env

(*
let assoc_exn env =
  let labels = List.assoc_all (Path_.id_of C.exn) env.ext in
  TVariant(false, labels)
 *)

let assoc_constr _env _c = assert false

let assoc_exn env =
  match assoc_type C.exn env with
  | env, ([], TVariant (VNonPoly, rows)) ->
      (* TODO: this must be List.fold_* instead of List.map *)
      let rows' =
        try
          List.map
            (fun (s1, (_, s2)) -> { (assoc_row (constr_of_path s2) rows) with row_constr = s1 })
            env.env.rebind
        with Not_found ->
          let rebind = List.map (fun (s1, (_, s2)) -> (s1, s2)) env.env.rebind in
          Format.eprintf "rebind: %a@." Print.(list (tconstr * path)) rebind;
          Format.eprintf "labels: %a@." Print.(list row_init) rows;
          assert false
      in
      (env, TVariant (VNonPoly, rows' @ rows))
  | _ -> assert false
  | exception Not_found -> assert false

let sig_of_mod_typ ~env ty =
  try Type.sig_of_mod_typ ~env ty
  with Sig_of_Lid m -> (
    let menv = List.map (fun (x, y) -> (x, ({ env = empty; prefix = None }, y))) env in
    let env = { !!init with menv } in
    match assoc_value m ~env with
    | _, TModSig sgn -> sgn
    | _, TModLid _ -> [%invalid_arg]
    | _, TConstr (mty, []) -> (
        match assoc_type mty env with _, ([], TModSig sgn) -> sgn | _ -> assert false)
    | _ -> [%invalid_arg])

let rec normalize_type env ty =
  match elim_tattr ty with
  | TVar (_, { contents = Some ty' }, _) -> normalize_type env ty'
  | TConstr (c, tys) -> (
      match assoc_type_opt c env with
      | Some (_, pty) ->
          let ty' = apply_tconstr pty tys in
          assert (ty <> ty');
          normalize_type env ty'
      | None -> ty)
  | ty -> ty

let assoc_type ?(copy = true) (path : path) env : _ params * _ Type.t =
  snd @@ assoc_type ~copy path env

let assoc_value path ~env = snd @@ assoc_value path ~env
