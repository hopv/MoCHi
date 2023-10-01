open Util
open Type

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

module Print = struct
  include Print_
  include Print_typ
  let typ = typ_init
  let decl = decl_init
end


(* TODO: 'a t must be recursive *)
type 'a t =
  {menv: (tconstr * 'a Type.t) list;               (** module environment *)
   tenv: (tconstr * ('a params * 'a Type.t)) list; (** type environment *)
   rebind: (tconstr * path) list}                  (** rebind (exception A = B) environment *)
[@@deriving show]

let empty() =
  {menv = [];
   tenv = [Path.id_of C.exn, ([], TVariant(VNonPoly, []))];
   rebind = []}

let env_of_ext_mod menv =
  {!!empty with menv}

let print_length = ref (-1)
let set_print_length length = print_length := length

let print_init fm {menv; tenv; rebind} =
  let print_params fm params =
    match params with
    | [] -> ()
    | [ty] -> Format.fprintf fm "%a " Print.typ ty
    | _ -> Format.fprintf fm "(%a) " (print_list Print.typ ",") params
  in
  let pr_list pr xs = List.print ~limit:!print_length pr xs in
  let pr_decl fm (c,(ps,ty)) = Format.fprintf fm "%a%a = %a" print_params ps Print.tconstr c Print.typ ty in
  let pr_rebind fm (s1,s2) = Format.fprintf fm "exception %a = %a" Print.tconstr s1 Print.path s2 in
  Format.fprintf fm "@[@[menv: %a;@]@ @[tenv: %a;@]@ @[rebind: %a;@]@]"
    (pr_list Print.(Id.print * typ)) menv
    (pr_list pr_decl) tenv
    (pr_list pr_rebind) rebind

let constr_of_path p =
  Id.make (Path.to_string p) ()
let tconstr_of_path p =
  Id.make (Path.to_string p) ()

let update_typ (s : path) pt ~env =
  match s with
  | LId c ->
      let tenv = List.modify_def pt c (fun _ -> pt) env.tenv in
      {env with tenv}
  | _ -> env (* WORKAROUND *)

let rec typ_is_in_sig env sgn p =
  sgn
  |> types_in_signature ~env:env.menv
  |> List.exists (fun (prefix,(c,_)) -> Path.eq (add_prefix_opt prefix (LId c)) p)

and extensions_in_signature env {sig_ext; sig_values} =
  sig_ext @@@
    (sig_values
     |> List.filter is_mod_var
     |> List.rev_flatten_map (extensions_in_module ~add_prefix:true env))

and extensions_in_module ?(add_prefix=false) env m = (* BUGGY: assumed that type constructors are unique *)
  try
    let sgn = sig_of_id ~env:env.menv m in
    let m' = Id.set_typ m () in
    let map =
      sgn
      |> types_in_signature ~env:env.menv
      |> List.rev_map (fun (prefix,(c,_)) ->
             let prefix' =
               match prefix with
               | None -> LId m'
               | Some p -> Path.cons m' p
             in
             c, LDot(prefix', Id.name c))
    in
    let aux_head p =
      if add_prefix && typ_is_in_sig env sgn p then Path.cons m' p else p
    in
    let aux_body {ext_row_path; ext_row_args; ext_row_ret} =
      let ext_row_path = if add_prefix then Path.cons m' ext_row_path else ext_row_path in
      let ext_row_args = List.map (subst_tconstr map) ext_row_args in
      {ext_row_path; ext_row_args; ext_row_ret}
    in
    sgn
    |> extensions_in_signature env
    |> Fmap.(list (aux_head * snd aux_body))
  with Invalid_argument _ -> [%invalid_arg]

and add_extension_type s (params, row) env =
  match assoc_type s env with
  | (params', TVariant(VNonPoly,rows)) ->
      let row_constr = constr_of_path row.ext_row_path in
      let params'',row_ret,row_args =
        let tys = Option.to_list row.ext_row_ret @ row.ext_row_args in
        let _,params'',tys' = copy_tconstr_params_list params tys in
        if row.ext_row_ret = None then
          params'', None, tys'
        else
          params'', Some (List.hd tys'), List.tl tys'
      in
      List.iter2 instantiate params' params'';
      let typ = TVariant(VNonPoly, {row_constr;row_args;row_ret}::rows) in
      update_typ s (params', typ) ~env
  | (params', _) -> (* WORKAROUND *)
      let rows = [] in
      let row_constr = constr_of_path row.ext_row_path in
      let params'',row_ret,row_args =
        let tys = Option.to_list row.ext_row_ret @ row.ext_row_args in
        let _,params'',tys' = copy_tconstr_params_list params tys in
        if row.ext_row_ret = None then
          params'', None, tys'
        else
          params'', Some (List.hd tys'), List.tl tys'
      in
      List.iter2 instantiate params' params'';
      let typ = TVariant(VNonPoly, {row_constr;row_args;row_ret}::rows) in
      update_typ s (params', typ) ~env
  | exception Not_found ->
      Format.eprintf "@.Not found: %a@." Print.path s;
      [%invalid_arg]

and add_module x ty ~env =
  match ty with
  | TModSig _
  | TModLid _ ->
      let exts = extensions_in_module env ~add_prefix:true (Id.set_typ x ty) in
      let m = Id.set_typ x () in
      let env = {env with menv = (m, ty)::env.menv} in
      List.fold_right (Fun.uncurry add_extension_type) exts env
  | _ -> env

(** Returns the type of the value of [path] *)
and assoc_value (path:path) ~env : _ Type.t =
  match
    match path with
    | LId constr ->
        Id.List.assoc constr env.menv
    | LDot _ ->
        let hd = Path.head path in
        let path_of (p,x) = add_prefix_opt p (LId (Id.set_typ x ())) in
        let m = Id.set_typ hd @@ List.assoc ~eq:(Eq.on Id.name) hd env.menv in
        m
        |> values_in_module ~env:env.menv
        |> List.find (fun px -> Path.eq (path_of px) path)
        |> snd
        |> Id.typ
    | LApp(path1, path2) ->
        let arg,ty = ValE'._TFun @@ assoc_value path1 ~env in
        subst_path_head (Id.set_typ arg ()) path2 ty
  with
  | r ->
      Dbg.printf "Tenv.assoc_value %a: %a@." Path.print path Print.typ r;
      r
  | exception Not_found when !!Dbg.check ->
      Dbg.printf "Tenv.assoc_value %a: Not found@." Path.print path;
      raise Not_found

(** Returns the type declaration of [path] *)
and assoc_type ?(copy=true) (path:path) env : _ params * _ Type.t =
  match
    let pty =
      match path with
      | LId constr ->
          Id.List.assoc constr env.tenv
      | _ when Id.List.mem_assoc (tconstr_of_path path) env.tenv -> (* WORKAROUND: for Problem.ext_typ *)
          Id.List.assoc (tconstr_of_path path) env.tenv
      | LDot _ ->
          let hd = Path.head path in
          let path_of (p,(c,_x)) = add_prefix_opt p (LId (Id.set_typ c ())) in
          let m = Id.set_typ hd @@ List.assoc ~eq:(Eq.on Id.name) hd env.menv in
          m
          |> types_in_module ~env:env.menv
          |> List.find (fun pcty -> Path.eq (path_of pcty) path)
          |> snd
          |> snd
      | LApp(_, _) -> [%invalid_arg]
    in
    if copy then
      snd @@ copy_tconstr_params pty
    else
      pty
  with
  | r ->
      Dbg.printf "Tenv.assoc_type %a: %a@." Path.print path Print.typ (snd r);
      r
  | exception Not_found ->
      Dbg.printf "Tenv.assoc_type %a: Not found@." Path.print path;
      raise Not_found

let assoc_type_opt path env = Option.try_with_not_found (assoc_type path) env
let assoc_value_opt path env = Option.try_with_not_found (fun env -> assoc_value path ~env) env
let mem_assoc_type path env = Exception.not_raise ~exn:Not_found (assoc_type path) env
let mem_assoc_value path env = Exception.not_raise ~exn:Not_found (fun env -> assoc_value path ~env) env

(*
let assoc_exn env =
  let labels = List.assoc_all (Path_.id_of C.exn) env.ext in
  TVariant(false, labels)
 *)

let assoc_constr _env _c =
  assert false

let assoc_exn env =
  match assoc_type C.exn env with
  | [], TVariant(VNonPoly,rows) ->
      (* TODO: this must be List.fold_* instead of List.map *)
      let rows' =
        try
          List.map (fun (s1,s2) -> {(assoc_row (constr_of_path s2) rows) with row_constr=s1}) env.rebind
        with Not_found ->
          Format.eprintf "rebind: %a@." Print.(list (tconstr * path)) env.rebind;
          Format.eprintf "labels: %a@." Print.(list row_init) rows;
          assert false
      in
      TVariant(VNonPoly, rows' @ rows)
  | _ -> assert false
  | exception Not_found -> assert false

let add_typ constr (params,typ) env =
  {env with tenv = (constr,(params,typ))::env.tenv}

let add_exn ext_row_path ext_row_args env =
  let row = {ext_row_path; ext_row_args; ext_row_ret=None} in
  add_extension_type C.exn ([], row) env

let add_ext_rebind s1 s2 env =
  {env with rebind = (s1,s2) :: env.rebind}

let add_ext (ext : 'a extension) env =
  match ext with
  | Ext_type(s,(params,row)) -> add_extension_type s (params,row) env
  | Ext_rebind(s,s') -> add_ext_rebind s s' env

let add_typ_decl decls env =
  List.fold_right (Fun.uncurry add_typ) decls env
let add_typ_decls decls env =
  List.fold_right (List.fold_right (Fun.uncurry add_typ)) decls env

let add_external_type path (params,ty) env =
  let c = constr_of_path path in
  add_typ c (params,ty) env

let sig_of_mod_typ ~env ty =
  try
    sig_of_mod_typ ~env:env ty
  with Sig_of_Lid m ->
         let env = {!!empty with menv = env} in
         match assoc_value m ~env with
         | TModSig sgn -> sgn
         | TModLid _ -> [%invalid_arg]
         | TConstr _ -> [%unsupported]
         | _ -> [%invalid_arg]

let rec normalize_type env ty =
  match elim_tattr ty with
  | TVar(_,{contents = Some ty'},_) -> normalize_type env ty'
  | TConstr(c, tys) ->
      (match assoc_type_opt c env with
       | Some pty ->
           let ty' = apply_tconstr pty tys in
           assert (ty <> ty');
           normalize_type env ty'
       | None -> ty)
  | ty -> ty
