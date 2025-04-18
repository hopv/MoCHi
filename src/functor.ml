open Util
open Type
open Type_util
open Syntax
open Term_util

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

(** [remove env t] removes functors in let-bindings and signatures *)
let remove : (tconstr * typ) list -> term -> term =
  let tr = Tr2.make () in
  let tr_decl env decl =
    match tr.decl_rec env decl with
    | Decl_let decls -> Decl_let (List.filter_out (is_functor env -| snd) decls)
    | decl -> decl
  in
  let tr_typ env ty =
    match tr.typ_rec env ty with
    | TModSig sgn ->
        sgn
        |> List.filter_out (function
             | Sig_value x -> is_functor_typ ~env:(`Mod_env env) @@ Id.typ x
             | _ -> false)
        |> _TModSig
    | TConstr (path, _) when Path.has_app path -> Ty.unknown (* WORKAROUND: Support Tmty_with *)
    | ty -> ty
  in
  tr.decl <- tr_decl;
  tr.term <- tr.term_rec |-- set_afv_shallowly;
  tr.typ <- tr_typ;
  tr.term

(** [to_abst ty] returns [ty] in which there are neither functor types nor functor applications *)
let to_abst =
  make_trans (fun _ ty ->
      match ty with
      | TFun _ when is_functor_typ ty -> Some Ty.abst
      | TConstr (p, _) when Path.has_app p -> Some Ty.abst
      | _ -> None)

(* TODO: Check conflict with existing modules *)
let nam_counter = ref 1

let check_arg_module t =
  match t.desc with App _ -> is_mod_typ t.typ && not (is_rand_unit t) | _ -> false

let rec normalize_arg_module_aux t =
  match t.desc with
  | App (t11, ts) ->
      let ts', decls =
        ts
        |> List.split_map (fun t ->
               match t.desc with
               | Var _ -> (t, [])
               | _ ->
                   let t', decls =
                     if check_arg_module t then normalize_arg_module_aux t else (t, [])
                   in
                   let name = "Arg" ^ string_of_int !nam_counter in
                   incr nam_counter;
                   let arg = Id.new_var ~name t.typ in
                   (Term.var arg, decls @ [ Decl_let [ (arg, t') ] ]))
      in
      (set_typ Term.(t11 @ ts') t.typ, List.flatten decls)
  | _ -> [%invalid_arg]

let normalize_arg_module : term -> term =
  make_decl_trans (fun decl ->
      match decl with
      | Decl_let [ (m, ({ desc = App _ } as t1)) ] when check_arg_module t1 ->
          let t1', decls = normalize_arg_module_aux t1 in
          decls @@@ [ Decl_let [ (m, t1') ] ]
          (* TODO: Fix the order of decls w.r.t. evaluation strategy *)
      | _ -> [ decl ])

(* TODO: Check the conflict with existing modules *)
let normalize_include =
  make_decl_trans (fun decl ->
      match decl with
      | Include t1 when not (Is._Var t1) ->
          let x = new_var_of_term t1 in
          [ Decl_let [ (x, t1) ]; Include [%term x] ]
      | _ -> [ decl ])

type prefix = [ `Id of unit Id.t | `Str of string ] list
and env = Env of (prefix * env ref * declaration) list [@@deriving show]

let print_prefix fm prefix =
  let pr fm = function `Id x -> Id.print fm x | `Str s -> Format.pp_print_string fm s in
  Print.list pr fm prefix

let print_prefix = pp_prefix

let rec print_env depth fm (Env env) =
  if depth < 0 && env <> [] then Format.fprintf fm "..."
  else
    let pr fm (prefix, env, decl) =
      Format.fprintf fm "@[%a,@ %a%a%t,@ %a@]" print_prefix prefix Color.set Blue
        (print_env (depth - 1))
        !env Color.reset Print.decls [ decl ]
    in
    Format.fprintf fm "@[Env %a@]" Print.(list pr) env

let print_env = print_env 0
let string_of_prefix_elem = function `Id x -> Id.name x | `Str s -> s

let lid_of_prefix (prefix : prefix) =
  match prefix with
  | `Id hd :: tl ->
      List.map string_of_prefix_elem tl |> List.fold_left _LDot (LId (Id.set_typ hd Ty.unknown))
  | _ -> [%invalid_arg]

let prefix_of_path path =
  let hd, tl = Path.flatten path in
  `Id hd :: List.map (fun s -> `Str s) tl

let path_of_prefix (prefix : prefix) =
  match prefix with
  | `Id hd :: tl -> List.map string_of_prefix_elem tl |> List.fold_left Type._LDot (LId hd)
  | _ -> [%invalid_arg]

let add_to_env ?(recursive = false) prefix decl (Env env) =
  let env' = ref (Env []) in
  Dbg.printf "add_to_env prefix: %a@." print_prefix prefix;
  Dbg.printf "             decl: %a@." Print.decls [ decl ];
  Dbg.printf "              env: %a@." print_env (Env env);
  if recursive then (
    env' := Env ((prefix, env', decl) :: env);
    !env')
  else Env ((prefix, ref (Env env), decl) :: env)

let map_env f (Env env) = Env (f env)

let target_of target s =
  match target with `Var -> `Var s | `TConstr -> `TConstr s | `Constr -> `Constr s

let assoc_defs s decls = decls |> List.find_opt (fst |- Id.name |- ( = ) s) |> Option.map snd

let string_of_target_with = function
  | `Var s -> Format.sprintf "Var %s" s
  | `TConstr s -> Format.sprintf "TConstr %s" s
  | `Constr s -> Format.sprintf "Constr %s" s

let string_of_target = function `Var -> "Var" | `TConstr -> "TConstr" | `Constr -> "Constr"

let rec assoc_decl env target decl =
  let ( let* ) = Option.( let* ) in
  match (target, decl) with
  | _, Include { desc = Var x } ->
      let* _, env, r = assoc_gen env `Var (path_of_lid x) in
      let* decls = match r with `Var { desc = Module decls } -> Some decls | _ -> None in
      assoc_decls env [] target decls (* TODO: prefix? *) |> snd
  | _, Include _ -> [%unsupported]
  | `Var s, Decl_let defs -> assoc_defs s defs |> Option.map (fun t -> `Var t)
  | `Var _, _ -> None
  | `TConstr s, Decl_type tdecls -> assoc_defs s tdecls |> Option.map (fun _ -> `TConstr)
  | `TConstr _, _ -> None
  | `Constr s, Decl_type tdecls ->
      tdecls
      |> List.find_opt (function _, (_, TConstr (LId c, _)) -> Id.name c = s | _ -> false)
      |> Option.map (fun _ -> `Constr)
  | `Constr s, Type_ext (Ext_type (_, (_, { ext_row_path = LId c }))) when Id.name c = s ->
      Some `Constr
  | `Constr s, Type_ext (Ext_rebind (c, _)) when Id.name c = s -> Some `Constr
  | `Constr _, _ -> None

and assoc_decls env prefix target decls =
  List.L.fold_left decls ~init:(env, None) ~f:(fun (env, r) decl ->
      match r with
      | Some _ -> (env, r)
      | None ->
          let env' = add_to_env prefix decl env in
          let r' = assoc_decl env' target decl in
          (env', r'))

and assoc_gen (Env env) target (path : path) =
  let ( let* ) = Option.( let* ) in
  match path with
  | LId x -> (
      let target = target_of target (Id.name x) in
      let* prefix, env', t =
        List.L.find_map_opt env ~f:(fun (prefix, env'', decl) ->
            assoc_decl !env'' target decl |> Option.map (Triple.triple prefix env''))
      in
      match t with
      | `Var { desc = Var y } -> assoc_gen !env' `Var (path_of_lid y)
      | _ -> Some (prefix, !env', t))
  | LDot (path', s) ->
      let* prefix, env', decls =
        match assoc_gen (Env env) `Var path' with
        | Some (prefix, env, `Var { desc = Module decls }) -> Some (prefix, env, decls)
        | _ -> None
      in
      let prefix' = prefix @ prefix_of_path path' in
      let target = target_of target s in
      let env'', t = assoc_decls env' prefix' target decls in
      Some (prefix, env'', Option.get t)
  | LApp _ -> None (* external functor *)

let assoc_var env lid =
  match assoc_gen env `Var (path_of_lid lid) with
  | None -> None
  | Some (prefix, env', `Var t) -> Some (prefix, env', t)
  | Some _ -> assert false

let assoc_tconstr env c =
  match assoc_gen env `TConstr c with
  | None -> None
  | Some (prefix, _, `TConstr) -> Some prefix
  | _ -> assert false

let assoc_constr env c =
  match assoc_gen env `Constr c with
  | None -> None
  | Some (prefix, _, `Constr) -> Some prefix
  | _ -> assert false

let add_prefix_lid prefix lid =
  match prefix with
  | [] -> lid
  | _ ->
      let hd, ss = Lid.flatten lid in
      List.fold_left _LDot (lid_of_prefix prefix) (Id.name hd :: ss)

let add_prefix_path (prefix : prefix) path =
  match prefix with
  | [] -> path
  | _ ->
      let hd, ss = Path.flatten path in
      List.fold_left Type._LDot (path_of_prefix prefix) (Id.name hd :: ss)

let move_lid (prefix_dst, env) x =
  match assoc_var env x with
  | None -> x
  | Some (prefix_src, _, _) ->
      let _, prefix_src', _ = List.decomp_common_prefix prefix_src prefix_dst in
      (*
      Dbg.printf "move[%a] env: %a@." Print.lid x print_env (Env env);
      Dbg.printf "move[%a] prefix_src: %a@." Print.lid x print_prefix prefix_src;
      Dbg.printf "move[%a] prefix_dst: %a@." Print.lid x print_prefix prefix_dst;
      Dbg.printf "move[%a] prefix_src': %a@.@." Print.lid x print_prefix prefix_src';
*)
      add_prefix_lid prefix_src' x

let move_path assoc (prefix_dst, env) c =
  match assoc env c with
  | None -> c
  | Some prefix_src ->
      let _, prefix_src', _ = List.decomp_common_prefix prefix_src prefix_dst in
      add_prefix_path prefix_src' c

let move_tconstr = move_path assoc_tconstr
let move_constr = move_path assoc_constr

let move_to : prefix -> env -> term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun ((prefix, env) as pe) desc ->
      match desc with
      | Var x -> Var (move_lid pe @@ Lid.map ~f:(Id.map_typ (tr.typ pe)) x)
      | Local ((Decl_let [ (m, ({ desc = Module _ } as t1)) ] as decl), t2) ->
          let prefix' = prefix @ [ `Id (Id.set_typ m ()) ] in
          let env' = add_to_env prefix decl env in
          let t1' = tr.term_rec (prefix', env) t1 in
          let t2' = tr.term_rec (prefix, env') t2 in
          Local (Decl_let [ (m, t1') ], t2')
      | Local (decl, _) ->
          let env' = add_to_env prefix decl env in
          tr.desc_rec (prefix, env') desc
      | Module decls -> Module (trans_decls_as_term (tr.term pe) decls)
      | Constr (poly, c, ts) ->
          let c' = move_constr pe c in
          tr.desc_rec pe @@ Constr (poly, c', ts)
      | _ -> tr.desc_rec pe desc);
  tr.pat <-
    (fun pe p ->
      match p.pat_desc with
      | PConstr (poly, c, ps) ->
          let c' = move_constr pe c in
          tr.pat_rec pe @@ set_pat_desc p @@ PConstr (poly, c', ps)
      | _ -> tr.pat_rec pe p);
  tr.typ <-
    (fun pe ty ->
      match ty with
      | TConstr (c, tys) ->
          let c' = move_tconstr pe c in
          tr.typ_rec pe @@ TConstr (c', tys)
      | _ -> tr.typ_rec pe ty);
  Fun.curry tr.term

let get_fv_in_functors =
  let col = Col.make [] ( @@@ ) in
  col.desc <-
    (function Fun (_, t) when is_module t -> get_fv t @@@ col.term t | desc -> col.desc_rec desc);
  col.term

(* TODO: reanem constructors & type constructors *)
let rename_shadowed : term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun ((used, bv) as arg) desc ->
      match desc with
      | Local (Decl_let defs, t) ->
          let bv' = List.map fst defs in
          let must_rename = bv' |> Id.List.Set.inter bv |> Id.List.Set.inter used |> List.unique in
          let map =
            bv'
            |> List.filter (Id.List.mem -$- must_rename)
               (* the types of [must_rename] may be different from [bv'] *)
            |> List.map (Pair.add_right Id.new_var_id)
          in
          let bv'' = bv' @@@ bv in
          let defs' =
            Fmap.(list (pair (Id.List.subst map) (tr.term (used, bv'') -| subst_var_map map))) defs
          in
          let t' = tr.term (used, bv'') t in
          Local (Decl_let defs', t')
      | Module decls -> Module (trans_decls_as_term (tr.term arg) decls)
      | _ -> tr.desc_rec arg desc);
  tr.term <- set_afv_shallowly --| tr.term_rec;
  fun t -> tr.term (get_fv_in_functors t, []) t

let alpha_rename_functor_arg : term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun bv desc ->
      match desc with
      | Fun (x, t) when is_mod_var x && not (Id.List.mem x !bv) ->
          bv := x :: !bv;
          Fun (x, tr.term bv t)
      | Fun (x, t) when is_mod_var x && Id.List.mem x !bv ->
          let map, x' =
            if Id.List.mem x !bv then
              let x' = gen_fresh_name_var_int !bv x in
              ([ (x, x') ], x')
            else ([], x)
          in
          let path_map =
            let aux = Id.set_typ -$- () in
            let map = List.map (Pair.map aux (Type._LId -| aux)) map in
            Id.List.assoc_opt -$- map
          in
          let sbst = subst_var_map map -| Trans.map_typ (subst_path_head_map path_map) in
          bv := x' :: !bv;
          let t' = tr.term bv @@ sbst t in
          Fun (x', t')
      | Module decls -> decls |> trans_decls_as_term (tr.term bv) |> _Module
      | _ -> tr.desc_rec bv desc);
  fun t -> tr.term (ref []) t

let subst_functors_in_types : (path * path) list -> term -> term =
  let tr = Tr2.make () in
  tr.typ <- subst_path_prefix_map;
  tr.term

let make_sbst m f ts =
  let map =
    match List.map ValE._Var ts with
    | exception Invalid_argument _ -> assert false (* Check normalize_* if this occurs *)
    | xs ->
        let prefix = List.fold_left Type._LApp (path_of_lid f) (List.map path_of_lid xs) in
        let m = Type.LId (tconstr_of_id m) in
        [ (prefix, m) ]
  in
  subst_functors_in_types map

let inline_functor_app (prefix, env) f ts typ =
  match assoc_var env f with
  | None -> Term.rand typ
  | Some (_, _, { desc = Local (Decl_let defs, t) }) when is_rand_unit t ->
      (* The binding would be introduced by Module.abst_first_class_module *)
      Term.(local (Decl_let defs) (rand typ))
  | Some (_, env_f, t) ->
      let ms, t1 = decomp_funs t in
      if List.length ms <> List.length ts then unsupported "Partial application of functor";
      let env_f' =
        env_f
        |> map_env
             (List.filter (function
               | _, _, Decl_let [ (m', _) ] when List.exists (Id.( = ) m') ms -> false
               | _ -> true))
      in
      let decls =
        Dbg.printf "prefix: %a@." pp_prefix prefix;
        Dbg.printf "env_f': %a@." print_env env_f';
        t1
        |@> Dbg.printf "def of %a: %a@." Print.lid f Print.term
        |> move_to prefix env_f'
        |@> Dbg.printf "move to %a: %a@." print_prefix prefix Print.term
        |> ValE._Module
      in
      let bv =
        List.rev_flatten_map (function Decl_let defs -> List.map fst defs | _ -> []) decls
      in
      let decls_arg =
        ts
        |> List.L.map2 ms ~f:(fun x t ->
               match t.desc with
               | Var (LId y) when Id.(x = y) ->
                   let z = gen_fresh_name_var bv x in
                   [ Decl_let [ (z, Term.var y) ]; Decl_let [ (x, Term.var z) ] ]
               | _ -> [ Decl_let [ (x, t) ] ])
        |> List.flatten
      in
      Term.module_ ~typ (decls_arg @ decls)
(* Add decls_arg to the signature *)

let inline_term =
  let tr = Tr2.make () in
  tr.term <-
    (fun ((prefix, env) as pe) t ->
      match t.desc with
      | Local (Decl_let [ (m, ({ desc = App ({ desc = Var f }, ts) } as t1)) ], t2)
        when is_mod_var m ->
          let ts = List.map (tr.term pe) ts in
          let sbst = make_sbst m f ts in
          let t1' = inline_functor_app pe f ts @@ tr.typ pe t1.typ in
          let m = Id.set_typ m t1.typ in
          (* TODO: need? *)
          let decl = Decl_let [ (m, t1') ] in
          let env' = add_to_env prefix decl env in
          let t2' = sbst @@ tr.term (prefix, env') t2 in
          Term.local decl t2'
      | App ({ desc = Var f }, ts) when is_mod_typ t.typ -> inline_functor_app pe f ts t.typ
      | Local (Decl_let [ (m, ({ desc = Module _ } as t1)) ], t2) ->
          Dbg.printf "m: %a@." Print.id m;
          Dbg.printf "t1: %a@.@." Print.term t1;
          let prefix' = prefix @ [ `Id (Id.set_typ m ()) ] in
          let t1' = tr.term (prefix', env) t1 in
          let env' = add_to_env prefix (Decl_let [ (m, t1') ]) env in
          let t2' = tr.term (prefix, env') t2 in
          Term.local (Decl_let [ (m, t1') ]) t2'
      | Local (decl, _) when is_recursive_module_decl decl ->
          Format.eprintf "decl: %a@." Print.decls [ decl ];
          unsupported "Recursive modules"
      | Local (decl, t1) ->
          let decl' = tr.decl pe decl in
          let env' = add_to_env prefix decl' env in
          let t1' = tr.term (prefix, env') t1 in
          Term.local decl' t1'
      | Module decls ->
          let typ = tr.typ pe t.typ in
          Term.module_ ~typ (trans_decls_as_term (tr.term pe) decls)
      | _ -> set_afv_shallowly @@ tr.term_rec pe t);
  tr.typ <-
    (fun pe ty ->
      match ty with
      | TConstr (path, _) when Path.has_app path -> Ty.unknown (* WORKAROUND: Support Tmty_with *)
      | _ -> tr.typ_rec pe ty);
  (* Subsitutions in types are performed by subst_functors_in_types *)
  let pr s t = Dbg.printf "##[Functor] %s:@.  @[%a@.@." s Print.term t in
  fun ext_mod_typ t ->
    t
    |@> pr "INPUT"
    |> normalize_include
    |@> pr "normalize_include"
    |> normalize_arg_module
    |@> pr "normalize_arg_module"
    |> alpha_rename_functor_arg
    |@> pr "alpha_rename_functor_arg"
    |> rename_shadowed
    |@> pr "rename_shadowed"
    |> tr.term ([], Env [])
    |@> pr "tr.term ([], Env [])"
    |> remove ext_mod_typ
    |@> pr "remove ext_mod_typ"
    |> Trans.elim_unused_let ~leave_last:true
    |@> pr "Trans.elim_unused_let ~leave_last:true"

let pp_tconstr = Id.print

type typ_term = Typ of (params * typ) * tenv [@printer fun fm ((_, ty), _) -> Print.typ fm ty]

(* TODO: Extensible types? *)
and sgn = (tconstr * typ_term) list
and tenv = (tconstr * (int * typ_term)) list [@@deriving show { with_path = false }]

let rec add_decl_to_env ~cnt ~(env : tenv) decl : tenv =
  match decl with
  | Sig_value x -> add_val_to_env ~cnt x (Id.typ x) ~env
  | Sig_type decls ->
      List.L.fold_left decls ~init:env ~f:(fun env (c, (params, ty)) ->
          add_to_env ~cnt c (Typ ((params, ty), env)) ~env)
  | Sig_ext _ -> env

and add_to_env : type a. cnt:int ref -> a Id.t -> typ_term -> env:tenv -> tenv =
 fun ~cnt c t ~(env : tenv) : tenv ->
  incr cnt;
  (Id.set_typ c (), (!cnt, t)) :: env

and add_val_to_env : type a. cnt:int ref -> a Id.t -> typ -> env:tenv -> tenv =
 fun ~cnt x ty ~(env : tenv) : tenv ->
  if is_module_or_functor_typ ty then add_to_env ~cnt ~env (Id.set_typ x ()) (Typ (([], ty), env))
  else env

and add_term_to_env ~cnt c t ~(env : tenv) : tenv =
  incr cnt;
  (c, (!cnt, t)) :: env

let assoc ~cnt (s : string) (Typ ((params, ty), env)) : typ_term =
  assert (params = []);
  match ty with
  | TModSig sgn ->
      List.L.fold_left sgn ~init:(env, None) ~f:(fun (env, r) item ->
          let r' =
            match item with
            | Sig_value x -> if Id.name x = s then Some (Typ (([], Id.typ x), env)) else r
            | Sig_type decls ->
                List.L.fold_left decls ~init:(env, r) ~f:(fun (env, r) (c, (params, ty)) ->
                    let t = Typ ((params, ty), env) in
                    let env' = add_to_env ~cnt c t ~env in
                    let r' = if Id.name c = s then Some t else r in
                    (env', r'))
                |> snd
            | Sig_ext _ -> r
          in
          let env' = add_decl_to_env ~cnt ~env item in
          (env', r'))
      |> snd
      |> Option.get
  | _ -> [%invalid_arg]

let is_free ~env path =
  not (List.for_all (Id.List.mem_assoc -$- env) (Path.heads path) || is_prim_constr path)

let col_free_paths ~(env : tenv) (Typ ((_, ty), _)) : path list =
  make_reduce ty ~app:( @@@ ) ~default:[] ~f:(fun col ty ->
      match ty with
      | TConstr (c, tys) -> Some (c :: List.rev_flatten_map col tys)
      | TModSig _ -> Some []
      | TFun (x, ty') -> Some (List.filter_out (Path.eq (LId (Id.set_typ x ()))) @@ col ty')
      | _ -> None)
  |> List.sort_unique Path.compare
  |> List.filter (is_free ~env)

let typ_of_term (Typ ((params, ty), _)) : params * typ = (params, ty)

let rec reduce_path ~(env : tenv) ~cnt (path : path) : typ_term =
  match path with
  | LId x -> reduce_typ_term ~env ~cnt @@ snd @@ Id.List.assoc x env
  | LDot (path', s) -> reduce_typ_term ~cnt ~env @@ assoc ~cnt s @@ reduce_path ~env ~cnt path'
  | LApp (path1, path2) -> (
      let mt1 = reduce_path ~env ~cnt path1 in
      let mt2 = reduce_path ~env ~cnt path2 in
      match mt1 with
      | Typ (([], TFun (x, ty)), env1) ->
          let env' = add_to_env ~cnt (Id.set_typ x ()) mt2 ~env:env1 in
          reduce_typ_term ~env:env' ~cnt (Typ (([], ty), env1))
      | _ -> assert false)

and reduce_typ_term ~(env : tenv) ~cnt (t : typ_term) : typ_term =
  let (Typ ((params, ty), env')) = t in
  let env'' = List.Set.diff ~eq:(Eq.on (snd |- fst)) env' env in
  if env'' = [] then t
  else
    let map =
      t |> col_free_paths ~env |> List.map (Pair.add_right (reduce_path ~env ~cnt |- typ_of_term))
    in
    Typ ((params, inline_constr_map map ty), env')

let rec inline_typ ~env ~cnt (ty : typ) : typ =
  make_trans2
    (fun tr env ty ->
      match ty with
      | TModSig sgn -> Some (TModSig (inline_typ_sgn ~env ~cnt sgn))
      | TConstr (c, tys) when is_free ~env c && Path.has_app c -> (
          match reduce_path ~env ~cnt c with
          | exception Not_found -> None
          | t ->
              let tys' = List.map (tr env) tys in
              let pty = typ_of_term t in
              Some (apply pty tys'))
      | _ -> None)
    env ty

and inline_typ_sgn ~env ~cnt (sig_elems : term signature) : term signature =
  List.L.fold_left_map sig_elems ~init:env ~f:(fun env decl ->
      match decl with
      | Sig_value x ->
          let env' = add_val_to_env ~cnt x (Id.typ x) ~env in
          let x' = Id.map_typ (inline_typ ~env ~cnt) x in
          (env', Sig_value x')
      | Sig_type decls ->
          let env', decls' =
            List.L.fold_left_map decls ~init:env ~f:(fun env (c, (params, ty)) ->
                let t = Typ ((params, ty), env) in
                let env' = add_to_env ~cnt c t ~env in
                let ty' = inline_typ ~env:env' ~cnt ty in
                (env', (c, (params, ty'))))
          in
          (env', Sig_type decls')
      | Sig_ext _ -> (env, decl))
  |> snd

let (has_functor, has_functor_typ) : (term -> bool) * (typ -> bool) =
  let it = Iter.make () in
  it.term <-
    (fun t -> match t.desc with App _ when is_module t -> raise Found | _ -> it.term_rec t);
  it.typ <-
    (fun ty ->
      it.typ_rec ty;
      match ty with TFun (_, ty') when is_mod_typ ty' -> raise Found | _ -> ());
  (Exception.does_raise ~exn:Found it.term, Exception.does_raise ~exn:Found it.typ)

let inline_ext_mod_typ (ext_mod_typ : Problem.ext_mod_typ list) =
  let cnt = ref 0 in
  List.L.fold_left_map ext_mod_typ ~init:[] ~f:(fun env ((m : tconstr), ty) ->
      let ty' = inline_typ ~cnt ~env ty in
      (add_val_to_env m ty ~env ~cnt, (m, ty')))
  |> snd
  |> Fmap.(list (snd to_abst))

let inline (problem : Problem.t) : Problem.t option =
  let b1 = has_functor problem.term in
  let b2 = List.exists (snd |- has_functor_typ) problem.ext_mod_typ in
  if b1 || b2 then
    let term = (b1 ^> inline_term problem.ext_mod_typ) problem.term in
    let ext_mod_typ = (b2 ^> inline_ext_mod_typ) problem.ext_mod_typ in
    Some { problem with term; ext_mod_typ }
  else None
