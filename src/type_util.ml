open Util
open Type

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

module Pr = struct
  include Print_
  include Print_typ

  let typ = typ_init
  let tenv = Tenv.print_init
end

exception CannotUnify of (unit t * unit t) option

(** [remove_pred ty] removes [TAttr] in [ty] to convert ['a t] to [unit] *)
let rec remove_pred (ty : _ t) : unit t =
  let rm = remove_pred in
  let rm_row { row_constr; row_args; row_ret } =
    let row_args = List.map rm row_args in
    let row_ret = Option.map rm row_ret in
    { row_constr; row_args; row_ret }
  in
  let rm_ext_row { ext_row_path; ext_row_args; ext_row_ret } =
    let ext_row_args = List.map rm ext_row_args in
    let ext_row_ret = Option.map rm ext_row_ret in
    { ext_row_path; ext_row_args; ext_row_ret }
  in
  match ty with
  | TBase b -> TBase b
  | TVar (_, { contents = Some ty }, _) -> rm ty
  | TVar (b, _, id) -> TVar (b, ref None, id)
  | TFun (x, ty) -> TFun (Id.map_typ rm x, rm ty)
  | TConstr (c, tys) -> TConstr (c, List.map rm tys)
  | TTuple xs -> TTuple (List.map (Id.map_typ rm) xs)
  | TAttr (_, ty) -> rm ty
  | TFuns (xs, ty) -> TFuns (List.map (Id.map_typ rm) xs, rm ty)
  | TVariant (poly, rows) -> TVariant (poly, List.map rm_row rows)
  | TRecord fields -> TRecord (Fmap.(list (snd (snd rm))) fields)
  | TModSig sgn ->
      let sgn =
        sgn
        |> List.map (function
             | Sig_type decl -> Sig_type (Fmap.(list (snd (list rm * rm))) decl)
             | Sig_value x -> Sig_value (Id.map_typ rm x)
             | Sig_ext ext -> Sig_ext (Fmap.(snd (list rm * rm_ext_row)) ext))
      in
      TModSig sgn
  | TModLid m -> TModLid m
  | TPackage ty -> TPackage (rm ty)
  | TPoly (vars, ty) ->
      let rm_ref f { contents } = { contents = f contents } in
      TPoly (Fmap.(list (rm_ref (option rm))) vars, rm ty)
  | TConstraint (ty, cs) -> TConstraint (rm ty, Fmap.(list (rm * rm)) cs)
  | TOpen -> TOpen

(*
let tconstr_of_path (lid:path) : tconstr = Path.id_of lid
 *)

(** [subst_tconstr_aux params (params',ty)] returns [ty] with substituting [params'] by [params] *)
let subst_tconstr_params params pty =
  let _, (params', ty) = copy_tconstr_params pty in
  List.iter2 instantiate params' params;
  ty

(** [apply (params,ty) args] returs [ty] with replacing [rapams] with [args].
    Here, [([x1;x2;...;xn],ty)] can be regarded as the type abstraction Λx1.Λx2.....Λxn.ty *)
let apply pty args = subst_tconstr_params args pty

let inline_constr_map (map : (path * ('a params * 'a t)) list) : 'a t -> 'a t =
  make_trans (fun f ty ->
      match ty with
      | TConstr (c, tys) ->
          List.assoc_opt ~eq:Path.eq c map |> Option.map (subst_tconstr_params (List.map f tys))
      | _ -> None)

let inline_tconstr_map map ty = inline_constr_map (Fmap.(list (fst _LId)) map) ty
let label_pred_share = "pred_share" (* for TAId *)
let typ_unknown = TConstr (C.unknown, [])
let typ_abst = TConstr (C.abst, [])
let typ_exn = TConstr (C.exn, [])
let typ_string = TConstr (C.string, [])
let typ_bytes = TConstr (C.bytes, [])
let typ_result = TConstr (C.result, [])
let typ_char = TConstr (C.char, [])
let typ_float = TConstr (C.float, [])
let typ_class = TConstr (C.class_, []) (* abstracted type of classes *)
let is_class ty = ty = typ_class

let rec var_name_of typ =
  match typ with
  | TBase TUnit -> "u"
  | TBase TBool -> "b"
  | TBase TInt -> "n"
  | TFun _ -> "f"
  | TTuple _ -> "p"
  | TConstr (c, _) when c = C.list -> "xs"
  | TAttr (_, ty) -> var_name_of ty
  | _ -> "x"

let add_prefix_constr = Id.add_name_before

let new_var ?name typ =
  let name = match name with None -> var_name_of typ | Some name -> name in
  Id.new_var ~name typ

let pureTFun (x, typ) = TAttr ([ TAPureFun ], TFun (x, typ))
let safeTFun (x, typ) = TAttr ([ TASafeFun ], TFun (x, typ))
let raiseTFun (exn, x, typ) = TAttr ([ TARaise exn ], TFun (x, typ))
let make_tfun ?name typ1 typ2 = TFun (new_var ?name typ1, typ2)
let make_ptfun ?name typ1 typ2 = TAttr ([ TAPureFun ], make_tfun ?name typ1 typ2)
let make_stfun ?name typ1 typ2 = TAttr ([ TASafeFun ], make_tfun ?name typ1 typ2)
let make_tfun_raise ?name typ1 ~typ_exn typ2 = TAttr ([ TARaise typ_exn ], make_tfun ?name typ1 typ2)
let make_ttuple typs = TTuple (List.map new_var typs)
let make_tpair typ1 typ2 = make_ttuple [ typ1; typ2 ]
let make_tlist typ = TConstr (C.list, [ typ ])
let make_tset typ = TConstr (C.set, [ typ ])
let make_tref typ = TConstr (C.ref, [ typ ])
let make_toption typ = TConstr (C.option, [ typ ])
let make_tarray typ = TConstr (C.array, [ typ ])
let make_tlazy typ = TConstr (C.lazy_, [ typ ])
let is_ref_typ ty = match elim_tattr ty with TConstr (c, [ _ ]) -> C.is_ref c | _ -> false
let is_base_prim c = List.mem ~eq:Path.eq c C.base_prims
let is_prim_constr c = List.mem ~eq:Path.eq c C.prims

let is_fun_typ typ =
  match elim_tattr typ with TFun (_, _) -> true | TFuns (_, _) -> true | _ -> false

let rec is_base_typ = function
  | TBase _ -> true
  | TConstr (c, _) when c = C.string -> true
  | TAttr (_, typ) -> is_base_typ typ
  | _ -> false

let is_tuple_typ ty = match elim_tattr ty with TTuple _ -> true | _ -> false
let tfuns_to_tfun = function TFuns (xs, typ) -> List.fold_right _TFun xs typ | typ -> typ

let elim_tattr_all ty =
  make_trans (fun tr ty -> match ty with TAttr (_, typ) -> Some (tr typ) | _ -> None) ty

let decomp_base ty = match elim_tattr ty with TBase b -> Some b | _ -> None

let rec decomp_tfun typ =
  match elim_tattr typ with
  | TFun (x, typ) ->
      let xs, typ = decomp_tfun typ in
      (x :: xs, typ)
  | _ -> ([], typ)

let decomp_tfuns = function TFuns (xs, typ) -> (xs, typ) | _ -> invalid_arg "decomp_tfuns"
let arity typ = List.length @@ fst @@ decomp_tfun typ
let decomp_module s = List.decomp_snoc @@ String.split_on_char '.' s
let base = snd -| decomp_module

let decomp_effect = function
  | TAttr (attrs, typ) -> (
      let attrs1, attrs2 = List.partition (function TAEffect _ -> true | _ -> false) attrs in
      let typ' = if attrs2 = [] then typ else TAttr (attrs2, typ) in
      match attrs1 with
      | [] -> None
      | [ TAEffect e ] -> Some (e, typ')
      | _ -> invalid_arg "decomp_effect")
  | _ -> None

let decomp_raise_tfun ty =
  match ty with
  | TAttr (attrs, TFun (x, ty2)) ->
      List.find_map_opt (function TARaise exn -> Some exn | _ -> None) attrs
      |> Option.map (fun exn -> (exn, x, ty2))
  | _ -> None

let is_raise_tfun ty = Option.is_some (decomp_raise_tfun ty)

let rec flatten typ =
  match typ with TVar (_, { contents = Some typ' }, _) -> flatten typ' | _ -> typ

let occurs =
  let aux r _ ty =
    match ty with TVar (_, ({ contents = None } as r'), _) -> r == r' | _ -> false
  in
  fun r ty -> ty |> make_find (aux r) |> Option.is_some

let tconstr_occurs =
  let aux s _ ty = match ty with TConstr (LId s', _) -> Id.(s = s') | _ -> false in
  fun s ty -> ty |> make_find (aux s) |> Option.is_some

let has_tvar ty =
  make_find (fun _ ty -> match ty with TVar (_, r, _) when !r = None -> true | _ -> false) ty
  |> Option.is_some

let rec unify ?(for_check = false) ?(env : _ Tenv.t = !!Tenv.init) ?(sub = false)
    ?((* [unify ~sub:true ty1 ty2] succeeds if [ty1] is a subtype of [ty2] *)
      only_weak = false) ?(acc = ref [])
    ?((* WORKAROUND: ignore the unification error for types without type variables if this is true *)
      ignore_non_poly_fail = false) (typ1 : 'a t) (typ2 : 'a t) =
  (*
  try
*)
  let uni ?(env = env) = unify ~env ~for_check ~sub ~only_weak ~acc ~ignore_non_poly_fail in
  let print_error f =
    if for_check then Format.ifprintf Format.std_formatter f else Format.eprintf f
  in
  let cannot_unify () =
    if ignore_non_poly_fail && not (has_tvar typ1 || has_tvar typ2) then ()
    else (
      print_error "@[<hov 4>unification error: ~sub:%b@ @[<hv>@[%a@],@ @[%a@]@]@\n" sub Pr.typ typ1
        Pr.typ typ2;
      print_error "env: %a@\n" Pr.tenv env;
      let arg = if !!Dbg.check then Some (remove_pred typ1, remove_pred typ2) else None in
      raise (CannotUnify arg))
  in
  let check_bool b = if not b then cannot_unify () in
  let check_eq x y = check_bool (x = y) in
  let _check_eq_on f x y = check_bool (f x = f y) in
  let check_len_eq x y = check_bool (List.compare_lengths x y = 0) in
  let unify_poly_variant tys1 tys2 =
    let decomp_tuple tys = match tys with [ TTuple xs ] -> List.map Id.typ xs | _ -> tys in
    let tys1, tys2 =
      match (decomp_tuple tys1, decomp_tuple tys2) with
      | [ (TVar _ as ty) ], _ :: _ :: _ ->
          let tys = List.map (fun _ -> !!new_tvar) tys2 in
          uni ty (make_ttuple tys);
          List.iter2 uni tys tys2;
          (tys, tys2)
      | _ :: _ :: _, [ (TVar _ as ty) ] ->
          let tys = List.map (fun _ -> !!new_tvar) tys1 in
          uni ty (make_ttuple tys);
          List.iter2 uni tys1 tys;
          (tys1, tys)
      | tys1, tys2 ->
          check_len_eq tys1 tys2;
          (tys1, tys2)
    in
    List.iter2 uni tys1 tys2
  in
  match (typ1, typ2) with
  | TVar (_, r1, _), TVar (_, r2, _) when r1 == r2 -> ()
  | TVar (_, { contents = Some typ1 }, _), _ -> uni typ1 typ2
  | _, TVar (_, { contents = Some typ2 }, _) -> uni typ1 typ2
  | TAttr (_, typ1), _ -> uni typ1 typ2
  | _, TAttr (_, typ2) -> uni typ1 typ2
  | (TVar (false, _, _), _ | _, TVar (false, _, _)) when only_weak -> ()
  | (TVar (_, r, _), typ | typ, TVar (_, r, _)) when occurs r typ ->
      print_error "occur-check failure: %a, %a@." Pr.typ (flatten typ1) Pr.typ (flatten typ2);
      cannot_unify ()
  | TVar (weak, r, n), typ | typ, TVar (weak, r, n) ->
      Dbg.printf "UNIFY %a := %a@." (Pr.tvar ~weak) n Pr.typ typ;
      r := Some typ
  | TBase b1, TBase b2 -> check_eq b1 b2
  | TFun (x1, typ1), TFun (x2, typ2) ->
      uni (Id.typ x2) (Id.typ x1);
      uni typ1 typ2
  | ty1, ty2 when ty1 = typ_unknown || ty2 = typ_unknown -> ()
  | TConstr (c1, typs1), TConstr (c2, typs2)
    when Path.to_string c1 = Path.to_string c2 (* WORKAROUND *)
         || (List.mem (c1, c2) !acc || List.mem (c2, c1) !acc)
            && List.compare_lengths typs1 typs2 = 0 (* BUGGY? *) ->
      check_len_eq typs1 typs2;
      List.iter2 uni typs1 typs2
  | TConstr (c, []), _ when C.is_exn c ->
      uni (snd @@ Tenv.assoc_exn env) typ2 (* TODO: Use discarded environment *)
  | _, TConstr (c, []) when C.is_exn c ->
      uni typ1 (snd @@ Tenv.assoc_exn env) (* TODO: Use discarded environment *)
  | TConstr (s, tys), _ when Tenv.mem_assoc_type s env ->
      let tys', typ1' = Tenv.assoc_type s env in
      check_len_eq tys tys';
      (match typ2 with TConstr (s', _) -> acc := (s, s') :: !acc | _ -> ());
      List.iter2 uni tys tys';
      uni typ1' typ2
  | _, TConstr (s, tys) when Tenv.mem_assoc_type s env ->
      let tys', typ2' = Tenv.assoc_type s env in
      (match typ1 with TConstr (s', _) -> acc := (s, s') :: !acc | _ -> ());
      check_len_eq tys tys';
      List.iter2 uni tys tys';
      uni typ1 typ2'
  | TTuple xs1, TTuple xs2 ->
      check_len_eq xs1 xs2;
      List.iter2 (fun x1 x2 -> uni (Id.typ x1) (Id.typ x2)) xs1 xs2
  | TVariant (VPoly { closed = true; _ }, rows1), TVariant (VPoly { closed = true; _ }, rows2)
    when sub ->
      (* TODO *)
      check_bool (List.length rows1 <= List.length rows2);
      let check row1 =
        match assoc_row row1.row_constr rows2 with
        | row2 -> unify_poly_variant row1.row_args row2.row_args
        | exception Not_found ->
            print_error "Not_found %a in %a@." Id.print row1.row_constr Pr.typ typ2;
            cannot_unify ()
      in
      List.iter check rows1
  | TVariant (VPoly { closed = false; _ }, rows1), TVariant (VPoly { closed = false; _ }, rows2)
    when sub ->
      check_bool (List.length rows1 >= List.length rows2);
      let check row2 =
        match assoc_row row2.row_constr rows1 with
        | row1 -> unify_poly_variant row1.row_args row2.row_args
        | exception Not_found ->
            print_error "Not_found %a in %a@." Id.print row2.row_constr Pr.typ typ2;
            cannot_unify ()
      in
      List.iter check rows2
  | TVariant (VNonPoly, rows1), TVariant (VNonPoly, rows2) ->
      check_len_eq rows1 rows2;
      let check row1 row2 =
        check_eq row1.row_constr row2.row_constr;
        check_len_eq row1.row_args row2.row_args;
        List.iter2 uni row1.row_args row2.row_args
      in
      let sort = List.sort (Compare.on row_constr) in
      List.iter2 check (sort rows1) (sort rows2)
  | TVariant (VPoly _, rows1), TVariant (VPoly _, rows2) ->
      check_len_eq rows1 rows2;
      let check row1 row2 =
        check_eq row1.row_constr row2.row_constr;
        unify_poly_variant row1.row_args row2.row_args
      in
      let sort = List.sort (Compare.on row_constr) in
      List.iter2 check (sort rows1) (sort rows2)
  | TRecord fields1, TRecord fields2 ->
      check_len_eq fields1 fields2;
      let check (s1, (f1, typ1)) (s2, (f2, typ2)) =
        check_eq s1 s2;
        check_eq f1 f2;
        uni typ1 typ2
      in
      List.iter2 check fields1 fields2
  | TModLid x, TModLid y -> check_bool Path.(x = y)
  | TModLid _m, TModSig _sgn -> [%unsupported]
  | TModSig _sgn, TModLid _m -> [%unsupported]
  | TModSig sgn1, TModSig sgn2 when !Flag.Debug.check_tmodule && sub ->
      check_bool (List.length sgn1 >= List.length sgn2);
      sgn2
      |> List.iter (function
           | Sig_type decls ->
               decls
               |> List.iter (fun (s2, (_, ty2)) ->
                      match
                        List.find_map
                          (function
                            | Sig_type decl ->
                                List.find_map_opt
                                  (fun (s2', (_, ty)) -> if Id.(s2 = s2') then Some ty else None)
                                  decl
                            | _ -> None)
                          sgn1
                      with
                      | ty1 -> uni ty1 ty2
                      | exception Not_found ->
                          print_error "Not_found %a in %a@." Pr.constr s2 Pr.typ typ2;
                          cannot_unify ())
           | Sig_value y -> (
               match
                 List.find_map (function Sig_value x when Id.(x = y) -> Some x | _ -> None) sgn1
               with
               | x -> uni (Id.typ x) (Id.typ y)
               | exception Not_found ->
                   print_error "Not_found %a in %a@." Id.print y Pr.typ typ1;
                   cannot_unify ())
           | Sig_ext _ -> ())
  | TModSig _sgn1, TModSig _sgn2 when !Flag.Debug.check_tmodule -> [%unsupported]
  (*
      check_len_eq sgn1.sig_types sgn2.sig_types;
      let env =
        List.L.fold_left2 sgn1.sig_types sgn2.sig_types ~init:env ~f:(fun env decls1 decls2 ->
            check_len_eq decls1 decls2;
            List.L.iter2 decls1 decls2 ~f:(fun (s1, (params1, ty1)) (s2, (params2, ty2)) ->
                check_eq s1 s2;
                uni ~env ty1 ty2;
                List.iter2 instantiate params1 params2);
            List.fold_left
              (fun env (s1, (params1, ty1)) -> Tenv.add_typ s1 (params1, ty1) env)
              env decls1)
      in
      check_len_eq sgn1.sig_values sgn2.sig_values;
      let sort = List.sort Id.compare in
      let unify_val x y = uni ~env (Id.typ x) (Id.typ y) in
      List.iter2 unify_val (sort sgn1.sig_values) (sort sgn2.sig_values)
  *)
  | TModSig _, TModSig _ when not !Flag.Debug.check_tmodule -> ()
  | TModSig _, TConstr _ | TConstr _, TModSig _ -> () (* TODO??? *)
  | (TConstr (c, _), _ | _, TConstr (c, _)) when Path.has_app c -> () (* TODO *)
  | TPackage ty1, TPackage ty2 -> uni ty1 ty2
  | TPoly (params1, ty1), TPoly (params2, ty2) when sub ->
      let env = List.combine params1 params2 in
      if Type.equal ~env ty1 ty2 then () else [%unsupported]
  | TPoly (params1, ty1), TPoly (params2, ty2) ->
      let env = List.combine params1 params2 in
      check_bool (Type.equal ~env ty1 ty2)
  | TPoly (_, ty1), _ when sub -> uni (snd @@ copy_tvar_typ ty1) typ2
  | TConstraint (ty, cs), ty2 ->
      List.iter (Fun.uncurry uni) cs;
      uni ty ty2
  | ty1, TConstraint (ty, cs) ->
      List.iter (Fun.uncurry uni) cs;
      uni ty1 ty
  | _, _ ->
      let ty1 = Tenv.normalize_type env typ1 in
      let ty2 = Tenv.normalize_type env typ2 in
      if Type.eq ty1 typ1 && Type.eq ty2 typ2 then cannot_unify () else uni ty1 ty2
(*
  with CannotUnify _ as e when !!Dbg.check ->
    Format.eprintf "unify typ1: %a@." Print_typ.typ_init typ1;
    Format.eprintf "unify typ2: %a@.@." Print_typ.typ_init typ2;
    raise e
 *)

let rec eq_decl ?(eq = eq) (c1, pty1) (c2, pty2) =
  Id.(c1 = c2)
  &&
  let _, (p1, ty1) = copy_tconstr_params pty1 in
  let _, (p2, ty2) = copy_tconstr_params pty2 in
  List.iter2 unify p1 p2;
  eq ty1 ty2

and eq ty1 ty2 =
  let eq_id = Compare.eq_on Id.typ ~eq in
  match (ty1, ty2) with
  | TBase b1, TBase b2 -> b1 = b2
  | TVar (_, x, _), TVar (_, y, _) -> x == y
  | TFun (x, ty1), TFun (y, ty2) -> eq_id x y && eq ty1 ty2
  | TFuns _, TFuns _ -> assert false
  | TTuple tys1, TTuple tys2 -> List.eq ~eq:eq_id tys1 tys2
  | TVariant (b1, rows1), TVariant (b2, rows2) ->
      let eq_row row1 row2 =
        Id.eq row1.row_constr row2.row_constr
        && List.eq ~eq row1.row_args row2.row_args
        && Option.eq ~eq row1.row_ret row2.row_ret
      in
      b1 = b2 && List.eq ~eq:eq_row rows1 rows2
  | TRecord fields1, TRecord fields2 ->
      List.eq ~eq:(Pair.eq ( = ) (Pair.eq ( = ) eq)) fields1 fields2
  | TConstr (c1, typs1), TConstr (c2, typs2) -> c1 = c2 && List.eq ~eq typs1 typs2
  | TAttr (attr1, ty1), TAttr (attr2, ty2) -> attr1 = attr2 && ty1 = ty2
  | TModSig sgn1, TModSig sgn2 ->
      let eq_elem x y =
        match (x, y) with
        | Sig_type decl1, Sig_type decl2 -> List.equal eq_decl decl1 decl2
        | Sig_value x, Sig_value y -> Id.(x = y)
        | Sig_ext (p1, _), Sig_ext (p2, _) ->
            (* BUGGY: must compare arguments *)
            Path.(p1 = p2)
        | _ -> false
      in
      List.equal eq_elem sgn1 sgn2
  | TModLid m1, TModLid m2 -> Path.(m1 = m2)
  | _ -> false

let rec is_instance_of ?(strict = false) ty1 ty2 =
  let eq = is_instance_of ~strict in
  let eq_id = Compare.eq_on Id.typ ~eq in
  match (elim_tattr ty1, elim_tattr ty2) with
  | TVar (_, { contents = None }, _), TVar (_, { contents = None }, _) -> not strict
  | TVar (_, { contents = Some ty1 }, _), TVar (_, { contents = None }, _) -> eq ty1 ty2
  | TBase b1, TBase b2 -> b1 = b2
  | TVar (_, x, _), TVar (_, y, _) -> x == y
  | TFun (x, ty1), TFun (y, ty2) -> eq_id x y && eq ty1 ty2
  | TFuns _, TFuns _ -> assert false
  | TTuple xs1, TTuple xs2 -> List.eq ~eq:eq_id xs1 xs2
  | TVariant (b1, rows1), TVariant (b2, rows2) ->
      let eq_row row1 row2 =
        Id.eq row1.row_constr row2.row_constr
        && List.eq ~eq row1.row_args row2.row_args
        && Option.eq ~eq row1.row_ret row2.row_ret
      in
      b1 = b2 && List.eq ~eq:eq_row rows1 rows2
  | TRecord fields1, TRecord fields2 ->
      List.eq ~eq:(Pair.eq ( = ) (Pair.eq ( = ) eq)) fields1 fields2
  | TConstr (c1, typs1), TConstr (c2, typs2) -> c1 = c2 && List.eq ~eq typs1 typs2
  | TModSig sgn1, TModSig sgn2 ->
      let eq_elem x y =
        match (x, y) with
        | Sig_type decl1, Sig_type decl2 -> List.equal (eq_decl ~eq) decl1 decl2
        | Sig_value x, Sig_value y -> Id.(x = y)
        | Sig_ext (p1, _), Sig_ext (p2, _) ->
            (* BUGGY: must compare arguments *)
            Path.(p1 = p2)
        | _ -> false
      in
      List.equal eq_elem sgn1 sgn2
  | TModLid m1, TModLid m2 -> Path.(m1 = m2)
  | _ -> false

let rec same_shape typ1 typ2 =
  let eq = same_shape in
  let eq_id = Compare.eq_on Id.typ ~eq:same_shape in
  match (elim_tattr typ1, elim_tattr typ2) with
  | TBase b1, TBase b2 -> b1 = b2
  | TVar (_, { contents = None }, _), TVar (_, { contents = None }, _) -> true
  | TVar (_, { contents = Some typ1 }, _), TVar (_, { contents = Some typ2 }, _) -> eq typ1 typ2
  | TFun (x1, typ1), TFun (x2, typ2) -> eq_id x1 x2 && eq typ1 typ2
  | TConstr (c1, typs1), TConstr (c2, typs2) -> c1 = c2 && List.for_all2 eq typs1 typs2
  | TTuple xs1, TTuple xs2 -> List.eq ~eq:eq_id xs1 xs2
  | TVariant (poly1, rows1), TVariant (poly2, rows2) ->
      let eq_row row1 row2 =
        Id.eq row1.row_constr row2.row_constr
        && List.eq ~eq row1.row_args row2.row_args
        && Option.eq ~eq row1.row_ret row2.row_ret
      in
      poly1 = poly2 && List.eq ~eq:eq_row rows1 rows2
  | TRecord fields1, TRecord fields2 ->
      List.eq ~eq:(Pair.eq ( = ) (Pair.eq ( = ) eq)) fields1 fields2
  | TModSig sgn1, TModSig sgn2 ->
      let eq_elem x y =
        match (x, y) with
        | Sig_type decl1, Sig_type decl2 -> List.equal (eq_decl ~eq) decl1 decl2
        | Sig_value x, Sig_value y -> Id.(x = y)
        | Sig_ext (p1, _), Sig_ext (p2, _) ->
            (* BUGGY: must compare arguments *)
            Path.(p1 = p2)
        | _ -> false
      in
      List.equal eq_elem sgn1 sgn2
  | TModLid m1, TModLid m2 -> Path.(m1 = m2)
  | _ -> false

let rec app_typ typ typs =
  match (typ, typs) with
  | TFun (_, typ2), _ :: typs' -> app_typ typ2 typs'
  | _, [] -> typ
  | _ -> assert false

let tuple_num typ = match elim_tattr typ with TTuple xs -> Some (List.length xs) | _ -> None

let proj_typ i typ =
  match elim_tattr typ with
  | TTuple xs -> Id.typ @@ List.nth xs i
  | typ when typ = typ_unknown -> typ_unknown
  | typ' -> invalid_arg "proj_typ %d (%a)" i Pr.typ_init typ'

let fst_typ typ = proj_typ 0 typ
let snd_typ typ = proj_typ 1 typ

let make_decomp c ty =
  match elim_tattr ty with
  | TConstr (c', [ typ ]) when c = c' -> typ
  | typ when typ = typ_unknown -> typ_unknown
  | _ -> invalid_arg "%s_typ" (Path.to_string c)

let ref_typ ty = make_decomp C.ref ty
let list_typ ty = make_decomp C.list ty
let option_typ ty = make_decomp C.option ty
let array_typ ty = make_decomp C.array ty
let set_typ ty = make_decomp C.set ty

let has_pred =
  let aux _ ty =
    match ty with
    | TAttr (attr, _) -> List.exists (function TAPred (_, _ :: _) -> true | _ -> false) attr
    | _ -> false
  in
  fun ty -> ty |> make_find aux |> Option.is_some

let has_tfun =
  let aux _ ty = match ty with TFun _ -> true | _ -> false in
  fun ty -> ty |> make_find aux |> Option.is_some

let string_of_constr (c : constr) = Id.to_string c
let string_of_tconstr (c : tconstr) = Id.to_string c
let string_of_path (c : path) = Path.to_string c
let string_of_label (l : label) = Id.to_string l
let constr_of_string s : constr = Id.make s ()
let tconstr_of_string s : tconstr = Id.make s ()
let label_of_string s : label = Id.make s ()
let lid_of_string s : path = LId (constr_of_string s)
let constr_of_path (c : path) = constr_of_string @@ Path.to_string c
let print_label = Id.print

let rec to_id_string = function
  | TBase TUnit -> "unit"
  | TBase TBool -> "bool"
  | TBase TInt -> "int"
  | TVar (_, { contents = None }, _) -> "x"
  | TVar (_, { contents = Some typ }, _) -> to_id_string typ
  | TFun (x, typ) -> to_id_string (Id.typ x) ^ "__" ^ to_id_string typ
  | TConstr (c, [ typ ]) -> to_id_string typ ^ "_" ^ string_of_path c
  | TTuple xs ->
      let xs', x = List.decomp_snoc xs in
      let aux x s = to_id_string (Id.typ x) ^ "_x_" ^ s in
      List.fold_right aux xs' @@ to_id_string @@ Id.typ x
  | TAttr (_, typ) -> to_id_string typ
  | TConstr (c, _) -> string_of_path c
  | TFuns _ -> [%unsupported]
  | TVariant (_, rows) ->
      rows |> List.take 2 |> List.map (row_constr |- string_of_constr) |> String.join "_"
  | TRecord fields -> String.join "_" @@ List.map (fst |- string_of_constr) fields
  | TModSig _ | TModLid _ -> "module"
  | TPackage _ -> "pack"
  | TPoly (_, ty) -> to_id_string ty
  | TConstraint (ty, _) -> to_id_string ty
  | TOpen -> "open"

let rec to_id_string_short = function
  | TBase TUnit -> "u"
  | TBase TBool -> "b"
  | TBase TInt -> "i"
  | TVar (_, { contents = None }, _) -> "x"
  | TVar (_, { contents = Some typ }, _) -> to_id_string_short typ
  | TFun (x, typ) -> to_id_string_short (Id.typ x) ^ to_id_string_short typ
  | TConstr (c, [ typ ]) -> to_id_string_short typ ^ string_of_path c
  | TTuple xs ->
      let xs', x = List.decomp_snoc xs in
      let aux x s = to_id_string_short (Id.typ x) ^ s in
      List.fold_right aux xs' @@ to_id_string_short @@ Id.typ x
  | TAttr (_, typ) -> to_id_string_short typ
  | TConstr (c, _) -> string_of_path c
  | TFuns _ -> [%unsupported]
  | TVariant (_, rows) ->
      rows |> List.take 2 |> List.map (row_constr |- string_of_constr) |> String.join ""
  | TRecord fields -> String.join "" @@ List.map (fst |- string_of_constr) fields
  | TModSig _ | TModLid _ -> "m"
  | TPackage _ -> "p"
  | TPoly (_, ty) -> to_id_string_short ty
  | TConstraint (ty, _) -> to_id_string_short ty
  | TOpen -> "o"

(** order of simpl types *)
let rec order typ =
  match typ with
  | TBase _ -> 0
  | TConstr _ -> assert false
  | TVar (_, { contents = None }, _) -> assert false
  | TVar (_, { contents = Some typ }, _) -> order typ
  | TFun (x, typ) -> max (order (Id.typ x) + 1) (order typ)
  | TTuple xs -> List.fold_left (fun m x -> max m (order @@ Id.typ x)) 0 xs
  | TAttr (_, typ) -> order typ
  | _ -> assert false

let decomp_ttuple typ =
  match elim_tattr typ with TTuple xs -> List.map Id.typ xs | _ -> invalid_arg "decomp_ttuple"

let is_mutable_record typ =
  match typ with
  | TRecord fields -> List.exists (fun (_, (f, _)) -> f = Mutable) fields
  | _ -> invalid_arg "is_mutable_record"

let is_prim_tconstr ty =
  if ty = typ_unknown then invalid_arg "is_prim_tconstr";
  match ty with TConstr (c, _) -> is_prim_constr c | _ -> false

let rec remove_arg_at i ty =
  match elim_tattr ty with
  | TFun (_, typ) when i = 0 -> typ
  | TFun (x, typ) -> TFun (x, remove_arg_at (i - 1) typ)
  | _ -> assert false

let decomp_tattr ty = match ty with TAttr (attrs, ty') -> (attrs, ty') | _ -> ([], ty)
let assoc_tattr ty = fst @@ decomp_tattr ty
let is_tvar ty = match elim_tattr ty with TVar (_, { contents = None }, _) -> true | _ -> false
let is_pure_fun ty = List.mem TAPureFun (fst (decomp_tattr ty))

let rec is_functor_typ ?default env ty =
  match decomp_tfun ty with
  | [], TModLid x -> (
      match Tenv.assoc_value x ~env with
      | ty -> is_functor_typ ?default env ty
      | exception Not_found -> ( match default with None -> raise Not_found | Some b -> b))
  | [], _ -> false
  | _, ty' -> is_mod_typ ty'

let is_functor_typ ?default ?env ty =
  let env =
    match env with
    | None -> !!Tenv.init
    | Some (`Tenv env) -> env
    | Some (`Mod_env env) -> Tenv.env_of_ext_mod env
  in
  is_functor_typ ?default env ty

let is_module_or_functor_typ ty =
  let _, ty' = decomp_tfun ty in
  is_mod_typ ty'

let add_tattr attr ty =
  match ty with
  | TAttr (attrs, ty') when not (List.mem attr attrs) -> TAttr (attr :: attrs, ty')
  | _ -> TAttr ([ attr ], ty)

let filter_map_attr f =
  make_trans (fun tr ty ->
      match ty with
      | TAttr (attr, typ) ->
          let attr' = List.filter_map f attr in
          Some (TAttr (attr', tr typ))
      | _ -> None)

let map_attr f ty = filter_map_attr (Option.some -| f) ty

let map_path f =
  make_trans (fun tr ty ->
      match ty with TConstr (c, tys) -> Some (TConstr (f c, List.map tr tys)) | _ -> None)

let elim_tid l ty = filter_map_attr (function TAId (l', _) when l = l' -> None | a -> Some a) ty
let typ_event () = make_tfun (TBase TUnit) (TBase TUnit)
let typ_event' () = make_tfun (TBase TUnit) typ_result

let typ_event_cps () =
  List.fold_right make_tfun [ TBase TUnit; make_tfun (TBase TUnit) typ_result ] typ_result

let row_of_ext_row { ext_row_path; ext_row_args; ext_row_ret } =
  { row_constr = constr_of_path ext_row_path; row_args = ext_row_args; row_ret = ext_row_ret }

let ext_row_of_row { row_constr; row_args; row_ret } =
  { ext_row_path = LId row_constr; ext_row_args = row_args; ext_row_ret = row_ret }

let map_row_typ ~f { row_constr; row_args; row_ret } =
  { row_constr; row_args = List.map f row_args; row_ret = Option.map f row_ret }

let col_tvars =
  let app xs ys = List.Set.union ~eq:( == ) xs ys in
  let f _ ty = match ty with TVar (_, r, _) -> Some [ r ] | _ -> None in
  fun ty -> make_reduce ~f ~app ~default:[] ty

let col_constrs =
  let app = ( @@@ ) in
  let f cl ty =
    match ty with TConstr (c, tys) -> Some (c :: List.rev_flatten_map cl tys) | _ -> None
  in
  fun ty -> make_reduce ~f ~app ~default:[] ty

let map_pred f ty =
  let f = function
    | TAPred (x, ps) -> TAPred (x, List.map f ps)
    | TARefPred (x, p) -> TARefPred (x, f p)
    | attr -> attr
  in
  map_attr f ty

let subst_tvar map =
  make_trans (fun _ ty -> match ty with TVar (_, r, _) -> List.assq_opt r map | _ -> None)

let subst_constr_map map =
  make_trans (fun f ty ->
      match ty with
      | TConstr (s, tys) when List.mem_assoc ~eq:Path.eq s map ->
          let tys' = List.map f tys in
          Some (subst_tconstr_params tys' (List.assoc ~eq:Path.eq s map))
      | _ -> None)

let col_used_path ty =
  let ( ++ ) = Path.Set.union in
  let default = Path.Set.empty in
  make_reduce ty ~app:( ++ ) ~default ~f:(fun col ty ->
      match ty with
      | TConstr (c, tys) ->
          Some (Path.Set.add c @@ List.fold_left (fun acc ty -> acc ++ col ty) default tys)
      | _ -> None)

module Ty = struct
  let unit = TBase TUnit
  let bool = TBase TBool
  let int = TBase TInt
  let unknown = typ_unknown
  let result = typ_result
  let abst = typ_abst
  let exn = typ_exn
  let string = typ_string
  let bytes = typ_bytes
  let char = typ_char
  let float = typ_float
  let event = typ_event
  let event_cps = typ_event_cps
  let fun_ = make_tfun
  let funs tys ty = List.fold_right make_tfun tys ty
  let pfun = make_ptfun
  let sfun = make_stfun
  let tuple = make_ttuple
  let pair = make_tpair
  let ( * ) = pair
  let list = make_tlist
  let ref = make_tref
  let option = make_toption
  let array = make_tarray
  let set = make_tset
  let lazy_ = make_tlazy
  let attr = add_tattr
end
