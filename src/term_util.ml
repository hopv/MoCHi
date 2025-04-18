[@@@alert "-unsafe"]

open Util
open Type
open Type_util
open Syntax

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

module Id = struct
  include Id

  let new_var ?name ?(attr = []) typ =
    let name = match name with None -> Type_util.var_name_of typ | Some name -> name in
    make ~id:!!new_int name ~attr typ
end

module PredVar = struct
  let pvar_name = "P"
  let is_pvar = Id.is_predicate

  let new_pvar ?(name = pvar_name) ?id tys =
    let ty = List.fold_right make_tfun tys Ty.bool in
    let attr = [ Id.Predicate ] in
    match id with None -> Id.new_var ~name ~attr ty | Some id -> Id.make ~id name ~attr ty
end

module Fmap = struct
  include Fmap

  let id_typ = Id.map_typ
end

let occur_in x t = Id.List.mem x @@ get_fv t

(*** TERM CONSTRUCTORS ***)

let abst_var = Id.make ~id:(-1) "v" typ_unknown
let abst_var_int = Id.set_typ abst_var Ty.int
let abst_var_bool = Id.set_typ abst_var Ty.bool

type attr_info += String of string
type attr_info += Id of id
type attr_info += Term of term
type attr_info += Label of string * attr_info

let () =
  update_pp_attr_info (fun fm info ->
      match info with
      | String s ->
          Format.fprintf fm "%s" s;
          true
      | Id x ->
          Format.fprintf fm "Id %a" Print.id x;
          true
      | Term t ->
          Format.fprintf fm "Term %a" Print.term t;
          true
      | Label (s, info') ->
          Format.fprintf fm "Label(%s, %a)" s pp_attr_info info';
          true
      | _ -> false)

let make_attr ?(attrs = pure_attr) ts =
  let check a = List.for_all (List.mem a -| attr) ts in
  List.filter_map (Option.make check) attrs

let rec is_value t =
  match t.desc with
  | Const _ -> true
  | Var _ -> true
  | Fun _ -> true
  | Nil -> true
  | Cons (t1, t2) -> is_value t1 && is_value t2
  | Tuple ts -> List.for_all is_value ts
  | _ -> false

let copy_tvar =
  let tr = Fold_tr.make () in
  let tr_typ env ty =
    match ty with
    | TVar (false, ({ contents = None } as r), _) -> (
        match List.assq_opt r env with
        | None ->
            let ty = !!new_tvar in
            ((r, ty) :: env, ty)
        | Some ty -> (env, ty))
    | _ -> tr.typ_rec env ty
  in
  tr.typ <- tr_typ;
  fun ?(env = []) t -> tr.term env t

let copy_tvar_list ?(env = []) ts = List.fold_left_map (fun env t -> copy_tvar ~env t) env ts

let can_unify ?env ?(sub = false) ?(ignore_poly_variant = false) ty1 ty2 =
  let env', ty1' = copy_tvar_typ ty1 in
  let _, ty2' = copy_tvar_typ ~env:env' ty2 in
  try
    unify ~for_check:true ?env ~sub ty1' ty2';
    true
  with
  | CannotUnify (Some (ty1, ty2)) when ignore_poly_variant -> (
      match (ty1, ty2) with
      | TVariant (VPoly _, _), _ -> true
      | _, TVariant (VPoly _, _) -> true
      | _ -> false)
  | CannotUnify _ -> false

let can_unify_multi ?env tys =
  let _, tys' = List.fold_right_map (fun ty env -> copy_tvar_typ ~env ty) tys [] in
  match tys' with
  | [] -> invalid_arg "Term_util.can_unify_multi"
  | ty1 :: tys'' -> (
      try
        List.iter (unify ~for_check:true ?env ty1) tys'';
        true
      with CannotUnify _ -> false)

let has_safe_attr t = List.Set.(safe_attr <= t.attr)
let has_pure_attr t = List.Set.(pure_attr <= t.attr)
let add_attrs ?(force = false) attrs t = List.fold_right (add_attr ~force) attrs t

let merge_attrs attrs t =
  add_attrs (List.filter_out (function AFV _ -> true | _ -> false) attrs) t

let add_comment s t = add_attr (AComment s) t
let add_id id t = add_attr (AId id) t

let filter_attr f t = set_attr t (List.filter f t.attr)
[@@alert unsafe "This function must be used carefully"]

let remove_attr_if f t = set_attr t (List.filter_out f t.attr)
[@@alert unsafe "This function must be used carefully"]

let filter_out_attr = remove_attr_if [@@alert unsafe "This function must be used carefully"]

let remove_attr attr t = remove_attr_if (( = ) attr) t
[@@alert unsafe "This function must be used carefully"]

let replace_id id1 id2 t = add_id id2 @@ remove_attr (AId id1) t
let end_of_definitions = make End_of_definitions Ty.unit ~attr:const_attr
let unit_term = make (Const Unit) Ty.unit ~attr:const_attr
let true_term = make (Const True) Ty.bool ~attr:const_attr
let false_term = make (Const False) Ty.bool ~attr:const_attr
let cps_result = make (Const CPS_result) Ty.result ~attr:const_attr
let fail_term = make (Event ("fail", false)) !!Ty.event ~attr:const_attr
let fail_term_cps = make (Event ("fail", true)) !!Ty.event_cps ~attr:const_attr
let make_bool b = if b then true_term else false_term
let make_bottom typ = make Bottom typ
let make_event s = make (Event (s, false)) !!Ty.event ~attr:const_attr
let make_event_cps s = make (Event (s, true)) !!Ty.event_cps ~attr:const_attr
let make_var x = make (Var (LId x)) (Id.typ x) ~attr:pure_attr

let make_var_lid ?typ lid =
  let ty = Option.default_delayed (fun () -> Lid.typ lid) typ in
  make (Var lid) ty ~attr:pure_attr

let make_int n = make (Const (Int n)) Ty.int ~attr:const_attr
let make_string s = make (Const (String s)) Ty.string ~attr:const_attr

let rec make_app ?env t ts =
  let check typ1 typ2 =
    match env with
    | None -> ()
    | Some env ->
        if
          not (Flag.Debug.check_typ && (not (is_mod_typ typ2)) => can_unify ~env ~sub:true typ1 typ2)
        then (
          Format.eprintf "##[make_app]@[@ %a@ <=/=>@ %a@." Print.typ typ1 Print.typ typ2;
          Format.eprintf "##[make_app] fun: %a@." Print.term t;
          Format.eprintf "##[make_app] arg: %a@." Print.term @@ List.hd ts;
          assert false)
  in
  let ty = tfuns_to_tfun @@ elim_tattr t.typ in
  let attr =
    if (List.mem TAPureFun @@ fst @@ decomp_tattr t.typ) && List.for_all has_pure_attr (t :: ts)
    then pure_attr
    else if (List.mem TASafeFun @@ fst @@ decomp_tattr t.typ) && List.for_all has_safe_attr (t :: ts)
    then safe_attr
    else []
  in
  match (t.desc, flatten ty, ts) with
  | _, _, [] -> set_afv_shallowly t
  | App (t1, ts1), TFun (x, typ), t2 :: ts2 ->
      check (Id.typ x) t2.typ;
      make_app (make (App (t1, ts1 @ [ t2 ])) typ ~attr) ts2
  | App (t1, ts1), typ, t2 :: ts2 when typ = typ_unknown || is_tvar typ ->
      make_app (make (App (t1, ts1 @ [ t2 ])) typ ~attr) ts2
  | _, TFun (x, typ), t2 :: ts ->
      check (Id.typ x) t2.typ;
      make_app (make (App (t, [ t2 ])) typ ~attr) ts
  | _, typ, t2 :: ts when typ = typ_unknown || is_tvar typ ->
      make_app (make (App (t, [ t2 ])) typ ~attr) ts
  | _ when not Flag.Debug.check_typ -> make (App (t, ts)) typ_unknown ~attr
  | _ ->
      Format.eprintf "Untypable(make_app) FUN:  %a@." Print.term' t;
      Format.eprintf "                    ARGS: %a@." Print.(list term') ts;
      assert false

let make_app_raw t ts =
  let t' = make_app t ts in
  set_desc t' (App (t, ts))

let rec make_local decl t =
  match decl with
  | Decl_type [] | Decl_let [] | Decl_multi [] -> t
  | Decl_multi decls -> List.fold_right make_local decls t
  | _ ->
      let attr =
        let ts =
          match decl with (* TODO: support modules *)
          | Decl_let defs -> List.map snd defs | _ -> []
        in
        make_attr (t :: ts)
      in
      make (Local (decl, t)) t.typ ~attr

let make_locals decls t = List.fold_right make_local decls t
let make_let bindings t2 = make_local (Decl_let bindings) t2

(** remove unused bindings without changing semantics
    DO NOT USE THIS FOR MUTUAL RECURSIONS *)
let make_let_s bindings t2 =
  let bindings' =
    List.filter
      (fun (f, t1) ->
        occur_in f t2 || (not (has_safe_attr t1)) || List.exists (snd |- occur_in f) bindings)
      bindings
  in
  make_let bindings' t2

let make_lets_s bindings t2 = List.fold_right (make_let_s -| List.singleton) bindings t2
let make_let_type (decls : type_decls) t2 = make_local (Decl_type decls) t2

let make_lets_type (decls : type_decls) t2 =
  List.fold_right (make_let_type -| List.singleton) decls t2

let make_lets bindings t2 = List.fold_right (make_let -| List.singleton) bindings t2

(* Allow t1 with any type not just unit type *)
let make_seq t1 t2 =
  if is_value t1 || has_safe_attr t1 then t2 else make_let [ (Id.new_var ~name:"u" t1.typ, t1) ] t2

let make_seqs = List.fold_right make_seq
let make_ignore t = if t.typ = Ty.unit then t else make_seq t unit_term

let make_fail_unit loc =
  let t = make_app fail_term [ unit_term ] in
  match loc with None -> t | Some loc -> add_attr (ALoc loc) t

let make_fail ?loc ?(force = false) typ =
  let t2 = make_bottom typ in
  if !Flag.Method.only_specified && not force then t2 else make_seq (make_fail_unit loc) t2

let make_fun x t =
  let attr =
    let fv = List.filter_out Id.(( = ) x) (get_fv t) in
    AFV fv :: pure_attr
  in
  make (Fun (x, t)) (TFun (x, t.typ)) ~attr

let make_pure_fun x t =
  let attr =
    let fv = List.filter_out Id.(( = ) x) (get_fv t) in
    AFV fv :: pure_attr
  in
  make (Fun (x, t)) (pureTFun (x, t.typ)) ~attr

let make_funs = List.fold_right make_fun

let make_not t =
  match t.desc with
  | Const True -> false_term
  | Const False -> true_term
  | Not t -> t
  | _ -> make (Not t) (TBase TBool) ~attr:(make_attr [ t ])

let make_and t1 t2 =
  if t1 = false_term then false_term
  else if t1 = true_term then t2
  else if t2 = true_term then t1
  else if t2 = false_term && has_safe_attr t1 then false_term
  else make (BinOp (And, t1, t2)) (TBase TBool) ~attr:(make_attr [ t1; t2 ])

let make_ands ts = List.fold_right make_and ts true_term

let make_or t1 t2 =
  if t1 = true_term then true_term
  else if t1 = false_term then t2
  else if t2 = false_term then t1
  else if t2 = true_term && has_safe_attr t1 then true_term
  else make (BinOp (Or, t1, t2)) (TBase TBool) ~attr:(make_attr [ t1; t2 ])

let make_ors ts = List.fold_right make_or ts false_term

let make_add t1 t2 =
  if t2.desc = Const (Int 0) then t1
  else if t1.desc = Const (Int 0) then t2
  else make (BinOp (Add, t1, t2)) (TBase TInt) ~attr:(make_attr [ t1; t2 ])

let make_sub t1 t2 =
  if t2.desc = Const (Int 0) then t1
  else make (BinOp (Sub, t1, t2)) (TBase TInt) ~attr:(make_attr [ t1; t2 ])

let make_mul t1 t2 =
  if t1.desc = Const (Int 0) && has_safe_attr t2 then make_int 0
  else if t2.desc = Const (Int 0) && has_safe_attr t1 then make_int 0
  else if t2.desc = Const (Int 1) then t1
  else if t1.desc = Const (Int 1) then t2
  else make (BinOp (Mult, t1, t2)) (TBase TInt) ~attr:(make_attr [ t1; t2 ])

let make_div t1 t2 = make (BinOp (Div, t1, t2)) (TBase TInt) ~attr:(make_attr [ t1; t2 ])
let make_neg t = make_sub (make_int 0) t

let make_if_ t1 t2 t3 =
  assert (Flag.Debug.check_typ => can_unify t1.typ (TBase TBool));
  assert (Flag.Debug.check_typ => can_unify t2.typ t3.typ);
  match t1.desc with
  | Const True -> t2
  | Const False -> t3
  | _ ->
      let typ =
        match (has_pred t2.typ, has_pred t3.typ) with
        | _, false -> t2.typ
        | false, true -> t3.typ
        | true, true ->
            if t2.typ <> t3.typ then
              warning " @[<hv 2>if-branches have different types@ %a and@ %a@]" Print.typ t2.typ
                Print.typ t3.typ;
            t2.typ
      in
      make (If (t1, t2, t3)) typ ~attr:(make_attr [ t1; t2; t3 ])

let make_eq t1 t2 =
  assert (Flag.Debug.check_typ => can_unify t1.typ t2.typ);
  match (t1.desc, t2.desc) with
  | Const c1, Const c2 -> make_bool (c1 = c2)
  | _ ->
      if t1.typ = Ty.unit && has_safe_attr t1 && has_safe_attr t2 then true_term
      else make (BinOp (Eq, t1, t2)) (TBase TBool) ~attr:(make_attr [ t1; t2 ])

let make_neq t1 t2 = make_not (make_eq t1 t2)
let make_lt t1 t2 = make (BinOp (Lt, t1, t2)) (TBase TBool) ~attr:(make_attr [ t1; t2 ])
let make_gt t1 t2 = make (BinOp (Gt, t1, t2)) (TBase TBool) ~attr:(make_attr [ t1; t2 ])
let make_leq t1 t2 = make (BinOp (Leq, t1, t2)) (TBase TBool) ~attr:(make_attr [ t1; t2 ])
let make_geq t1 t2 = make (BinOp (Geq, t1, t2)) (TBase TBool) ~attr:(make_attr [ t1; t2 ])

let make_binop op =
  match op with
  | Eq -> make_eq
  | Lt -> make_lt
  | Gt -> make_gt
  | Leq -> make_leq
  | Geq -> make_geq
  | And -> make_and
  | Or -> make_or
  | Add -> make_add
  | Sub -> make_sub
  | Mult -> make_mul
  | Div -> make_div

let make_proj i t = make (Proj (i, t)) (proj_typ i t.typ) ~attr:(make_attr [ t ])

let make_tuple ts =
  let typ = make_ttuple @@ List.map Syntax.typ ts in
  make (Tuple ts) typ ~attr:(make_attr ts)

let make_fst ?typ t =
  let ty = Option.default_delayed (fun () -> proj_typ 0 t.typ) typ in
  make (Proj (0, t)) ty ~attr:(make_attr [ t ])

let make_snd ?typ t =
  let ty = Option.default_delayed (fun () -> proj_typ 1 t.typ) typ in
  make (Proj (1, t)) ty ~attr:(make_attr [ t ])

let make_pair t1 t2 = make_tuple [ t1; t2 ]
let make_nil ~elem_typ = make Nil (make_tlist elem_typ) ~attr:const_attr
let make_nil2 ~list_typ = make Nil list_typ ~attr:const_attr

let make_cons t1 t2 =
  assert (Flag.Debug.check_typ => can_unify (make_tlist t1.typ) t2.typ);
  make (Cons (t1, t2)) t2.typ ~attr:(make_attr [ t1; t2 ])

let rec make_list ?typ ts =
  match (ts, typ) with
  | [], None -> make_nil ~elem_typ:typ_unknown
  | [], Some ty -> make_nil ~elem_typ:ty
  | [ t1 ], _ -> make_cons t1 @@ make_nil ~elem_typ:t1.typ
  | t1 :: ts', _ -> make_cons t1 @@ make_list ts'

let make_pany typ = make_pattern PAny typ
let make_pvar x = make_pattern (PVar x) (Id.typ x)
let make_pconst t = make_pattern (PConst t) t.typ
let make_pnondet ty = make_pattern PNondet ty
let make_ppair p1 p2 = make_pattern (PTuple [ p1; p2 ]) (make_tpair p1.pat_typ p2.pat_typ)
let make_ptuple ps = make_pattern (PTuple ps) (make_ttuple @@ List.map (fun p -> p.pat_typ) ps)
let make_pnil ~elem_typ = make_pattern PNil (make_tlist elem_typ)
let make_pnil2 ~list_typ = make_pattern PNil list_typ
let make_pcons p1 p2 = make_pattern (PCons (p1, p2)) p2.pat_typ
let make_por p1 p2 = make_pattern (POr (p1, p2)) p1.pat_typ

let make_plist ?elem_typ ?list_typ ps =
  let nil =
    match (elem_typ, list_typ, ps) with
    | Some ty, _, _ -> make_pnil ~elem_typ:ty
    | _, Some ty, _ -> make_pnil2 ~list_typ:ty
    | _, _, p :: _ -> make_pnil ~elem_typ:p.pat_typ
    | _ -> invalid_arg "%s" __FUNCTION__
  in
  List.fold_right make_pcons ps nil

let make_pwhen p t =
  if t.desc = Const True then p
  else
    let p', t' = match p.pat_desc with PWhen (p', t') -> (p', make_and t t') | _ -> (p, t) in
    make_pattern (PWhen (p', t')) p.pat_typ

let make_plazy p = make_pattern (PLazy p) (Ty.lazy_ p.pat_typ)
let make_peval x t p = make_pattern (PEval (x, t, p)) (Id.typ x)
let make_psome p = make_pattern (PSome p) (Ty.option p.pat_typ)
let make_palias p x = make_pattern (PAlias (p, x)) p.pat_typ
let make_label_aux info t = add_attr (AInfo info) t

let make_label ?(label = "") info t =
  let info = if label = "" then info else Label (label, info) in
  make_label_aux info t

let decomp_label ?label t =
  let attr1, attr2 =
    match label with
    | None -> List.partition_map (function AInfo info -> Left info | attr -> Right attr) t.attr
    | Some l ->
        List.partition_map
          (function AInfo (Label (l', info)) when l = l' -> Left info | info -> Right info)
          t.attr
  in
  (attr1, set_attr t attr2)

let assoc_label ?label t = fst @@ decomp_label ?label t
let remove_label ?label t = snd @@ decomp_label ?label t
let make_ref t = make (Ref t) (make_tref t.typ)

let make_deref ?typ t =
  let typ = match typ with None -> ref_typ t.typ | Some ty -> ty in
  make (Deref t) typ

let make_setref r t = make (SetRef (r, t)) (TBase TUnit)
let make_construct ?(poly = false) c ts typ = make (Constr (poly, c, ts)) typ ~attr:(make_attr ts)
let make_record fields typ = make (Record fields) typ

let make_field ?ty t s =
  let typ =
    Option.default_delayed (fun () -> t.typ |> ValE'._TRecord |> Id.List.assoc s |> snd) ty
  in
  make (Field (t, s)) typ

let make_event_unit s = make_app (make_event s) [ unit_term ]
let make_raise ~typ t = make (Raise t) typ
let make_imply t1 t2 = make_or (make_not t1) t2

let make_eq_dec t1 t2 =
  assert (Flag.Debug.check_typ => can_unify t1.typ t2.typ);
  let aux t =
    match t.desc with
    | Var x -> (make_var_lid x, Fun.id)
    | _ ->
        let x = Id.new_var t.typ in
        (make_var x, make_let [ (x, t) ])
  in
  let rec make t1 t2 =
    match t1.typ with
    | TBase _ -> make_eq t1 t2
    | TTuple xs ->
        let n = List.length xs in
        List.fromto 0 n
        |> List.map (fun i -> make (make_proj i t1) (make_proj i t2))
        |> List.fold_left make_and true_term
    | _ -> assert false
  in
  let t1', k1 = aux t1 in
  let t2', k2 = aux t2 in
  k1 @@ k2 @@ make t1' t2'

let is_length_var (x : lid) =
  match x with LId x -> Id.is_primitive x && Id.name x = "List.length" | _ -> false

let make_length_var typ =
  let x = Id.make ~id:(-1) "l" typ in
  Id.make ~id:(-1) "List.length" ~attr:[ Id.Primitive ] (TFun (x, Ty.int))

let make_length t =
  make_app (make_var @@ make_length_var t.typ) [ t ] |> add_attrs safe_attr |> set_afv_shallowly

let sig_items_of_decl ?env decl =
  match decl with
  | Decl_let defs -> List.map (_Sig_value -| fst) defs
  | Decl_type decls -> [ Sig_type decls ]
  | Include t -> sig_of_mod_typ ~env:(Option.default [] env) t.typ
  | Type_ext (Ext_type (s, (params, row))) -> [ Sig_ext (s, (params, row)) ]
  | Type_ext (Ext_rebind (s1, _s2)) when not (C.is_exn (Type.LId s1)) ->
      unsupported "rebind except exceptions"
  | Type_ext (Ext_rebind (s1, _s2)) ->
      (* TODO: fix *)
      let row = { ext_row_path = Type.LId s1; ext_row_args = []; ext_row_ret = None } in
      [ Sig_ext (C.exn, ([], row)) ]
  | Decl_multi _ -> [%invalid_arg]

let make_module ?typ ?env decls =
  let decls = List.filter_out (fun decl -> decl = Decl_type [] || decl = Decl_let []) decls in
  let typ =
    match typ with
    | None ->
        let sgn = decls |> List.flatten_map (sig_items_of_decl ?env) in
        let not_unique () = failwith "Names must be unique in a structure/signature" in
        if
          not
          @@ List.is_unique ~eq:(Compare.eq_on Id.name)
          @@ List.filter is_mod_var
          @@ sig_values sgn
        then not_unique ();
        if
          not
          @@ List.is_unique ~eq:(Compare.eq_on (fst |- Id.name))
          @@ List.filter_out (snd |- snd |- is_class) (* WORKAROUND *)
          @@ List.flatten
          @@ sig_types sgn
        then not_unique ();
        TModSig sgn
    | Some ty -> ty
  in
  make (Module decls) typ

let make_pack t ty = make (Pack t) (TPackage ty)

let make_unpack ?typ t =
  let ty =
    match (typ, t.typ) with
    | None, TPackage ty -> ty
    | Some ty, _ -> ty
    | _ -> invalid_arg "Term_util.make_unpack"
  in
  make (Unpack t) ty

let make_dummy ty = match ty with TBase TUnit -> unit_term | _ -> make (Const (Dummy ty)) ty

let rec make_default_term typ =
  match elim_tattr typ with
  | TBase TUnit -> unit_term
  | TBase TBool -> true_term
  | TBase TInt -> make_int 0
  | TFun (x, typ) -> make_fun x (make_default_term typ)
  | TTuple xs -> make_tuple @@ List.map (make_default_term -| Id.typ) xs
  | TConstr (c, []) when c = C.char -> make (Const (Char '\000')) typ ~attr:const_attr
  | TConstr (c, []) when c = C.string -> make (Const (String "")) typ ~attr:const_attr
  | TConstr (c, []) when c = C.float -> make (Const (Float 0.)) typ ~attr:const_attr
  | TConstr (c, [ typ' ]) when c = C.list -> make_nil ~elem_typ:typ'
  | ty when ty = typ_result -> cps_result
  | _ -> make_dummy typ

let make_none ~elem_typ = make TNone (make_toption elem_typ)
let make_none2 ~opt_typ = make TNone opt_typ
let make_some t = make (TSome t) (make_toption t.typ)
let make_lazy t = make (Lazy t) (make_tlazy t.typ) ~attr:pure_attr
let make_forall x t = make (Forall (x, t)) Ty.bool
let make_exists x t = make (Exists (x, t)) Ty.bool
let none_flag = false_term
let some_flag = true_term

(*
let none_flag = make_int 0
let some_flag = make_int 1
 *)
let opt_typ_enc typ = TTuple [ Id.new_var none_flag.typ; Id.new_var typ ]
let get_opt_typ_enc typ = snd_typ typ
let is_none_enc t = match t.desc with Tuple [ t1; _ ] -> t1 = none_flag | _ -> false

let decomp_some_enc t =
  match t.desc with Tuple [ t1; t2 ] when t1 = some_flag -> Some t2 | _ -> None

let make_none_enc typ = make_pair none_flag (make_default_term typ)
let make_some_enc t = make_pair some_flag t
let make_is_none_enc t = make_eq (make_fst t) none_flag
let make_is_some_enc t = make_not (make_is_none_enc t)
let make_get_val t = make_snd t

let decomp_is_none_enc t =
  match t.desc with
  | BinOp (Eq, { desc = Proj (0, t1) }, t2) when t2 = none_flag -> Some t1
  | _ -> None

let decomp_get_val t = match t.desc with Proj (1, t) -> Some t | _ -> None
let make_type_ext ext t = make_local (Type_ext (Ext_type ext)) t

(*** AUXILIARY FUNCTIONS ***)

let is_base_var x = is_base_typ @@ Id.typ x
let is_fun_var x = is_fun_typ @@ Id.typ x
let is_fun t = [] <> fst @@ decomp_funs t
let decomp_decls = decomp_locals
let is_mod_or_functor_var x = (is_mod_typ ||| is_functor_typ) @@ Id.typ x

let rec decomp_lets t =
  match t.desc with
  | Local (Decl_let bindings, t2) ->
      let fbindings, t2' = decomp_lets t2 in
      (bindings :: fbindings, t2')
  | _ -> ([], t)

let rec decomp_and t =
  match t.desc with BinOp (And, t1, t2) -> decomp_and t1 @@@ decomp_and t2 | _ -> [ t ]

let rec decomp_or t =
  match t.desc with BinOp (Or, t1, t2) -> decomp_or t1 @@@ decomp_or t2 | _ -> [ t ]

let decomp_assert t =
  match t.desc with
  | If
      ( t1,
        { desc = Const Unit },
        { desc = App ({ desc = Event ("fail", _) }, [ { desc = Const Unit } ]); attr } ) ->
      let loc = List.find_map_opt (function ALoc loc -> Some loc | _ -> None) attr in
      Some (t1, loc)
  | _ -> None

let get_int = Col.make [] ( @@@ )
let get_int_term t = match t.desc with Const (Int n) -> [ n ] | _ -> get_int.term_rec t
let get_int_typ _ = []
let () = get_int.term <- get_int_term
let () = get_int.typ <- get_int_typ
let get_int t = List.unique @@ get_int.term t
let rec get_args ty = match elim_tattr ty with TFun (x, typ) -> x :: get_args typ | _ -> []

let rec get_argvars ty =
  match elim_tattr ty with
  | TFun (x, typ) -> (x :: get_argvars (Id.typ x)) @ get_argvars typ
  | _ -> []

let rec get_argtyps ty =
  match elim_tattr ty with TFun (x, typ) -> Id.typ x :: get_argtyps typ | _ -> []

let arg_num typ = List.length (get_args typ)

let is_poly_typ_aux =
  let col = Col2.make false ( || ) in
  col.typ <-
    (fun weak typ ->
      match elim_tattr typ with
      | TVar (b, { contents = None }, _) -> weak => b
      | _ -> col.typ_rec weak typ);
  col.term <- Fun.const2 false;
  col.typ

let is_poly_typ t = is_poly_typ_aux false t
let is_weak_poly_typ t = is_poly_typ_aux true t

let rename, rename_pat =
  let tr = Tr2.make () in
  tr.var <-
    (fun map x ->
      match Id.List.assoc_opt x map with None -> x | Some y -> Id.set_typ y @@ Id.typ x);
  tr.typ <- Fun.snd;
  (tr.term, tr.pat)

let subst = Tr2.make ()

(* does not include primitive type consructors *)
(* TODO: deal with modules *)
let get_tconstr, get_tconstr_typ =
  let col = Col.make [] ( @@@ ) in
  col.typ <-
    (fun ty ->
      match ty with
      | TConstr (c, tys) when not (Type_util.is_prim_constr c) ->
          (c, tys) :: List.rev_map_flatten col.typ tys
      | _ -> col.typ_rec ty);
  (col.term, col.typ)

let trans_decls_as_term f decls =
  let decls', eod = decls |> make_locals -$- end_of_definitions |> f |> decomp_decls in
  assert (eod.desc = End_of_definitions);
  decls'

(* [x |-> t], [t/x] *)
(* ASSUME: fv_t = FV(t) *)
let subst_term ((b_ty, x, t, fv_t) as arg) t' =
  let t' = if b_ty then make_raw ~attr:t'.attr t'.desc (subst.typ arg t'.typ) else t' in
  if (not b_ty) && not (Id.List.mem x @@ get_fv t') then t'
  else
    let rename map t =
      List.fold_left (fun t (y, y') -> subst.term_rec (b_ty, y, make_var y', [ y' ]) t) t map
    in
    match t'.desc with
    | Var (LId y) when Id.(x = y) -> t
    | Var lid ->
        let map' =
          Lid.heads lid
          |> List.filter_map (fun h ->
                 if Id.(h = x) then (
                   match t.desc with
                   | Var lid' -> Some (h, lid')
                   | _ ->
                       Format.eprintf "lid: %a@." Print.lid lid;
                       Format.eprintf "h: %a@." Print.id h;
                       Format.eprintf "t: %a@." Print.term t;
                       [%unsupported])
                 else None)
          |> IdMap.of_list
        in
        if IdMap.is_empty map' then t' else make_var_lid ~typ:t'.typ (Lid.subst_head map' lid)
    | Fun (y, _) when Id.(x = y) -> t'
    | Fun (y, t1) when Id.List.mem y fv_t ->
        let y' = Id.new_var_id y in
        let desc = subst.desc_rec arg @@ Fun (y', rename [ (y, y') ] t1) in
        make desc t'.typ
    | Local (Decl_let bindings, _) when Id.List.mem_assoc x bindings -> t'
    | Local (Decl_let bindings, t2) when List.exists (Id.List.mem_assoc -$- bindings) fv_t ->
        let map =
          bindings
          |> List.filter_map (fun (y, _) -> if Id.List.mem y fv_t then Some y else None)
          |> List.map (Pair.add_right Id.new_var_id)
        in
        let bindings' = List.map (Pair.map (Id.List.subst map) (rename map)) bindings in
        let t2' = rename map t2 in
        let desc = subst.desc_rec arg @@ Local (Decl_let bindings', t2') in
        make desc t'.typ
    | Match (t1, pats) ->
        let pats =
          pats
          |> List.map (fun (p, t) ->
                 let map =
                   get_bv_pat p
                   |> Id.List.Set.inter -$- fv_t
                   |> List.map (Pair.add_right Id.new_var_id)
                 in
                 (rename_pat map p, rename map t))
          |> List.map (fun (p, t1) ->
                 let xs = get_bv_pat p in
                 if List.exists (Id.same x) xs then (p, t1) else (subst.pat arg p, subst.term arg t1))
        in
        let desc = Match (subst.term arg t1, pats) in
        make desc t'.typ
    | Module decls ->
        (* TODO: should be capture-avoiding *)
        let rec aux decls =
          match decls with
          | [] -> []
          | Decl_let bindings :: _ when Id.List.mem_assoc x bindings -> decls
          | decl :: decls' -> subst.decl arg decl :: aux decls'
        in
        let desc = Module (aux decls) in
        make desc t'.typ
    | _ -> subst.term_rec arg t'

let subst_int = Tr2.make ()

let subst_int_term (n, t) t' =
  match t'.desc with
  | Const (Int m) when n = m -> t
  | Const (Int m) -> make_add t @@ make_int (m - n)
  | _ -> subst_int.term_rec (n, t) t'

let () = subst_int.term <- subst_int_term
let subst_int n t t' = subst_int.term (n, t) t'

let subst_map, subst_decl_map =
  let tr = Tr2.make () in
  tr.term <-
    (fun map t ->
      match List.filter (fst |- Id.List.mem -$- get_fv t) map with
      | [] -> t
      | map ->
          let t' =
            match t.desc with
            | Var (LId y) -> ( match Id.List.assoc_opt y map with None -> t | Some (t, _) -> t)
            | Var lid ->
                let map' =
                  Lid.heads lid
                  |> List.filter_map (fun h ->
                         match Id.List.assoc_opt h map with
                         | None -> None
                         | Some ({ desc = Var lid' }, _) -> Some (h, lid')
                         | Some _ -> unsupported "%s" __FUNCTION__)
                  |> IdMap.of_list
                in
                if IdMap.is_empty map' then t else make_var_lid ~typ:t.typ (Lid.subst_head map' lid)
            | Fun (y, t1) ->
                let map' = List.filter_out (fst |- Id.same y) map in
                let t1' = tr.term map' t1 in
                make_fun y t1'
            | Local (Decl_let bindings, t2) ->
                let map' = List.filter (fun (x, _) -> not (Id.List.mem_assoc x bindings)) map in
                let bindings' = List.map (Pair.map_snd @@ tr.term map') bindings in
                let t2' = tr.term map' t2 in
                make_let bindings' t2'
            | Match (t1, pats) ->
                let pats =
                  List.L.map pats ~f:(fun (p, t1) ->
                      let map' = List.filter_out (fst |- Id.List.mem -$- get_bv_pat p) map in
                      (set_afv_abv_pat @@ tr.pat map' p, tr.term map' t1))
                in
                make (Match (tr.term map t1, pats)) t.typ
            | _ -> set_afv_shallowly @@ tr.term_rec map t
          in
          merge_attrs t.attr t');
  tr.attr <-
    (fun map attrs ->
      let sbst y = match Id.List.assoc_opt y map with Some (_, fv) -> fv | None -> [ y ] in
      List.map (function AFV xs -> AFV (List.rev_flatten_map sbst xs) | a -> a) attrs);
  let make_map = List.map (Pair.map_snd (Pair.add_right get_fv)) in
  (tr.term -| make_map, tr.decl -| make_map)

let subst_attr (_, x, _, fv_t) attrs =
  let sbst y = if Id.(x = y) then fv_t else [ y ] in
  List.map (function AFV xs -> AFV (List.rev_flatten_map sbst xs) | a -> a) attrs

(* TODO: Fix the inefficient recursive application of "subst_path_head" *)
let subst_typ ((b_ty, x, t, _) as arg) ty =
  let ty = subst.typ_rec arg ty in
  match t.desc with
  | Var m when b_ty -> subst_path_head (tconstr_of_id x) (path_of_lid m) ty
  | _ -> ty

let () = subst.term <- subst_term
let () = subst.pat <- (fun arg t -> subst.pat_rec arg t |> set_afv_abv_pat)
let () = subst.attr <- subst_attr
let () = subst.typ <- subst_typ
let subst_type ?(b_ty = true) x t typ = subst.typ (b_ty, x, t, get_fv t) typ
let subst_type_var x y typ = subst_type x (make_var y) typ
let subst_decl ?(b_ty = false) x t decl = subst.decl (b_ty, x, t, get_fv t) decl

let subst ?(b_ty = false) x t1 t2 =
  let fv = get_fv t1 in
  subst.term (b_ty, x, t1, fv) t2

let subst_var x y t = subst x (make_var y) t
let subst_var_map map t = subst_map (List.map (Pair.map_snd make_var) map) t

let subst_var_map_without_typ : lid IdMap.t -> term -> term =
  let tr = Tr2.make () in
  let assoc map x =
    match IdMap.find x map with
    | LId x' -> LId (Id.set_typ x' (Id.typ x))
    | lid -> lid
    | exception Not_found -> LId x
  in
  tr.desc <-
    (fun map desc ->
      match desc with
      | Var (LId x) -> Var (assoc map x)
      | Var x -> Var (Lid.subst_head map x)
      | Fun (x, t) ->
          let map = IdMap.remove x map in
          if IdMap.is_empty map then desc else Fun (tr.var map x, tr.term map t)
      | Local (Decl_let bindings, t2) ->
          let map = List.fold_left (fun map (x, _) -> IdMap.remove x map) map bindings in
          if IdMap.is_empty map then desc
          else
            let bindings' = List.map (Pair.map (tr.var map) (tr.term map)) bindings in
            let t2' = tr.term map t2 in
            Local (Decl_let bindings', t2')
      | Match (t1, pats) ->
          let pats' =
            pats
            |> List.map (fun (p, t1) ->
                   let bv = get_bv_pat p in
                   let map = List.fold_right IdMap.remove bv map in
                   if IdMap.is_empty map then (p, t1) else (tr.pat map p, tr.term map t1))
          in
          Match (tr.term map t1, pats')
      | Module decls -> Module (trans_decls_as_term (tr.term map) decls)
      | _ -> tr.desc_rec map desc);
  tr.attr <-
    (fun map ->
      List.map (function
        | AFV xs -> AFV (List.flatten_map (assoc map |- Lid.heads) xs)
        | attr -> attr));
  tr.typ <-
    (fun map ->
      let map' =
        map |> IdMap.filter_map (fun x lid -> if is_mod_var x then Some (path_of_lid lid) else None)
      in
      let map'' x = IdMap.find_opt (Id.set_typ x Ty.unit) map' in
      subst_path_head_map map'' |- map_pred (tr.term map));
  tr.pat <- set_afv_abv_pat --| tr.pat_rec;
  fun map t -> if IdMap.is_empty map then t else tr.term map t

let subst_var_without_typ x y t = subst_var_map_without_typ (IdMap.singleton x y) t

let make_nonrec_let_gen mk bindings t2 =
  let map =
    bindings
    |> List.filter (fun (f, t) -> Id.List.mem f @@ get_fv t)
    |> List.map fst
    |> List.map (Pair.add_right Id.new_var_id)
  in
  let map' = List.map (Pair.map_snd _LId) map |> IdMap.of_list in
  let bindings' = Fmap.(list (fst (Id.List.subst map))) bindings in
  mk bindings' @@ subst_var_map_without_typ map' t2

let make_nonrec_let bindings t2 = make_nonrec_let_gen make_let bindings t2
let make_nonrec_let_s bindings t2 = make_nonrec_let_gen make_let_s bindings t2
let make_nonrec_lets bindings t2 = List.fold_right (make_nonrec_let -| List.singleton) bindings t2

let make_nonrec_lets_s bindings t2 =
  List.fold_right (make_nonrec_let_s -| List.singleton) bindings t2

let make_match ?typ t1 pats =
  match pats with
  | [] -> ( match typ with None -> [%invalid_arg] | Some ty -> make_bottom ty)
  | [ ({ pat_desc = PVar x; pat_typ }, t2) ] ->
      unify t1.typ pat_typ;
      make_nonrec_let [ (x, t1) ] t2
  | [ ({ pat_desc = PTuple ps }, t) ] when Is._Tuple t1 && List.for_all Is._PVar ps ->
      let xs = List.map ValE._PVar ps in
      let must_rename = List.filter (Id.List.mem -$- get_fv t1) xs in
      let xs', t' =
        if must_rename = [] then (xs, t)
        else
          let map = List.map (Pair.add_right Id.new_var_id) must_rename in
          let xs' = List.map (Id.List.subst map) xs in
          let map' = List.map (Pair.map_snd _LId) map |> IdMap.of_list in
          (xs', subst_var_map_without_typ map' t)
      in
      let bind = List.combine xs' (ValE._Tuple t1) in
      List.iter (fun (x, t) -> unify (Id.typ x) t.typ) bind;
      let bind = if Flag.EvalStrategy.tuple_left_to_right then bind else List.rev bind in
      make_lets bind t'
  | (_, t) :: _ ->
      let ty = Option.default t.typ typ in
      let t =
        let pats' =
          let rec match_any p =
            match p.pat_desc with
            | PAny -> true
            | PVar _ -> true
            | PAlias (p1, _) -> match_any p1
            | PConst { desc = Const Unit } -> true
            | POr (p1, p2) -> match_any p1 || match_any p2
            | PWhen (p, c) -> match_any p && c.desc = Const True
            | _ -> false
          in
          let aux (p, t) acc = (p, t) :: (if match_any p then [] else acc) in
          List.fold_right aux pats []
        in
        match pats' with
        | [ ({ pat_desc = PAny }, t2) ] -> make_seq t1 t2
        | [ ({ pat_desc = PVar x }, t2) ] ->
            if Id.List.mem x @@ get_fv t1 then
              let x' = Id.new_var_id x in
              make_let_s [ (x', t1) ] @@ subst_var_without_typ x (LId x') t2
            else make_let_s [ (x, t1) ] t2
        | _ -> make (Match (t1, pats')) ty
      in
      set_typ t ty

let make_single_match ?(total = false) t1 p t2 =
  let rec is_total p =
    match p.pat_desc with
    | PAny -> true
    | PVar _ -> true
    | PTuple ps -> List.for_all is_total ps
    | PRecord fields -> List.for_all (snd |- is_total) fields
    | PAlias (p, _) -> is_total p
    | _ -> false
  in
  if total || is_total p then make_match t1 [ (p, t2) ]
  else make_match t1 [ (p, t2); (make_pany p.pat_typ, make_fail t2.typ) ]

let make_trywith_handler t handler =
  if has_safe_attr t then t else make (TryWith (t, handler)) t.typ

let make_trywith t x pats =
  if has_safe_attr t then t
  else
    let handler = make_fun x @@ make_match (make_var x) pats in
    make_trywith_handler t handler

let make_function ~partial ~loc ?ty_arg ~ty_ret pats =
  let ty = Option.default_delayed (fun () -> (fst (List.hd pats)).pat_typ) ty_arg in
  let x = Id.new_var ty in
  match pats with
  | [ ({ pat_desc = PAny }, t') ] -> make_fun x t'
  | [ ({ pat_desc = PVar y }, t') ] -> make_fun x @@ subst_var y x t'
  | [ ({ pat_desc = PConst { desc = Const Unit } }, t') ] -> make_fun x t'
  | _ ->
      let pats' = if partial then pats @ [ (make_pany ty, make_fail ~loc ty_ret) ] else pats in
      make_fun x @@ make_match ~typ:ty_ret (make_var x) pats'

let make_empty ty = make (Const Empty) (make_tset ty) ~attr:const_attr
let make_mem t1 t2 = make (MemSet (t1, t2)) Ty.bool ~attr:(make_attr [ t1; t2 ])
let make_addset t1 t2 = make (AddSet (t1, t2)) t2.typ ~attr:(make_attr [ t1; t2 ])
let make_subset t1 t2 = make (Subset (t1, t2)) Ty.bool ~attr:(make_attr [ t1; t2 ])

let get_tapred typ =
  match typ with
  | TAttr (attrs, _) ->
      Option.of_list
      @@ List.filter_map (function TAPred (x, ps) -> Some (x, ps) | _ -> None) attrs
  | _ -> None

let add_tapred x ps typ =
  let attrs', typ' =
    match (get_tapred typ, typ) with
    | None, _ -> ([ TAPred (x, ps) ], typ)
    | Some (x', ps'), TAttr (attrs, typ') ->
        let attrs' = List.filter (function TAPred _ -> false | _ -> true) attrs in
        let ps' = List.map (subst_var x' x) ps' @ ps in
        (TAPred (x, ps') :: attrs', typ')
    | _ -> assert false
  in
  _TAttr attrs' typ'

let max_pat_num = Col.make 0 max

let max_pat_num_term t =
  match t.desc with
  | Match (t, pats) ->
      let m = max (List.length pats) (max_pat_num.term t) in
      let aux acc (_, t) = max acc (max_pat_num.term t) in
      List.fold_left aux m pats
  | _ -> max_pat_num.term_rec t

let () = max_pat_num.term <- max_pat_num_term
let max_pat_num = max_pat_num.term

let rec same_const c1 c2 =
  match (c1, c2) with
  | Rand (typ1, b1), Rand (typ2, b2) -> b1 = b2 && same_shape typ1 typ2
  | _ -> c1 = c2

and same_term t1 t2 = same_desc t1.desc t2.desc

and same_desc t1 t2 =
  let ( === ) = same_term in
  match (t1, t2) with
  | Const c1, Const c2 -> same_const c1 c2
  | Var x, Var y -> Lid.(x = y)
  | Fun (x, t1), Fun (y, t2) -> t1 === subst_var y x t2
  | App (t1, ts1), App (t2, ts2) -> List.eq ~eq:same_term (t1 :: ts1) (t2 :: ts2)
  | If (t11, t12, t13), If (t21, t22, t23) -> t11 === t21 && t12 === t22 && t13 === t23
  | Local (Decl_let bindings1, t1), Local (Decl_let bindings2, t2) ->
      let eq (f, t1) (g, t2) = Id.(f = g) && t1 === t2 in
      List.eq ~eq bindings1 bindings2 && t1 === t2
  | BinOp (op1, t11, t12), BinOp (op2, t21, t22) -> op1 = op2 && t11 === t21 && t12 === t22
  | Not t1, Not t2 -> t1 === t2
  | Event (s1, b1), Event (s2, b2) -> s1 = s2 && b1 = b2
  | Record fields1, Record fields2 -> List.eq ~eq:(Pair.eq ( = ) ( === )) fields1 fields2
  | Field (t1, s1), Field (t2, s2) -> t1 === t2 && s1 = s2
  | SetField (t11, s1, t12), SetField (t21, s2, t22) -> t11 === t21 && s1 = s2 && t12 === t22
  | Nil, Nil -> true
  | Cons (t11, t12), Cons (t21, t22) -> t11 === t21 && t12 === t22
  | Constr (b1, c1, ts1), Constr (b2, c2, ts2) ->
      b1 = b2 && c1 = c2 && List.for_all2 ( === ) ts1 ts2
  | Match (t1, pats1), Match (t2, pats2) ->
      let eq (pat1, t1) (pat2, t2) = pat1 = pat2 && t1 === t2 in
      t1 === t2 && List.eq ~eq pats1 pats2
  | Raise t1, Raise t2 -> t1 === t2
  | TryWith (t11, t12), TryWith (t21, t22) -> t11 === t21 && t12 === t22
  | Tuple ts1, Tuple ts2 -> List.eq ~eq:same_term ts1 ts2
  | Proj (i, t1), Proj (j, t2) -> i = j && t1 === t2
  | Bottom, Bottom -> true
  | _ -> false

and same_info _i1 _i2 = unsupported "same_term"
and same_type_kind _k1 _k2 = unsupported "same_term"
and same_typed_pattern p1 p2 = same_pattern p1.desc p2.desc
and same_pattern _p1 _p2 = unsupported "same_term"

let same_term' t1 t2 = try same_term t1 t2 with _ -> false (* WORKAROUND *)

let var_name_of_term t =
  let rec name_of t =
    match t.desc with
    | Bottom -> "bot"
    | Var x -> Lid.name x
    | Local (_, t) -> name_of t
    | Tuple [] -> "nil"
    | Tuple ts ->
        if List.length ts <= 3 then String.join "__" (List.map name_of ts)
        else String.join "__" (List.map name_of (List.take 2 ts) @ [ "etc" ])
    | Proj (i, t) ->
        let n = tuple_num t.typ in
        let names = String.split_on_string ~by:"__" (name_of t) in
        if n = Some (List.length names) && List.nth names i <> "" && n = Some 4 => (i <> 3) then
          List.nth names i
        else name_of t ^ "_" ^ string_of_int i
    | App ({ desc = Var f }, _) ->
        let s = Lid.name f in
        let s =
          try
            let l = String.rindex s '.' + 1 in
            String.sub s l (String.length s - l)
          with Not_found -> s
        in
        "r_" ^ s
    | _ -> var_name_of @@ elim_tattr t.typ
  in
  let name = name_of t in
  if is_module t then String.capitalize_ascii name else name

let new_var_of_term t = Id.new_var ~name:(var_name_of_term t) t.typ

let rec var_name_of_pattern p =
  match p.pat_desc with
  | PAny -> "u"
  | PVar x -> Id.name x
  | PTuple [] -> "nil"
  | PTuple ps -> String.join "__" @@ List.map var_name_of_pattern ps
  | PNil -> "nil"
  | _ -> var_name_of p.pat_typ

let rec var_name_of_pattern_short p =
  match p.pat_desc with
  | PAny -> "u"
  | PVar x -> Id.name x
  | PTuple [] -> "u"
  | PTuple ps -> String.join "" @@ List.map var_name_of_pattern_short @@ List.take 3 ps
  | PNil -> "e"
  | _ -> var_name_of p.pat_typ

let new_var_of_pattern p =
  let name = var_name_of_pattern p in
  let name =
    if String.length name < Flag.long_name_len then name else var_name_of_pattern_short p
  in
  Id.new_var ~name p.pat_typ

let merge_tattrs attr1 attr2 =
  let attrs =
    let eq x y =
      match (x, y) with
      | TAPred _, TAPred _ -> true
      | TAPureFun, TAPureFun -> true
      | TARefPred _, TARefPred _ -> true
      | TAId (s1, _), TAId (s2, _) -> s1 = s2
      | _ -> false
    in
    List.classify ~eq List.Set.(attr1 + attr2)
  in
  let merge a1 a2 =
    match a1 with
    | None -> Some a2
    | Some a1 -> (
        match (a1, a2) with
        | TAPred (x1, ps1), TAPred (x2, ps2) ->
            let merge_preds ps1 ps2 =
              let aux p ps = if List.exists (same_term p) ps then ps else p :: ps in
              List.fold_right aux ps1 ps2
            in
            let ps2' = List.map (subst_var x2 x1) ps2 in
            Some (TAPred (x1, merge_preds ps1 ps2'))
        | TARefPred (x1, p1), TARefPred (x2, p2) ->
            let p2' = subst_var x2 x1 p2 in
            let p = if same_term p1 p2' then p1 else make_and p1 p2' in
            Some (TARefPred (x1, p))
        | TAPureFun, TAPureFun -> Some TAPureFun
        | TAId _, TAId _ ->
            warning "merge TAId";
            None
        | _ -> assert false)
  in
  List.filter_map (List.fold_left merge None) attrs

(* TODO: this should be removed *)
let rec merge_typ typ1 typ2 =
  match (typ1, typ2) with
  | TVar (_, { contents = Some typ1 }, _), typ2 | typ1, TVar (_, { contents = Some typ2 }, _) ->
      merge_typ typ1 typ2
  | TVar (_, { contents = None }, _), _ -> typ2
  | _, TVar (_, { contents = None }, _) -> typ1
  | _ when typ1 = typ_unknown -> typ2
  | _ when typ2 = typ_unknown -> typ1
  | TBase b1, TBase b2 when b1 = b2 -> TBase b1
  | TAttr (attr1, typ1), TAttr (attr2, typ2) ->
      _TAttr (merge_tattrs attr1 attr2) (merge_typ typ1 typ2)
  | TAttr (attr, typ'), typ | typ, TAttr (attr, typ') -> _TAttr attr (merge_typ typ typ')
  | TFuns (xs1, typ1), TFuns (xs2, typ2) when List.compare_lengths xs1 xs2 = 0 ->
      let xs =
        List.map2
          (fun x1 x2 -> Id.new_var ~name:(Id.name x1) @@ merge_typ (Id.typ x1) (Id.typ x2))
          xs1 xs2
      in
      TFuns (xs, merge_typ typ1 typ2)
  | TFun (x1, typ1), TFun (x2, typ2) ->
      let x_typ = merge_typ (Id.typ x1) (Id.typ x2) in
      let x = Id.new_var ~name:(Id.name x1) x_typ in
      let typ = merge_typ (subst_type_var x1 x typ1) (subst_type_var x2 x typ2) in
      TFun (x, typ)
  | TConstr (c1, typs1), TConstr (c2, typs2) when Path.(c1 = c2) ->
      TConstr (c1, List.map2 merge_typ typs1 typs2)
  | TTuple xs1, TTuple xs2 when List.compare_lengths xs1 xs2 = 0 ->
      let aux x1 x2 xs =
        let x = Id.set_typ x1 @@ merge_typ (Id.typ x1) (Id.typ x2) in
        List.map (Id.map_typ @@ subst_type_var x2 x1) @@ (x :: xs)
      in
      TTuple (List.fold_right2 aux xs1 xs2 [])
  | TVariant (poly1, rows1), TVariant (poly2, rows2) ->
      assert (poly1 = poly2);
      List.iter2 (fun row1 row2 -> assert (row1.row_constr = row2.row_constr)) rows1 rows2;
      TVariant (poly1, rows1)
  | TRecord fields1, TRecord fields2 when List.compare_lengths fields1 fields2 = 0 ->
      let fields =
        List.map2
          (fun (s1, (f1, typ1)) (s2, (f2, typ2)) ->
            assert (s1 = s2 && f1 = f2);
            (s1, (f1, merge_typ typ1 typ2)))
          fields1 fields2
      in
      TRecord fields
  | _ ->
      Format.eprintf "typ1:%a, typ2:%a@." Print.typ typ1 Print.typ typ2;
      assert false

let make_if ?typ t1 t2 t3 =
  assert (Flag.Debug.check_typ => can_unify t1.typ Ty.bool);
  if Flag.Debug.check_typ && (not @@ can_unify t2.typ t3.typ) then (
    Format.eprintf "%a <=/=> %a@." Print.typ t2.typ Print.typ t3.typ;
    assert false);
  match t1.desc with
  | Const True -> t2
  | Const False -> t3
  | _ when has_safe_attr t2 && same_term' t2 t3 -> t2
  | _ when t2.desc = Const True && t3.desc = Const False -> t1
  | _ when same_term t2 t3 -> make_seq t1 t2
  | _ ->
      let typ = Option.default_delayed (fun _ -> merge_typ t2.typ t3.typ) typ in
      make (If (t1, t2, t3)) typ ~attr:(make_attr [ t1; t2; t3 ])

let make_assert ?loc ?(force = false) t =
  if !Flag.Method.only_specified && not force then make_ignore t
  else make_if t unit_term (make_fail_unit loc)

let make_assume t1 t2 = make_if t1 t2 (make_bottom t2.typ)

let make_rand typ =
  let ty = Ty.(sfun unit typ) in
  make (Const (Rand (typ, false))) ty

let rec make_use_var x t = make_use_lid (LId x) t

and make_use_lid x t =
  let ty = flatten @@ elim_tattr @@ Lid.typ x in
  if not (has_tfun ty) then t
  else
    let tx = make_var_lid x in
    match ty with
    | TBase _ | TVar _ -> assert false
    | TFun (y, ty) ->
        let r = Id.new_var ~name:"r" ty in
        make_let_s
          [
            ( r,
              make_if (make_rand_unit Ty.bool) (make_rand_unit ty)
                (make_app tx [ make_rand_unit (Id.typ y) ]) );
          ]
        @@ make_use_var r t
    | TFuns _ -> unsupported "%s" __FUNCTION__
    | TTuple xs ->
        let defs = List.mapi (fun i x' -> (x', make_proj i tx)) xs in
        make_lets_s defs @@ List.fold_right make_use_var xs t
    | TVariant (poly, rows) ->
        let pats =
          rows
          |> List.map (fun { row_constr; row_args } ->
                 let xs = List.map Id.new_var row_args in
                 let args = List.map make_pvar xs in
                 let desc = PConstr (poly <> VNonPoly, LId row_constr, args) in
                 (make_pattern desc ty, List.fold_right make_use_var xs unit_term))
        in
        make_seq (make_match tx pats) t
    | _ ->
        Flag.Abstract.under
        @@ Format.asprintf "the functions in values of type '%a' are safe" Print.typ ty;
        t

and make_rand_unit ?(use = true) typ =
  let mk = make_rand_unit ~use in
  match typ with
  | TBase TUnit -> unit_term
  | TBase TBool -> make_eq (mk Ty.int) (make_int 0)
  | TTuple [] -> make_tuple []
  | TTuple tys -> make_tuple @@ List.map (Id.typ |- mk) tys
  | TAttr (_, TFun _) when is_raise_tfun typ ->
      let ty_exn, x, ty = Option.get @@ decomp_raise_tfun typ in
      let t1 = mk Ty.bool in
      let t2 = make_raise (mk ty_exn) ~typ:ty in
      let t3 = mk ty in
      make_if t1 t2 t3 |> use ^> make_use_var x |> make_fun x
  | TFun (x, ty) -> mk ty |> use ^> make_use_var x |> make_fun x
  | TAttr (_, ty) -> mk ty
  | TModSig sgn ->
      sgn
      |> List.map (function
           | Sig_type decl -> Decl_type decl
           | Sig_value x -> Decl_let [ (x, (mk -| Id.typ) x) ]
           | Sig_ext ext -> Type_ext (Ext_type ext))
      |> make_module ~typ
  | TModLid _ -> [%unsupported]
  | _ -> make (App (make_rand typ, [ unit_term ])) typ ~attr:safe_attr

let make_use t1 t2 =
  match t1.desc with
  | Var x -> make_use_lid x t2
  | _ ->
      let x = new_var_of_term t1 in
      make_let_s [ (x, t1) ] (make_use_var x t2)

let make_rand_unit ?(expand = true) ?(use = true) ty =
  let add = add_attrs safe_attr in
  if ty = Ty.unit then unit_term
  else if expand then add @@ make_rand_unit ~use ty
  else add @@ make_app (make_rand ty) [ unit_term ]

let make_rand_cps typ =
  make (Const (Rand (typ, true))) [%ty: unit -> ('typ -> result) -> result] ~attr:const_attr

let make_randint_cps b = make_rand_cps Ty.int |> b ^> add_attr AAbst_under
let randint_term = make_rand Ty.int
let randint_unit_term = make_rand_unit Ty.int
let randbool_unit_term = make_rand_unit Ty.bool

let is_randint_unit t =
  match t.desc with
  | App (t1, [ { desc = Const Unit } ]) -> t1.desc = randint_term.desc
  | _ -> false

let is_randbool_unit t =
  match t.desc with
  | BinOp ((Eq | Leq | Geq | Lt | Gt), t, { desc = Const _ })
  | BinOp ((Eq | Leq | Geq | Lt | Gt), { desc = Const _ }, t) ->
      is_randint_unit t
  | _ -> false

let is_rand_unit ?(deep = false) t =
  match t.desc with
  | App
      ( { desc = Const (Rand (_, false)) },
        [ ({ desc = Const Unit } | { desc = Var _; typ = TBase TUnit }) ] ) ->
      true
  | _ -> if deep then same_term t (make_rand_unit ~expand:true t.typ) else false

let make_br t2 t3 = make_if randbool_unit_term t2 t3

let make_brs ts =
  if ts = [] then invalid_arg "Term_util.make_brs";
  List.reduce_right make_br ts

let make_either_ty ty1 ty2 = Ty.(tuple [ bool; ty1; ty2 ])
let make_left t ty = make_tuple [ true_term; t; make_default_term ty ]
let make_right ty t = make_tuple [ true_term; make_default_term ty; t ]
let make_is_left t = make_proj 0 t
let make_get_left t = make_proj 1 t
let make_get_right t = make_proj 2 t

let rec get_top_funs acc = function
  | { desc = Local (Decl_let defs, t) } ->
      let acc' = List.fold_left (fun acc (f, _) -> f :: acc) acc defs in
      get_top_funs acc' t
  | _ -> acc

let get_top_funs = get_top_funs []

let has_no_effect =
  let col = Col.make true ( && ) in
  col.term <-
    (fun t ->
      match t.desc with
      | Const _ -> true
      | Var _ -> true
      | Fun _ -> true
      | App (t1, ts) when List.mem TAPureFun (fst (decomp_tattr t1.typ)) ->
          col.term t1 && List.for_all col.term ts
      | App _ -> false
      | Local (Decl_let bindings, t) -> col.term t && List.for_all (snd |- col.term) bindings
      | Field _ -> false
      | SetField _ -> false
      | Raise _ -> false
      | Bottom -> false
      | Ref _ -> false
      | Deref _ -> false
      | SetRef _ -> false
      | _ -> col.desc t.desc);
  col.term

let make_safe_div ?loc t1 t2 =
  let t2' =
    let make_check t = make_seq (make_assert ?loc (make_neq t (make_int 0))) t in
    if has_no_effect t2 then make_check t2
    else
      let x = Id.new_var Ty.int in
      make_let [ (x, t2) ] (make_check (make_var x))
  in
  make_div t1 t2'

let is_const_or_var = Is._Const ||| Is._Var

let rec is_simple_aexp t =
  if elim_tattr t.typ <> Ty.int then false
  else
    match t.desc with
    | Const _ -> true
    | Var _ -> true
    | BinOp (_, t1, t2) -> is_simple_aexp t1 && is_simple_aexp t2
    | _ -> false

and is_simple_bexp t =
  if elim_tattr t.typ <> Ty.bool then false
  else
    match t.desc with
    | Const _ -> true
    | Var _ -> true
    | BinOp (_, t1, t2) ->
        (is_simple_bexp t1 && is_simple_bexp t2)
        || (is_simple_aexp t1 && is_simple_aexp t2)
        || (is_const_or_var t1 && is_const_or_var t2)
    | Not t -> is_simple_bexp t
    | _ -> false

let make_let' ?(subst_if_var = false) t1 make_t2 =
  match Val._Var t1 with
  | Some (LId x) when subst_if_var -> make_t2 (LId x)
  | _ ->
      let x = new_var_of_term t1 in
      make_let [ (x, t1) ] (make_t2 (LId x))

let make_let_subst_if_var x t1 t2 =
  match t1.desc with Var _ -> subst x t1 t2 | _ -> make_let [ (x, t1) ] t2

let col_same_term =
  let col = Col2.make [] ( @@@ ) in
  col.term <-
    (fun t1 t2 ->
      let b = try same_term t1 t2 with _ -> false in
      if b then [ t2 ] else col.term_rec t1 t2);
  col.term

let col_info_id =
  let col = Col.make [] ( @@@ ) in
  col.attr <- List.filter_map (function AInfo (Id x) -> Some x | _ -> None);
  col.term

(* [t1 |-> x] *)
let subst_rev =
  let tr = Tr2.make () in
  tr.term <-
    (fun (t1, fv, x) t2 ->
      if same_term' t1 t2 || t1 = t2 then make_var x
      else
        match t2.desc with
        | Fun (x, _) when Id.List.mem x fv -> t2
        | Match (t1, pats)
          when List.exists
                 (fst |- get_bv_pat |- List.Set.inter ~eq:Id.eq fv |- List.is_empty |- not)
                 pats ->
            let desc = Match (tr.term_rec (t1, fv, x) t2, pats) in
            make desc t2.typ
        | _ -> set_afv_shallowly @@ tr.term_rec (t1, fv, x) t2);
  fun ?(check_capture = false) t1 x t2 ->
    let fv = if check_capture then get_fv t1 else [] in
    tr.term (t1, fv, x) t2

(* replace t1 with t2 in t3 *)
let replace_term t1 t2 t3 =
  let x = Id.new_var t1.typ in
  subst x t2 @@ subst_rev t1 x t3

let is_bottom_def f t =
  let xs, t = decomp_funs t in
  match (xs, t.desc) with
  | _ :: _, App ({ desc = Var g }, ts) -> Lid.(LId f = g) && List.for_all has_no_effect ts
  | _ -> false

let rec decomp_seq t =
  if is_seq t then
    match t.desc with
    | Local (Decl_let [ (_, t1) ], t2) -> decomp_seq t1 @ decomp_seq t2
    | _ -> assert false
  else [ t ]

let rec decomp_bexp t =
  match t.desc with
  | BinOp ((And | Or), t1, t2) -> decomp_bexp t1 @ decomp_bexp t2
  | Not t1 -> decomp_bexp t1
  | _ -> [ t ]

let var_of_term t = match t.desc with Var x -> x | _ -> invalid_arg "var_of_term"

let int_of_term t =
  match t.desc with Const (Int n) -> n | _ -> invalid_arg "int_of_term (%a)" Print.term t

let bool_of_term t =
  match t.desc with
  | Const True -> true
  | Const False -> false
  | _ -> invalid_arg "bool_of_term (%a)" Print.term t

let pair_of_term t =
  match t.desc with Tuple [ t1; t2 ] -> (t1, t2) | _ -> invalid_arg "pair_of_term"

let tuple_of_term t = match t.desc with Tuple ts -> ts | _ -> invalid_arg "tuple_of_term"

let rec list_of_term t =
  match t.desc with
  | Nil -> []
  | Cons (t1, t2) -> t1 :: list_of_term t2
  | _ -> invalid_arg "list_of_term"

let subst_tconstr_map, subst_tconstr_map_typ =
  let tr = Tr2.make () in
  let check decls (path, _) = List.exists (fst |- Id.( = ) path) decls in
  let has_common map decls = List.exists (check decls) map in
  let filter map decls = List.filter_out (check decls) map in
  tr.desc <-
    (fun (map : (tconstr * _) list) desc ->
      match desc with
      | Local (Decl_type decls, _) when has_common map decls ->
          let map' = filter map decls in
          if map' = [] then desc else tr.desc_rec map' desc
      | Module decls ->
          let _, decls =
            List.L.fold_left_map decls ~init:map ~f:(fun map' decl ->
                match (map', decl) with
                | [], _ -> (map', decl)
                | _, Decl_type decls when has_common map decls -> (filter map decls, decl)
                | _ -> (map, tr.decl map decl))
          in
          Module decls
      | _ -> tr.desc_rec map desc);
  tr.typ <-
    (fun map ty ->
      match ty with
      | TConstr (LId s, tys) when Id.List.mem_assoc s map ->
          let tys' = List.map (tr.typ map) tys in
          subst_tconstr_params tys' (Id.List.assoc s map)
      | _ -> tr.typ_rec map ty);
  (tr.term, tr.typ)

let subst_tconstr_label_map, subst_tconstr_label_map_typ =
  let tr = Tr2.make () in
  let check decls (path, _) = List.exists (fst |- Path._LId |- Path.( = ) path) decls in
  let has_common map decls = List.exists (check decls) map in
  let filter map decls = List.filter_out (check decls) map in
  tr.desc <-
    (fun map desc ->
      match desc with
      | Local (Decl_type decls, _) when has_common map decls ->
          let map' = filter map decls in
          if map' = [] then desc else tr.desc_rec map' desc
      | Module decls ->
          let _, decls =
            List.L.fold_left_map decls ~init:map ~f:(fun map' decl ->
                if map' = [] then (map', decl)
                else
                  match decl with
                  | Decl_type decls when has_common map decls -> (filter map decls, decl)
                  | _ -> (map, tr.decl map decl))
          in
          Module decls
      | _ -> tr.desc_rec map desc);
  tr.typ <-
    (fun map ty ->
      match ty with
      | TConstr (s, params) when List.mem_assoc ~eq:Path.eq s map ->
          let s' = List.assoc ~eq:Path.eq s map in
          let params' = List.map (tr.typ map) params in
          TConstr (s', params')
      | _ -> tr.typ_rec map ty);
  let tr_map = List.map (Pair.map_same Path._LId) in
  ( (fun map t -> if map = [] then t else tr.term (tr_map map) t),
    fun map ty -> if map = [] then ty else tr.typ (tr_map map) ty )

let subst_tconstr s ty t = subst_tconstr_map [ (s, ty) ] t
let subst_tconstr_typ s ty1 ty2 = subst_tconstr_map_typ [ (s, ty1) ] ty2

let subst_constr_map =
  let tr = Tr2.make () in
  let has_common map decls =
    List.exists (Path._LId |- List.mem_assoc -$- map) @@ constrs_in_declaration decls
  in
  let filter map decls =
    let constrs = constrs_in_declaration decls in
    List.filter_out (fun (c, _) -> List.exists (fun c' -> Path.(c = LId c')) constrs) map
  in
  tr.desc <-
    (fun map desc ->
      match desc with
      | Constr (false, s, ts) ->
          let s' = List.subst ~eq:Path.eq map s in
          Constr (false, s', List.map (tr.term map) ts)
      | Local (Decl_type decls, _) when has_common map decls ->
          let map' = filter map decls in
          if map' = [] then desc else tr.desc_rec map' desc
      | Local (Decl_let [ (m, t1) ], _t2) when is_module t1 ->
          let constrs = constrs_in_module ~add_prefix:true ~env:[] m in
          (* TODO: Check [] is ok *)
          if List.exists (List.mem_assoc -$- map) constrs then unsupported "subst_constr_map"
          else tr.desc_rec map desc
      | Module decls ->
          let _, decls_rev =
            let aux (map', acc_rev) decl =
              let map', decl' =
                if map' = [] then (map', decl)
                else
                  match decl with
                  | Decl_type decls when has_common map decls -> (filter map decls, decl)
                  | _ -> (map, tr.decl map decl)
              in
              (map', decl' :: acc_rev)
            in
            List.fold_left aux (map, []) decls
          in
          Module (List.rev decls_rev)
      | _ -> tr.desc_rec map desc);
  tr.pat <-
    (fun map p ->
      let p' = tr.pat_rec map p in
      let pat_desc =
        match p'.pat_desc with
        | PConstr (false, s, ps) ->
            let s' = List.subst ~eq:Path.eq map s in
            PConstr (false, s', ps)
        | desc -> desc
      in
      make_pattern pat_desc p'.pat_typ);
  tr.typ <- Fun.snd;
  (* TODO *)
  fun map t -> tr.term map t

let subst_constr s s' t = subst_constr_map [ (s, s') ] t

let subst_field_map =
  let tr = Tr2.make () in
  let has_common map decls =
    fields_in_declaration decls
    |> List.exists (fun f -> List.exists (fun (f', _) -> Path.(LId f' = f)) map)
  in
  let filter map decls =
    let fields = fields_in_declaration decls in
    List.filter_out (fst |- Path._LId |- List.mem ~eq:Path.eq -$- fields) map
  in
  tr.desc <-
    (fun (map : (label * label) list) desc ->
      match desc with
      | Field (t, s) ->
          let s' = Id.List.subst map s in
          Field (tr.term map t, s')
      | SetField (t1, s, t2) ->
          let s' = Id.List.subst map s in
          SetField (tr.term map t1, s', tr.term map t2)
      | Record fields ->
          let fields' = List.map (fun (s, t) -> (Id.List.subst map s, tr.term map t)) fields in
          Record fields'
      | Local (Decl_type decls, _) when has_common map decls ->
          let map' = filter map decls in
          if map' = [] then desc else tr.desc_rec map' desc
      | Local (Decl_let [ (m, t1) ], _t2) when is_module t1 ->
          let constrs = constrs_in_module ~add_prefix:true ~env:[] m in
          (* TODO: Check [] is ok *)
          if List.exists (fun f -> List.exists (fun (f', _) -> Path.(LId f' = f)) map) constrs then
            unsupported "subst_constr_map"
          else tr.desc_rec map desc
      | Module decls ->
          let _, decls_rev =
            let aux (map', acc_rev) decl =
              let map', decl' =
                if map' = [] then (map', decl)
                else
                  match decl with
                  | Decl_type decls when has_common map decls -> (filter map decls, decl)
                  | _ -> (map, tr.decl map decl)
              in
              (map', decl' :: acc_rev)
            in
            List.fold_left aux (map, []) decls
          in
          Module (List.rev decls_rev)
      | _ -> tr.desc_rec map desc);
  tr.pat <-
    (fun map p ->
      let p' = tr.pat_rec map p in
      let pat_desc =
        match p'.pat_desc with
        | PRecord fields ->
            let fields' = Fmap.(list (fst (Id.List.subst map))) fields in
            PRecord fields'
        | desc -> desc
      in
      make_pattern pat_desc p'.pat_typ);
  tr.typ <-
    (fun map ty ->
      match tr.typ_rec map ty with
      | TRecord fields ->
          let fields' = Fmap.(list (fst (Id.List.subst map))) fields in
          TRecord fields'
      | ty -> ty);
  tr.term

let subst_field s s' t = subst_field_map [ (s, s') ] t

let subst_tconstr_map_decls (map : (tconstr * _) list) decls =
  let aux ((map : (tconstr * _) list), acc_rev) decl =
    if map = [] then (map, decl :: acc_rev)
    else
      match decl with
      | Decl_let defs ->
          let defs' =
            List.map
              (Pair.map (Id.map_typ (subst_tconstr_map_typ map)) (subst_tconstr_map map))
              defs
          in
          (map, Decl_let defs' :: acc_rev)
      | Decl_type decls ->
          let map' = List.filter_out (fun (c, _) -> List.mem_assoc c decls) map in
          let decls' = List.map (Pair.map_snd (Pair.map_snd (subst_tconstr_map_typ map'))) decls in
          (map', Decl_type decls' :: acc_rev)
      | Decl_multi _ -> [%unsupported]
      | Type_ext _ -> [%unsupported]
      | Include _ -> [%unsupported]
  in
  List.fold_left aux (map, []) decls |> snd |> List.rev

let subst_constr_map_decls map decls =
  let aux (map, acc_rev) decl =
    if map = [] then (map, decl :: acc_rev)
    else
      match decl with
      | Decl_let defs ->
          let defs' = List.map (Pair.map_snd (subst_constr_map map)) defs in
          (map, Decl_let defs' :: acc_rev)
      | Decl_type decls ->
          let constrs = constrs_in_declaration decls in
          let map' =
            List.filter_out (fun (c, _) -> List.exists (fun c' -> Path.(LId c' = c)) constrs) map
          in
          (map', decl :: acc_rev)
      | Decl_multi _ -> [%unsupported]
      | Type_ext _ -> [%unsupported]
      | Include _ -> [%unsupported]
  in
  List.fold_left aux (map, []) decls |> snd |> List.rev

let subst_field_map_decls map decls =
  let aux (map, acc_rev) decl =
    if map = [] then (map, decl :: acc_rev)
    else
      match decl with
      | Decl_let defs ->
          let defs' = List.map (Pair.map_snd (subst_field_map map)) defs in
          (map, Decl_let defs' :: acc_rev)
      | Decl_type decls ->
          let fields = fields_in_declaration decls in
          let map' = List.filter_out (fst |- Path._LId |- List.mem -$- fields) map in
          (map', decl :: acc_rev)
      | Decl_multi _ -> [%unsupported]
      | Type_ext _ -> [%unsupported]
      | Include _ -> [%unsupported]
  in
  List.fold_left aux (map, []) decls |> snd |> List.rev

let subst_map_decls map decls =
  let aux (map, acc_rev) decl =
    if map = [] then (map, decl :: acc_rev)
    else
      match decl with
      | Decl_let defs ->
          let map' = List.filter_out (fst |- Id.List.mem_assoc -$- defs) map in
          let defs' = List.map (Pair.map_snd (subst_map map')) defs in
          (map', Decl_let defs' :: acc_rev)
      | _ -> (map, decl :: acc_rev)
  in
  List.fold_left aux (map, []) decls |> snd |> List.rev

let subst_decls x t decls = subst_map_decls [ (x, t) ] decls
let subst_var_map_decls map decls = subst_map_decls (List.map (Pair.map_snd make_var) map) decls

let alpha_rename_pred_share =
  let fld = Fold_tr.make () in
  let find x env =
    if List.mem_assoc x env then (env, List.assoc x env)
    else
      let y = Id.new_int () in
      ((x, y) :: env, y)
  in
  fld.typ <-
    (fun env ty ->
      match ty with
      | TAttr (attr, ty1) ->
          let env, ty1' = fld.typ env ty1 in
          let env, attr' =
            let aux a (env, acc) =
              let env', a' =
                match a with
                | TAId (s, x) when s = label_pred_share ->
                    let env', y = find x env in
                    (env', TAId (s, y))
                | TAPredShare x ->
                    let env', y = find x env in
                    (env', TAPredShare y)
                | _ -> (env, a)
              in
              (env', a' :: acc)
            in
            List.fold_right aux attr (env, [])
          in
          (env, _TAttr attr' ty1')
      | _ -> fld.typ_rec env ty);
  fld.typ [] |- snd

(* for predicate sharing *)
let subst_tconstr_with_copy =
  let tr = Tr2.make () in
  tr.typ <-
    (fun (s, (params, ty1)) ty2 ->
      match ty2 with
      | TConstr (LId s', params') when s = s' ->
          alpha_rename_pred_share (subst_tconstr_params params' (params, ty1))
      | _ -> tr.typ_rec (s, (params, ty1)) ty2);
  Fun.curry tr.term

let rec get_last_definition prefix env def t =
  match t.desc with
  | Local (Decl_let bindings, t2) -> get_last_definition prefix env (Some (env, bindings)) t2
  | Local (Decl_type decls, t2) ->
      let env' =
        List.map
          (fun (c, (params, _)) -> (c, (params, TConstr (prefix (Type.LId c), params))))
          decls
        @@@ env
      in
      get_last_definition prefix env' def t2
  | Local (_, t2) -> get_last_definition prefix env def t2
  | Module _decls -> unsupported "get_last_definition"
  | Fun _ -> []
  | _ -> (
      match def with
      | None -> []
      | Some (_env', [ (m, { desc = Module decls }) ]) ->
          make_locals decls end_of_definitions
          |> get_last_definition (prefix |- Path.cons m) env None (* TODO: check env/env' *)
      | Some (env', bindings) ->
          let sbst = subst_tconstr_map_typ env' in
          Fmap.(list (fst (Lid._LId -| id_typ sbst))) bindings)

let get_last_definition t = get_last_definition Fun.id [] None t
let rec get_main t = match t.desc with Local (_, t2) -> get_main t2 | _ -> t
let count_occurrence x t = List.count Id.(( = ) x) @@ get_fv t

let get_id t =
  try List.find_map (function AId n -> Some n | _ -> None) t.attr
  with Not_found -> invalid_arg "get_id"

let get_id_option t = Option.try_with (fun () -> get_id t) (( = ) @@ Invalid_argument "get_id")

let get_id_map =
  let it = Iter2.make () in
  it.term <-
    (fun map t ->
      it.term_rec map t;
      Hashtbl.add map (get_id t) t);
  it.typ <- Fun.ignore2;
  fun t ->
    let map = Hashtbl.create 0 in
    it.term map t;
    map

let rec decomp_type_decls t =
  match t.desc with
  | Local (Decl_type tys, t1) ->
      let decls, t1' = decomp_type_decls t1 in
      (tys :: decls, t1')
  | _ -> ([], t)

let rec decomp_prog t =
  match t.desc with
  | Local (Decl_let bindings, t') ->
      let defs, main = decomp_prog t' in
      (bindings :: defs, main)
  | _ -> ([], t)

let from_fpat_const (c : Fpat.Const.t) =
  match c with
  | Unit -> unit_term
  | True -> true_term
  | False -> false_term
  | Int n -> make_int n
  | _ -> unsupported "Term_util.from_fpat_const"

let from_fpat_idnt x = Id.of_string (Fpat.Idnt.string_of x) typ_unknown

let decomp_binop (t : Fpat.Term.t) =
  match t with
  | Const c -> (
      match c with
      | Lt _ -> Some make_lt
      | Gt _ -> Some make_gt
      | Leq _ -> Some make_leq
      | Geq _ -> Some make_geq
      | Eq _ -> Some make_eq
      | Add _ -> Some make_add
      | Sub _ -> Some make_sub
      | Mul _ -> Some make_mul
      | Div _ -> Some make_div
      | Neq _ -> Some make_neq
      | _ -> None)
  | _ -> None

let rec decomp_list t =
  match t.desc with
  | Nil -> Some []
  | Cons (t1, t2) -> Option.map (List.cons t1) @@ decomp_list t2
  | _ -> None

let is_list_literal t = None <> decomp_list t

let rec from_fpat_term (t : Fpat.Term.t) =
  match t with
  | Const c -> from_fpat_const c
  | Var x -> make_var (from_fpat_idnt x)
  | App (App (f, t1), t2) when Option.is_some @@ decomp_binop f ->
      let make = Option.get @@ decomp_binop f in
      let t1' = from_fpat_term t1 in
      let t2' = from_fpat_term t2 in
      make t1' t2'
  | App (Const Not, t) -> make_not (from_fpat_term t)
  | t ->
      Fpat.Term.pr Format.std_formatter t;
      assert false

let from_fpat_formula t = from_fpat_term @@ Fpat.Formula.term_of t

let col_typ_var =
  let col = Col.make [] ( @ ) in
  col.typ <-
    (fun typ ->
      match typ with TVar (_, ({ contents = None } as r), _) -> [ r ] | _ -> col.typ_rec typ);
  List.unique ~eq:( == ) -| col.term

let col_id =
  let col = Col.make [] ( @@@ ) in
  col.attr <- (fun attr -> List.filter_map (function AId n -> Some n | _ -> None) attr);
  col.typ <- Fun.const [];
  List.unique -| col.term

let col_tid =
  let col = Col.make [] ( @@@ ) in
  col.typ <-
    (fun ty ->
      let acc = col.typ_rec ty in
      match ty with
      | TAttr (attr, _) ->
          List.filter_map (function TAId (s, n) -> Some (s, n) | _ -> None) attr @@@ acc
      | _ -> acc);
  col.term <- Fun.const [];
  List.unique -| col.typ

let rec is_fail t =
  match t.desc with
  | Local (Decl_let [ (_, t) ], _) -> is_fail t
  | App ({ desc = Event ("fail", _) }, [ { desc = Const Unit } ]) -> true
  | _ -> false

let col_app_args =
  let col = Col2.make [] ( @ ) in
  col.desc <-
    (fun f desc ->
      match desc with
      | App ({ desc = Var g }, ts) when Lid.(f = g) -> [ ts ]
      | _ -> col.desc_rec f desc);
  col.term

let col_non_fixed_args =
  let col = Col2.make [] ( @ ) in
  col.desc <-
    (fun (f, xs) desc ->
      match desc with
      | App ({ desc = Var g }, ts) when Lid.(f = g) ->
          let check (i, x) =
            match List.nth ts i with
            | { desc = Var y } when Lid.(x = y) -> []
            | t -> x :: col.term (f, xs) t
            | exception Invalid_argument _ -> [ x ]
          in
          List.flatten_map check xs
      | _ -> col.desc_rec (f, xs) desc);
  fun f xs t ->
    let xs' = List.mapi Pair.pair xs in
    col.term (f, xs') t

let find_fixed_args f xs t =
  let non_fixed = col_non_fixed_args f xs t in
  List.filter_out (List.mem ~eq:Lid.eq -$- non_fixed) xs

(* Assume that modules are extracted *)
let col_type_decl : term -> (Type.constr * (typ list * typ)) list list =
  let ( ++ ) (xs1, ys1) (xs2, ys2) = (xs1 @@@ xs2, ys1 @@@ ys2) in
  let col = Col.make ([], []) ( ++ ) in
  let col_desc desc =
    match desc with
    | Local (Decl_type decls, t1) -> ([ decls ], []) ++ col.term t1
    | Local (Type_ext (Ext_type (s, ext)), t1) -> ([], [ (s, ext) ]) ++ col.term t1
    | _ -> col.desc_rec desc
  in
  col.desc <- col_desc;
  fun t ->
    let declss, exts = col.term t in
    let declss =
      if (not (List.exists (List.mem_assoc (Path.id_of C.exn)) declss)) && List.mem_assoc C.exn exts
      then [ (Path.id_of C.exn, ([], TVariant (VNonPoly, []))) ] :: declss
      else declss
    in
    let declss =
      List.map
        (List.map (function s, (ps, TOpen) -> (s, (ps, TVariant (VNonPoly, []))) | decl -> decl))
        declss
    in
    List.L.fold_left ~init:declss exts
      ~f:(fun (declss : _ Type.declaration list) (p, (params, row)) ->
        let s = Path.id_of p in
        let row =
          match row.ext_row_path with
          | LId id ->
              {
                row_constr = Id.set_typ id ();
                row_args = row.ext_row_args;
                row_ret = row.ext_row_ret;
              }
          | _ -> [%unsupported]
        in
        if List.exists (Id.List.mem_assoc s) declss then
          declss
          |> List.map (fun decls ->
                 try
                   decls
                   |> Id.List.assoc_map s (fun pty ->
                          match apply_tconstr pty params with
                          | TVariant (VNonPoly, rows) -> (params, TVariant (VNonPoly, row :: rows))
                          | _ -> assert false)
                   |> snd
                 with Not_found -> decls)
        else
          let rows =
            if C.is_exn p then []
            else [ { row_constr = Id.add_name_prefix "Other_" s; row_args = []; row_ret = None } ]
          in
          [ (s, (params, TVariant (VNonPoly, row :: rows))) ] :: declss)

let col_exn_typs =
  let col = Col.make [] ( @@@ ) in
  col.desc <-
    (fun desc ->
      match desc with
      | Raise t -> [ t.typ ]
      | TryWith (_, { typ = TFun (x, _) }) -> [ Id.typ x ]
      | _ -> col.desc_rec desc);
  col.typ <- (fun _ -> []);
  col.term

let find_exn_typ t =
  match t |> col_type_decl |> List.flatten |> Id.List.assoc_opt (Path.id_of C.exn) with
  | Some ([], ty) -> Some ty
  | Some _ -> assert false
  | None -> List.hd_opt @@ col_exn_typs t

let trans_if =
  let tr = Tr2.make () in
  tr.term <- (fun trans t2 -> match trans t2 with None -> tr.term_rec trans t2 | Some t2' -> t2');
  tr.term

let trans_if_desc =
  let tr = Tr2.make () in
  tr.desc <-
    (fun trans desc -> match trans desc with None -> tr.desc_rec trans desc | Some desc' -> desc');
  tr.term

let get_max_var_id =
  let col = Col.make (-1) max in
  col.term <-
    (fun t ->
      match t.desc with
      | Var (LId x) -> max (Id.id x) (Id.id @@ Id.of_string (Id.name x) typ_unknown)
      | _ -> col.term_rec t);
  col.term

let rec effect_of_typ ty =
  match ty with
  | TAttr (attr, ty') ->
      attr
      |> List.find_map_opt (function TAEffect e -> Some e | _ -> None)
      |> Option.default_delayed (fun () -> try effect_of_typ ty' with Invalid_argument _ -> [])
  | _ ->
      Format.eprintf "[%s] ty: %a@." __FUNCTION__ Print.typ ty;
      [%invalid_arg]

let effect_of t =
  try List.find_map (function AEffect e -> Some e | _ -> None) t.attr
  with Not_found ->
    Format.eprintf "[%s] %a@." __FUNCTION__ Print.term t;
    [%invalid_arg]

let has_pnondet =
  let it = Iter.make () in
  it.pat <- (fun p -> match p.pat_desc with PNondet -> raise Found | _ -> it.pat_rec p);
  Exception.does_raise ~exn:Found it.pat

let has_pwhen =
  let it = Iter.make () in
  it.pat <- (fun p -> match p.pat_desc with PWhen _ -> raise Found | _ -> it.pat_rec p);
  Exception.does_raise ~exn:Found it.pat

let has_event =
  let it = Iter.make () in
  it.desc <- (fun desc -> match desc with Event _ -> raise Found | _ -> it.desc_rec desc);
  Exception.does_raise ~exn:Found it.term

let has_type_decl =
  let it = Iter.make () in
  it.decl <-
    (fun decl -> match decl with Decl_type _ | Type_ext _ -> raise Found | _ -> it.decl_rec decl);
  Exception.does_raise ~exn:Found it.term

let rec copy_for_pred_share n m ty =
  let copy_var x = Id.typ x |> copy_for_pred_share n m |> Pair.map_same (Id.set_typ x) in
  match ty with
  | TBase _ | TTuple [] ->
      let attr1, attr2 =
        match m with
        | None -> ([ TAId (label_pred_share, n) ], [ TAPredShare n ])
        | Some m ->
            ( [ TAId (label_pred_share, n); TAPredShare m ],
              [ TAId (label_pred_share, m); TAPredShare n ] )
      in
      (_TAttr attr1 ty, _TAttr attr2 ty)
  | TVar _ -> unsupported "%s TVar" __FUNCTION__
  | TFun (x, ty') ->
      let x1, x2 = copy_var x in
      let ty1, ty2 = copy_for_pred_share n m ty' in
      (TFun (x1, ty1), TFun (x2, ty2))
  | TFuns _ -> unsupported "%s TFuns" __FUNCTION__
  | TTuple xs ->
      let xs1, xs2 = List.split_map copy_var xs in
      (TTuple xs1, TTuple xs2)
  | TConstr (constr, tys) ->
      let tys1, tys2 = List.split_map (copy_for_pred_share n m) tys in
      (TConstr (constr, tys1), TConstr (constr, tys2))
  | TVariant _ -> unsupported "%s TVariant" __FUNCTION__
  | TRecord _ -> unsupported "%s TRecord" __FUNCTION__
  | TAttr (attr, ty') ->
      let ty1, ty2 = copy_for_pred_share n m ty' in
      (_TAttr attr ty1, _TAttr attr ty2)
  | TModSig _ -> unsupported "%s TModSig" __FUNCTION__
  | TModLid _ -> unsupported "%s TModId" __FUNCTION__
  | TPackage _ -> unsupported "%s TPackage" __FUNCTION__
  | TPoly _ -> unsupported "%s TPoly" __FUNCTION__
  | TConstraint _ -> unsupported "%s TConstraint" __FUNCTION__
  | TOpen -> unsupported "%s TOpen" __FUNCTION__

let copy_for_pred_share bidir ty =
  copy_for_pred_share !!Id.new_int (if bidir then Some !!Id.new_int else None) ty

let get_pred_share ty =
  let col ty =
    let ( ++ ) env1 env2 =
      List.fold_left
        (fun env (x, paths2) ->
          List.modify_opt x (fun paths1 -> Some (paths2 @ Option.default [] paths1)) env)
        env1 env2
    in
    let insert x path env = [ (x, [ path ]) ] ++ env in
    let rec aux path ty =
      match ty with
      | TBase _ -> ([], [])
      | TVar _ -> unsupported "%s TVar" __FUNCTION__
      | TFun (x, ty') ->
          let ips1, pps1 = aux (path @ [ 0 ]) (Id.typ x) in
          let ips2, pps2 = aux (path @ [ 1 ]) ty' in
          (ips1 ++ ips2, pps1 ++ pps2)
      | TFuns _ -> unsupported "%s TFuns" __FUNCTION__
      | TTuple _ -> unsupported "%s TTuple" __FUNCTION__
      | TConstr _ -> ([], [])
      | TVariant _ -> unsupported "%s TVariant" __FUNCTION__
      | TRecord _ -> unsupported "%s TRecord" __FUNCTION__
      | TAttr (attr, ty') ->
          let ips, pps = aux path ty' in
          let aux' f acc =
            let aux'' a acc = match f a with None -> acc | Some n -> insert n path acc in
            List.fold_right aux'' attr acc
          in
          ( aux' (function TAId (s, n) when s = label_pred_share -> Some n | _ -> None) ips,
            aux' (function TAPredShare n -> Some n | _ -> None) pps )
      | TModSig _ -> unsupported "%s TModSig" __FUNCTION__
      | TModLid _ -> unsupported "%s TModId" __FUNCTION__
      | TPackage _ -> unsupported "%s TPackage" __FUNCTION__
      | TPoly _ -> unsupported "%s TPoly" __FUNCTION__
      | TConstraint _ -> unsupported "%s TConstraint" __FUNCTION__
      | TOpen -> unsupported "%s TOpen" __FUNCTION__
    in
    aux [] ty
  in
  let id_paths, pred_paths = col ty in
  let rec longest_common_prefix paths =
    if paths = [] || List.mem [] paths then ([], paths)
    else
      let x = List.hd @@ List.hd paths in
      if List.for_all (List.hd |- ( = ) x) paths then
        let paths' = List.map List.tl paths in
        let lcp, paths'' = longest_common_prefix paths' in
        (x :: lcp, paths'')
      else ([], paths)
  in
  let aux n =
    let paths1 = List.assoc n id_paths in
    let paths2 = List.assoc_opt n pred_paths in
    match paths2 with
    | None -> None
    | Some paths2 ->
        let prefix1, paths1' = longest_common_prefix paths1 in
        let prefix2, paths2' = longest_common_prefix paths2 in
        if List.Set.(paths2' <= paths1') then Some (prefix1, paths2', prefix2)
        else (* WORKAROUND: This case must not occur *)
          None
  in
  List.map fst id_paths |> List.unique |> List.filter_map aux

let set_id_counter_to_max = Id.set_counter -| succ -| get_max_var_id

let rec size_pattern p =
  let sum ps = List.fold_left (fun s p -> s + size_pattern p) 0 ps in
  match p.pat_desc with
  | PAny -> 1
  | PNondet -> 1
  | PVar _ -> 1
  | PAlias (p, _) -> 1 + size_pattern p
  | PConst t -> size t
  | PConstr (_, _, ps) -> 1 + sum ps
  | PNil -> 1
  | PCons (p1, p2) -> 1 + sum [ p1; p2 ]
  | PTuple ps -> 1 + sum ps
  | PRecord pats -> 1 + sum (List.map snd pats)
  | POr (p1, p2) -> 1 + sum [ p1; p2 ]
  | PNone -> 1
  | PSome p -> 1 + size_pattern p
  | PWhen (p, cond) -> 1 + size_pattern p + size cond
  | PLazy p -> 1 + size_pattern p
  | PEval (_, t, p) -> 3 + size t + size_pattern p

and size_declaration decl =
  match decl with
  | Decl_let bindings -> List.fold_left (fun s (_, t) -> s + size t) 0 bindings
  | _ -> 0

and size t =
  let sum ts = List.fold_left (fun s t -> s + size t) 0 ts in
  match t.desc with
  | End_of_definitions -> 1
  | Const _ -> 1
  | Var _ -> 1
  | Fun (_, t) -> 1 + size t
  | App (t1, _) -> 1 + size t1
  | If (t1, t2, t3) -> 1 + sum [ t1; t2; t3 ]
  | Local (decl, t2) -> 1 + size t2 + size_declaration decl
  | BinOp (_, t1, t2) -> 1 + sum [ t1; t2 ]
  | Not t1 -> 1 + size t1
  | Event _ -> 1
  | Record fields -> 1 + sum (List.map snd fields)
  | Field (t1, _) -> 1 + size t1
  | SetField (t1, _, t2) -> 1 + sum [ t1; t2 ]
  | Nil -> 1
  | Cons (t1, t2) -> 1 + sum [ t1; t2 ]
  | Constr (_, _, ts) -> 1 + sum ts
  | Match (t1, pats) ->
      1 + size t1 + List.fold_left (fun s (p, t) -> s + size_pattern p + size t) 0 pats
  | Raise t -> 1 + size t
  | TryWith (t1, t2) -> 1 + sum [ t1; t2 ]
  | Tuple ts -> 1 + sum ts
  | Proj (_, t) -> 1 + size t
  | Bottom -> 1
  | Ref t -> 1 + size t
  | Deref t -> 1 + size t
  | SetRef (t1, t2) -> 1 + sum [ t1; t2 ]
  | TNone -> 1
  | TSome t -> 1 + size t
  | Lazy t -> 1 + size t
  | Module decls -> 1 + List.fold_left (fun s decl -> s + size_declaration decl) 0 decls
  | Pack t -> 1 + size t
  | Unpack t -> 1 + size t
  | MemSet (t1, t2) -> 1 + sum [ t1; t2 ]
  | AddSet (t1, t2) -> 1 + sum [ t1; t2 ]
  | Subset (t1, t2) -> 1 + sum [ t1; t2 ]
  | Forall (_, t) -> 1 + size t
  | Exists (_, t) -> 1 + size t

let rec split_type_decl_and_body ?(force = false) t =
  match t.desc with
  | Local (Decl_type decl, t') ->
      let decls, body = split_type_decl_and_body ~force:false t' in
      if (not force) && has_type_decl body then invalid_arg "Trans.split_type_decl_and_body";
      (decl :: decls, body)
  | _ -> ([], t)

let rec split_decls_and_body t =
  match t.desc with
  | Local (decl, t') ->
      let decls, body = split_decls_and_body t' in
      (decl :: decls, body)
  | _ -> ([], t)

(*
let col_free_tconstr =
  let (++) (xs1,ys1) (xs2,ys2) = xs1@xs2, ys1@ys2 in
  let col = Col2.make ([],[]) (++) in
  let col_typ prefix ty =
    match ty with
    | TConstr(LId c,_tys) -> ([],[prefix c])
    | _ -> col.typ_rec prefix ty
  in
  let col_desc prefix desc =
    match desc with
    | Local(Decl_let[m,t1], t2) when is_module t1 ->
        let bound,occur = col.term (prefix |- Path.cons m) t1 in
        let aux = List.map prefix in
        (aux bound, aux occur) ++ col.term prefix t2
    | _ -> col.desc_rec prefix desc
  in
  let col_decl prefix decl =
    match decl with
    | Decl_type decls ->
        let bound = List.map (fst |- prefix) decls in
        List.fold_left (fun acc (_,(_,ty)) -> acc ++ col_typ prefix ty) (bound,[]) decls
    | _ -> col.decl_rec prefix decl
  in
  col.desc <- col_desc;
  col.decl <- col_decl;
  col.typ <- col_typ;
  fun t ->
    let bound,occur = col.term Path._LId t in
    List.Set.(occur - bound)
    |> List.sort_uniq compare
 *)
let set_mark t = List.iter (function AMark r -> r := true | _ -> ()) t.attr

let add_mark =
  let tr = Tr.make () in
  let tr_term t = tr.term_rec t |> add_attr (AMark (ref false)) in
  tr.term <- tr_term;
  tr.term

let catch_all ty_exn t =
  let e = Id.new_var ~name:"e" ty_exn in
  let handler_body =
    if !Flag.Method.target_exn = [] then make_fail t.typ
    else
      match ty_exn with
      | TVariant (b, rows) ->
          (* TODO: VPoly *)
          let make row =
            let pat_desc =
              PConstr (b <> VNonPoly, Type.LId row.row_constr, List.map make_pany row.row_args)
            in
            let pat_typ = ty_exn in
            make_pattern pat_desc pat_typ
          in
          let pats =
            rows
            |> List.filter (row_constr |- string_of_label |- List.mem -$- !Flag.Method.target_exn)
            |> List.map make
            |> List.map (Pair.pair -$- make_fail ~force:true t.typ)
          in
          make_match (make_var e) (pats @ [ (make_pany ty_exn, make_bottom t.typ) ])
      | _ -> assert false
  in
  make_trywith_handler t (make_fun e handler_body)

let make_catch_all t =
  if !Flag.Method.target_exn = [] then Fun.id
  else match find_exn_typ t with None -> Fun.id | Some ty -> catch_all ty

let trans_typ_as_term f ty = ty |> make_dummy |> f |> Syntax.typ

let trans_decl_as_term f decl =
  let decls', eod = decl |> make_local -$- end_of_definitions |> f |> decomp_decls in
  assert (eod.desc = End_of_definitions);
  List.get decls'

let col_decls_as_term f decls = decls |> make_locals -$- end_of_definitions |> f

let col_raise =
  let col = Col.make [] ( @@@ ) in
  let col_desc desc =
    match desc with
    | Raise { desc = Constr (_, s, _) } -> [ Some s ]
    | Raise _ -> [ None ]
    | TryWith (t1, { desc = Fun (e, { desc = Match ({ desc = Var e' }, pats) }) })
      when Lid.(LId e = e')
           && (function
                | { pat_desc = PAny }, { desc = Raise { desc = Var e'' } } -> Lid.(LId e = e'')
                | _ -> false)
              @@ List.last pats ->
        let pats', _ = List.decomp_snoc pats in
        col.term t1 @@@ List.rev_flatten_map (snd |- col.term) pats'
    | _ -> col.desc_rec desc
  in
  col.desc <- col_desc;
  col.term

let has_raise ?(target = []) t =
  let check =
    if target = [] then fun _ -> true
    else Option.map_default (fun s -> List.exists (( = ) (string_of_path s)) target) true
  in
  col_raise t |> List.exists check

let has_deref =
  let it = Iter.make () in
  it.desc <- (fun desc -> match desc with Deref _ -> raise Found | _ -> it.desc_rec desc);
  Exception.does_raise ~exn:Found it.term

let has_module =
  let it = Iter.make () in
  it.desc <-
    (fun desc ->
      match desc with Module _ | Pack _ | Unpack _ -> raise Found | _ -> it.desc_rec desc);
  Exception.does_raise ~exn:Found it.term

let col_exn_constr : term -> (path * [ `Used of typ list | `Rebind ]) list =
  let ( ++ ) es1 es2 =
    let eq = Eq.on fst ~eq:Path.eq in
    List.fold_right (List.cons_unique ~eq) es1 es2
  in
  let add_prefix (prefix, penv) c =
    match (c, prefix, Id.List.assoc_opt (Path.head c) penv) with
    | _, _, Some (Some prefix') -> Type.LDot (prefix', Path.name c)
    | LId _, Some p, _ -> Type.LDot (p, Path.name c)
    | _ -> c
  in
  let col = Col2.make [] ( ++ ) in
  col.term <-
    (fun ((prefix, penv) as env) t ->
      match (t.desc, elim_tattr t.typ) with
      | Constr (false, c, ts), TConstr (p, _) when C.is_exn p ->
          let c' = add_prefix env c in
          [ (c', `Used (List.map Syntax.typ ts)) ]
      | Local (Decl_let [ (m, t1) ], t2), _ when is_module t1 ->
          let id = Id.set_typ m () in
          let prefix' =
            match prefix with None -> Type.LId id | Some lid -> LDot (lid, Id.name m)
          in
          col.term (Some prefix', penv) t1 ++ col.term (prefix, (id, prefix) :: penv) t2
      | Local (Decl_let defs, _), _ when List.exists (snd |- is_module) defs ->
          unsupported "%s" __FUNCTION__
      | Local (Type_ext (Ext_type (p, (_, { ext_row_path = LId c }))), t1), _ when C.is_exn p ->
          let penv' = (c, prefix) :: penv in
          col.term (prefix, penv') t1
      | Local (Type_ext (Ext_rebind (c, p)), t1), _ ->
          let penv' = (c, prefix) :: penv in
          [ (add_prefix env p, `Rebind) ] ++ col.term (prefix, penv') t1
      | Module decls, _ -> col_decls_as_term (col.term env) decls
      | _ -> col.desc env t.desc);
  col.pat <-
    (fun env p ->
      match (p.pat_desc, elim_tattr p.pat_typ) with
      | PConstr (false, c, ps), TConstr (p, _) when C.is_exn p ->
          let c' = add_prefix env c in
          [ (c', `Used (List.map pat_typ ps)) ]
      | _ -> col.pat_rec env p);
  col.term (None, [])

let col_constr_path_in_term =
  let col = Col.make [] ( @@@ ) in
  col.typ <- Fun.const [];
  col.desc <-
    (fun desc ->
      let cs = col.desc_rec desc in
      match desc with Constr (false, c, _) -> c :: cs | _ -> cs);
  col.pat <-
    (fun p ->
      let cs = col.pat_rec p in
      match p.pat_desc with PConstr (false, c, _) -> c :: cs | _ -> cs);
  col.term |- List.sort_unique compare

let col_constr_in_term =
  let col = Col.make [] ( @@@ ) in
  col.typ <- Fun.const [];
  col.desc <-
    (fun desc ->
      let cs = col.desc_rec desc in
      match desc with Constr (false, LId c, _) -> c :: cs | _ -> cs);
  col.pat <-
    (fun p ->
      let cs = col.pat_rec p in
      match p.pat_desc with PConstr (false, LId c, _) -> c :: cs | _ -> cs);
  col.term |- List.sort_unique compare

let col_poly_constr =
  let col = Col.make [] ( @@@ ) in
  col.typ <-
    (fun ty ->
      match ty with
      | TVariant (VPoly _, rows) ->
          List.rev_flatten_map
            (fun { row_constr; row_args } -> row_constr :: List.rev_flatten_map col.typ row_args)
            rows
      | _ -> col.typ_rec ty);
  col.desc <-
    (fun desc ->
      (* Needed for externally defined polymorphic types *)
      let cs = col.desc_rec desc in
      match desc with Constr (true, LId c, _) -> c :: cs | _ -> cs);
  col.pat <-
    (fun p ->
      let cs = col.pat_rec p in
      match p.pat_desc with PConstr (true, LId c, _) -> c :: cs | _ -> cs);
  col.term |- List.sort_unique compare

let col_exn_decl : term -> (Type.path * [ `Decl of typ list | `Rebind of Type.path ]) list =
  let ( ++ ) es1 es2 =
    let eq = Eq.on fst ~eq:Path.eq in
    List.fold_right (List.cons_unique ~eq) es1 es2
  in
  let col = Col2.make [] ( ++ ) in
  col.term <-
    (fun add_prefix t ->
      match t.desc with
      | Local (Type_ext (Ext_type (p, ([], row))), t2) when C.is_exn p ->
          let p = add_prefix row.ext_row_path in
          [ (p, `Decl row.ext_row_args) ] ++ col.term add_prefix t2
      | Local (Type_ext (Ext_rebind (c, p)), t2) ->
          [ (add_prefix (LId c), `Rebind p) ] ++ col.term add_prefix t2
      | Local (Decl_let [ (m, t1) ], t2) when is_module t1 ->
          let add_prefix' = add_prefix -| Path.cons m in
          col.term add_prefix' t1 ++ col.term add_prefix t2
      | Local (Decl_let defs, _) when List.exists (snd |- is_module) defs ->
          unsupported "%s" __FUNCTION__
      | Module decls -> col_decls_as_term (col.term add_prefix) decls
      | _ -> col.desc add_prefix t.desc);
  col.term Fun.id

let rec add_to_env decl env =
  match decl with
  | Decl_let bindings ->
      List.fold_left (fun env (f, t) -> Tenv.add_module f t.typ ~env) env bindings
  | Decl_type decl -> Tenv.add_typ_decl decl env
  | Type_ext ext -> Tenv.add_ext ext env
  | Include { typ } ->
      let decls =
        let env = List.map (fun (x, (_, ty)) -> (x, ty)) env.menv in
        sig_of_mod_typ ~env typ
        |> List.map (function
             | Sig_type decl -> Decl_type decl
             | Sig_value x -> Decl_let [ (x, make_dummy @@ Id.typ x) ]
             | Sig_ext _ -> [%unsupported])
      in
      List.fold_right add_to_env decls env
  | Decl_multi decls -> List.fold_right add_to_env decls env

let make_decl_trans : (declaration -> declaration list) -> term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun f desc ->
      match tr.desc_rec f desc with
      | Local (decl, t) -> (make_locals (f decl) t).desc
      | Module decls -> Module (List.flatten_map f decls)
      | desc -> desc);
  tr.term

(* includes external types *)
let get_free_types =
  let col = Col2.make [] ( @@@ ) in
  col.desc <-
    (fun ((bv, bt) as arg) desc ->
      match desc with
      | Local (decl, _) ->
          let bv' =
            get_bv_decl decl
            |> List.filter is_mod_var
            |> List.rev_map_append (Id.set_typ -$- ()) -$- bv
          in
          let bt' = get_bt_decl decl @@@ bt in
          col.desc_rec (bv', bt') desc
      | Module decls -> col_decls_as_term (col.term arg) decls
      | _ -> col.desc_rec arg desc);
  col.typ <-
    (fun ((bv, bt) as arg) ty ->
      match ty with
      | TConstr (path, tys) ->
          let is_bound_id bs = Id.List.mem -$- bs ||| Id.is_external ||| Id.is_primitive in
          let rec is_bound_module (path : path) =
            match path with
            | LId c -> is_bound_id bv c
            | LDot (p, _) | LApp (p, _) -> is_bound_module p
          in
          let is_bound (path : path) =
            match path with
            | LId c -> is_bound_id bt c || List.mem ~eq:Path.eq path C.prims
            | LDot (p, _) | LApp (p, _) -> is_bound_module p
          in
          let acc = col.typ_rec arg ty in
          if is_bound path then acc else (path, List.length tys) :: acc
      | TModSig sgn -> col.desc arg (List.fold_right make_let_type (sig_types sgn) unit_term).desc
      | _ -> col.typ_rec arg ty);
  col.attr <- Fun.const2 [];
  col.term ([], []) |- List.unique

let rec gen_fresh_name_var ?(postfix = "'") bv x =
  let x = Id.add_name_after postfix x in
  if List.mem ~eq:(Eq.on Id.name) x bv then gen_fresh_name_var bv x else x

let incr_string_postfix s =
  if Char.is_digit (String.last s) then
    let n = Str.search_backward (Str.regexp "[^0-9][0-9]+") s (String.length s) + 1 in
    let prefix = String.sub s 0 n in
    let postfix = String.sub s n (String.length s - n) in
    prefix ^ string_of_int (1 + int_of_string postfix)
  else s ^ "1"

let rec gen_fresh_name_var_int bv x =
  let x = Id.map_name incr_string_postfix x in
  if List.mem ~eq:(Eq.on Id.name) x bv then gen_fresh_name_var_int bv x else x

let is_recursive_module_decl decl =
  match decl with
  | Decl_let defs when List.exists (fst |- is_mod_var) defs ->
      let xs = List.map fst defs in
      let fv = List.rev_flatten_map (snd |- get_fv) defs in
      not (Id.List.Set.disjoint xs fv)
  | _ -> false

let use_try_raise =
  let it = Iter.make () in
  it.desc <-
    (fun desc -> match desc with Raise _ | TryWith _ -> raise Found | _ -> it.desc_rec desc);
  Exception.does_raise ~exn:Found it.term

let col_modules =
  let col = Col.make IdSet.empty IdSet.union in
  col.var <- (fun v -> if is_mod_var v then IdSet.singleton v else IdSet.empty);
  col.term |- IdSet.elements

let has_fail =
  let it = Iter.make () in
  it.desc <-
    (fun desc -> match desc with Event ("fail", _) -> raise Found | _ -> it.desc_rec desc);
  Exception.does_raise ~exn:Found it.term

let has_fun =
  let it = Iter.make () in
  it.desc <- (fun desc -> match desc with Fun _ -> raise Found | _ -> it.desc_rec desc);
  Exception.does_raise ~exn:Found it.term

let assoc_info t = List.filter_map (function AInfo info -> Some info | _ -> None) t.attr

(** [get_fv_typ ty] returns unbounded modules *)
let get_fv_typ =
  let col = Col2.make [] ( @@@ ) in
  let su x = Id.set_typ x () in
  let heads' bv p =
    match p with Type.LDot _ -> Path.heads p |> List.filter_out (Id.List.mem -$- bv) | _ -> []
  in
  col.typ <-
    (fun bv ty ->
      match ty with
      | TFun (x, ty') when is_functor_typ ty -> col.typ (su x :: bv) ty'
      | TConstr (p, tys) -> heads' bv p @@@ List.rev_flatten_map (col.typ bv) tys
      | TModSig sgn ->
          let acc, _ =
            List.L.fold_left sgn ~init:([], bv) ~f:(fun (acc, bv) item ->
                match item with
                | Sig_type decl ->
                    (List.fold_left (fun acc (_, (_, ty)) -> col.typ bv ty @@@ acc) acc decl, bv)
                | Sig_value x ->
                    let bv' = su x :: bv in
                    (col.typ bv' (Id.typ x) @@@ acc, bv')
                | Sig_ext (p, (_, { ext_row_path; ext_row_args })) ->
                    let acc = heads' bv p @@@ heads' bv ext_row_path @@@ acc in
                    (List.fold_left (fun acc ty -> col.typ bv ty @@@ acc) acc ext_row_args, bv))
          in
          acc
      | TModLid path -> heads' bv path
      | _ -> col.typ_rec bv ty);
  col.typ [] |- List.unique ~eq:Id.eq

let get_fv_typ' = get_fv_typ |- List.map (Id.set_typ -$- TModSig [])
let get_fv_all = get_fv_gen get_fv_typ'

let is_exn_free =
  let col = Col.make false ( || ) in
  col.desc <-
    (fun desc ->
      match desc with
      | Module decls -> col.term (make_locals decls end_of_definitions)
      | Local (Decl_type [ (c, _) ], _) when C.is_exn (LId c) -> false
      | _ -> col.desc_rec desc);
  col.typ <- col_constrs |- List.mem ~eq:Path.eq C.exn;
  col.term

module Term = struct
  let unit = unit_term
  let tt = true_term
  let true_ = true_term
  let ff = false_term
  let false_ = false_term
  let fail = make_fail_unit None
  let randi = randint_unit_term
  let randb = randbool_unit_term
  let rand = make_rand_unit
  let bot = make_bottom
  let eod = end_of_definitions
  let var = make_var
  let vars = List.map make_var
  let var_lid = make_var_lid
  let int = make_int
  let bool = make_bool
  let string = make_string
  let ( @ ) = make_app ?env:None
  let ( @@ ) = make_app ?env:None
  let type_ = make_let_type
  let let_ = make_let
  let let_s = make_let_s
  let lets = make_lets
  let lets_s = make_lets_s
  let let_nonrec = make_nonrec_let
  let fun_ = make_fun
  let pfun = make_pure_fun
  let funs = make_funs
  let not = make_not
  let ( && ) = make_and
  let ands = make_ands
  let ( || ) = make_or
  let ors = make_ors
  let ( => ) = make_imply
  let ( + ) = make_add
  let ( - ) = make_sub
  let ( * ) = make_mul
  let ( / ) = make_div
  let ( ~- ) = make_neg
  let if_ = make_if ?typ:None
  let br = make_br
  let ( |+| ) = make_br
  let brs = make_brs
  let ( = ) = make_eq
  let ( <> ) = make_neq
  let ( < ) = make_lt
  let ( > ) = make_gt
  let ( <= ) = make_leq
  let ( >= ) = make_geq

  let ( <| ) t1 op = make_binop op t1
  and ( |> ) mb t2 = mb t2

  let fst = make_fst
  let snd = make_snd
  let pair = make_pair
  let tuple = make_tuple
  let proj = make_proj
  let nil = make_nil
  let nil2 = make_nil2
  let cons = make_cons
  let list = make_list
  let seq = make_seq
  let seqs = make_seqs
  let ignore = make_ignore
  let assert_ = make_assert
  let assume = make_assume
  let none = make_none
  let none2 = make_none2
  let some = make_some
  let left = make_left
  let right = make_right
  let is_left = make_is_left
  let get_left = make_get_left
  let get_right = make_get_right
  let field = make_field
  let ref = make_ref
  let deref = make_deref
  let ( ! ) = make_deref
  let ( := ) = make_setref
  let constr = make_construct
  let match_ = make_match
  let module_ = make_module
  let pack = make_pack
  let unpack = make_unpack
  let local = make_local
  let locals = make_locals
  let type_ext = make_type_ext
  let length = make_length
  let raise = make_raise
  let try_ = make_trywith
  let trywith = make_trywith
  let trywith_h = make_trywith_handler
  let ( |-> ) = subst ~b_ty:false
  let empty = make_empty
  let mem = make_mem
  let addset = make_addset
  let subset = make_subset
  let lazy_ = make_lazy
  let forall = List.fold_right make_forall
  let exists = List.fold_right make_exists
  let dummy = make_dummy
  let record = make_record
end

module Pat = struct
  let __ = make_pany
  let any = make_pany
  let const = make_pconst
  let nondet = make_pnondet
  let unit = const unit_term
  let int = const -| make_int
  let bool = const -| make_bool
  let true_ = bool true
  let false_ = bool false
  let var = make_pvar
  let pair = make_ppair
  let ( * ) = pair
  let tuple = make_ptuple
  let nil = make_pnil
  let nil2 = make_pnil2
  let cons = make_pcons
  let list = make_plist
  let when_ = make_pwhen
  let lazy_ = make_plazy
  let eval = make_peval
  let some = make_psome
  let alias = make_palias
  let or_ = make_por
  let ( || ) = make_por
end

module Eq = struct
  include Eq

  let id = Id.eq
  let typ = Type.eq
  let path = Path.eq ~eq:Id.eq
end

module Tenv = struct
  include Tenv

  let add_decl ?prefix decl env =
    match decl with
    | Decl_let defs ->
        List.fold_left (fun env (x, _) -> add_module ?prefix x (Id.typ x) ~env) env defs
    | Decl_type decls -> add_typ_decl ?prefix decls env
    | Type_ext ext -> add_ext ext env
    | Include _ -> [%unsupported]
    | Decl_multi _ -> [%unsupported]
end
