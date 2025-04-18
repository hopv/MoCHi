open Util
open Type
open Type_util
open Syntax
open Term_util

module Debug = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

exception Failed of string

let print_error fm = Color.eprintf Bright ("##[Type_check] " ^^ fm)

let is_postfix s full =
  s = full
  ||
  match String.split full ~by:s with
  | pre, post -> post = "" && (String.ends_with pre "." || String.ends_with pre "__")
  | exception Not_found -> false

let check_failed loc t =
  set_mark t;
  raise (Failed loc)

let check_var loc env t x typ =
  if not @@ can_unify ~env (Id.typ x) typ then (
    print_error "check_var: (%a:%a), %a@." Id.print x Print.typ (Id.typ x) Print.typ typ;
    print_error "      env: @[%a@." Print.env env;
    check_failed loc t)

let check_lid loc env t lid typ =
  match can_unify ~sub:true ~env (Lid.typ lid) typ with
  | true -> ()
  | false ->
      print_error "check_lid: @[(%a:%a),@ %a@." Lid.print lid Print.typ (Lid.typ lid) Print.typ typ;
      check_failed loc t
  | exception Sig_of_Lid _ -> ()

let check_eq loc x y t = if x <> y then check_failed loc t

let not_module ty1 ty2 =
  let check = not -| is_mod_typ in
  check ty1 && check ty2

(* TODO: Update bv *)
let rec check_pat env bv t ?ty p =
  let ch = check_pat env bv t in
  Option.iter (fun ty -> if not (can_unify ~env p.pat_typ ty) then check_failed __LOC__ t) ty;
  match p.pat_desc with
  | PAny -> ()
  | PNondet -> ()
  | PVar _ -> ()
  | PAlias (p, _) -> ch ?ty p
  | PConst _ -> ()
  | PConstr (_, _, ps) -> List.iter ch ps
  | PNil -> ()
  | PCons (p1, p2) ->
      ch p1;
      ch ?ty p2
  | PTuple ps -> List.iter ch ps
  | PRecord fields -> List.iter (snd |- ch) fields
  | PNone -> ()
  | PSome p -> ch p
  | POr (p1, p2) ->
      ch ?ty p1;
      ch ?ty p2
  | PWhen (p, t) ->
      let bv' = get_bv_pat p @@@ bv in
      ch ?ty p;
      check env bv' t Ty.bool
  | PLazy p -> ch p
  | PEval (x, t, p) ->
      check env bv t (Id.typ x);
      ch p

(* The order of bv matters *)
and check env bv t typ =
  let ch = check env bv in
  let cu = can_unify ~env ~ignore_poly_variant:true in
  if true then Debug.printf "CHECK: @[%a, %a, %a@." Print.term t Print.typ t.typ Print.typ typ;
  (*
  if false then Format.fprintf !Flag.Print.target "#env: %a@.@." Type_util.print_declaration_init env;
   *)
  let pr_ty = Color.yellow (if true then Print.typ else Type.pp Print.term) in
  if (not (cu ~sub:true t.typ typ)) && not_module t.typ typ then (
    print_error "check: @[%a,@ %a@." (Color.red Print.term') t pr_ty typ;
    print_error "check: @[%a@." Print.env env;
    check_failed __LOC__ t);
  match (t.desc, Tenv.normalize_type env typ) with
  | _, TFuns _ -> ()
  | _, TVar (_, { contents = None }, _) -> ()
  | _, TPoly (_, ty) -> ch t ty
  | End_of_definitions, TBase TUnit -> ()
  | Const Unit, TBase TUnit -> ()
  | Const CPS_result, typ when typ = typ_result -> ()
  | Const (True | False), TBase TBool -> ()
  | Const (Int _), TBase TInt -> ()
  | Const (Rand (TBase TInt, false)), TFun (x, TBase TInt) -> check_var __LOC__ env t x Ty.unit
  | Const (Rand (TBase TInt, true)), TFun (x, TFun (k, rtyp)) ->
      if rtyp <> typ_result then check_failed __LOC__ t;
      check_var __LOC__ env t x Ty.unit;
      check_var __LOC__ env t k Ty.(fun_ int typ_result)
  | Const (Rand (typ1, false)), TFun ({ Id.typ = TBase TUnit }, typ2) ->
      if not @@ cu typ1 typ2 then check_failed __LOC__ t
  | ( Const (Rand (_typ1, true)),
      TFun ({ Id.typ = TBase TUnit }, TFun ({ Id.typ = TFun (_x, _rtyp1) }, _rtyp2)) ) ->
      ()
  (*
      assert (rtyp1 = typ_result);
      assert (rtyp2 = typ_result);
      assert (typ1 = Id.typ x)*)
  | Const (Dummy ty), _ when cu ~sub:true ty typ -> ()
  | Const Empty, typ -> ignore (Ty.set typ)
  | Var x, typ' ->
      let head = head_of_lid x in
      List.find_opt (Id.( = ) head) bv
      |> Option.iter (fun head' ->
             if not (cu ~sub:true (Id.typ head) (Id.typ head')) then (
               print_error "head:  %a@." Print.id_typ head;
               print_error "head': %a@." Print.id_typ head';
               print_error "bv: %a@." Print.(list id_typ) bv;
               print_error "env: %a@.@." Print.env env;
               (try unify ~env ~sub:true (Id.typ head) (Id.typ head') with _ -> ());
               check_failed __LOC__ t));
      check_lid __LOC__ env t x typ'
  | Fun (x, t1), TFun (y, typ') ->
      check_var __LOC__ env t x (Id.typ y);
      let env = Tenv.add_module x (Id.typ y) ~env in
      check env (x :: bv) t1 typ'
  | App (t1, ts), typ' ->
      let rec aux ts typ =
        match (ts, elim_tattr typ) with
        | [], _ -> ()
        | t :: ts, TFun (x, typ) ->
            ch t (Id.typ x);
            aux ts typ
        | _ :: _, TModLid _ -> () (* TODO *)
        | _, TVar (_, { contents = Some typ }, _) -> aux ts typ
        | _, TVar (_, { contents = None }, _) -> aux ts (Ty.fun_ !!Type.new_tvar !!Type.new_tvar)
        | [ _ ], typ when typ = !!Ty.event -> ()
        | [ _ ], typ when typ = Ty.unknown -> ()
        | _ ->
            print_error "ts: %a@." Print.(list term) ts;
            print_error "typ: %a@." Print.typ typ;
            check_failed __LOC__ t
      in
      aux ts t1.typ;
      ch t1 @@ List.fold_right (fun t typ -> Ty.fun_ t.typ typ) ts typ'
  | If (t1, t2, t3), typ' ->
      ch t1 Ty.bool;
      ch t2 typ';
      ch t3 typ'
  | Local (decl, t2), typ' ->
      let bv' =
        match decl with
        | Decl_let bindings ->
            List.iter (fun (f, t) -> check env bv t @@ Id.typ f) bindings;
            List.map fst bindings
        | _ -> []
      in
      let env = add_to_env decl env in
      check env (bv' @@@ bv) t2 typ'
  | BinOp (Eq, t1, t2), TBase TBool ->
      if not @@ cu t1.typ t2.typ then check_failed __LOC__ t;
      ch t1 t1.typ;
      ch t2 t2.typ
  | BinOp ((Lt | Gt | Leq | Geq), t1, t2), TBase TBool ->
      if not @@ cu t1.typ t2.typ then check_failed __LOC__ t;
      ch t1 t1.typ;
      ch t2 t2.typ
  | BinOp ((And | Or), t1, t2), TBase TBool ->
      ch t1 Ty.bool;
      ch t2 Ty.bool
  | BinOp ((Add | Sub | Mult | Div), t1, t2), TBase TInt ->
      ch t1 Ty.int;
      ch t2 Ty.int
  | Not t, TBase TBool -> ch t Ty.bool
  | Event (_, false), typ' ->
      if not (cu typ' !!Ty.event || cu typ' !!Ty.event) then check_failed __LOC__ t
  | Event (_s, true), typ' -> if not @@ cu typ' !!Ty.event_cps then check_failed __LOC__ t
  | Tuple ts, TTuple xs ->
      check_eq __LOC__ (List.length ts) (List.length xs) t;
      List.iter2 ch ts @@ List.map Id.typ xs
  | Proj (i, t), typ ->
      if not @@ cu typ @@ proj_typ i @@ Tenv.normalize_type env t.typ then check_failed __LOC__ t;
      ch t t.typ
  | Record fields, TRecord tfields -> (
      try List.L.iter fields ~f:(fun (s, t) -> tfields |> Id.List.assoc s |> snd |> ch t)
      with Not_found ->
        print_error "fields: %a@." Print.(list (label * __)) fields;
        print_error "tfields: %a@." Print.(list (label * __)) tfields;
        check_failed __LOC__ t)
  | Field (t1, s), typ ->
      (match Tenv.normalize_type env t1.typ with
      | TRecord tfields -> (
          try if not @@ cu typ @@ snd @@ Id.List.assoc s tfields then check_failed __LOC__ t
          with Not_found -> check_failed __LOC__ t)
      | _ ->
          print_error "t1: %a@." Print.term' t1;
          check_failed __LOC__ t);
      ch t1 t1.typ
  | SetField (t1, s, t2), typ ->
      if not @@ cu typ Ty.unit then check_failed __LOC__ t;
      (match Tenv.normalize_type env t1.typ with
      | TRecord tfields ->
          let f, typ' = try Id.List.assoc s tfields with Not_found -> check_failed __LOC__ t in
          if f <> Mutable then check_failed __LOC__ t;
          ch t2 typ'
      | _ -> check_failed __LOC__ t);
      ch t1 t1.typ
  | Nil, TConstr (c, _) when c = C.list -> ()
  | Cons (t1, t2), TConstr (c, [ typ' ]) when c = C.list ->
      ch t1 typ';
      ch t2 typ
  | Constr _, TConstr (c, _) when C.is_exn c ->
      ch t (snd @@ Tenv.assoc_exn env) (* TODO: Use discarded environment *)
  | Constr (false, s, ts), TVariant (VNonPoly, rows) ->
      let row =
        try assoc_row (constr_of_path s) rows
        with Not_found ->
          print_error "t: %a@." Print.term' t;
          print_error "t.typ: %a@." Print.typ t.typ;
          print_error "Not_found: %s@." (Path.name s);
          print_error "rows: %a@.@." Print.(list T.row_init) rows;
          print_error "env: %a@.@." Print.env env;
          check_failed __LOC__ t
      in
      check_eq __LOC__ (List.length ts) (List.length row.row_args) t;
      List.iter2 ch ts row.row_args
  | Constr (true, s, ts), TVariant (VPoly { closed; tvar = _; lower = _ }, rows) ->
      let row =
        try Some (assoc_row (constr_of_path s) rows)
        with Not_found ->
          if closed then (
            print_error "t: %a@." Print.term' t;
            print_error "t.typ: %a@." Print.typ t.typ;
            print_error "Not_found: %s@." (Path.name s);
            print_error "rows: %a@.@." Print.(list T.row_init) rows;
            print_error "env: %a@.@." Print.env env;
            check_failed __LOC__ t)
          else None
      in
      Option.iter
        (fun row ->
          check_eq __LOC__ (List.length ts) (List.length row.row_args) t;
          List.iter2 ch ts row.row_args)
        row
  | Match (t1, pats), typ' ->
      ch t1 t1.typ;
      List.L.iter pats ~f:(fun (p, t2) ->
          let bv' = get_bv_pat p @@@ bv in
          check_pat env bv t1 ~ty:t1.typ p;
          check env bv' t2 typ')
  | Raise t, _ -> ch t t.typ
  | TryWith (t1, t2), typ ->
      ch t1 typ;
      ch t2 @@ Ty.fun_ !!new_tvar typ
  | Bottom, _ -> ()
  | Ref t, TConstr (c, [ typ ]) when c = C.ref -> ch t typ
  | Deref t, typ -> ch t (make_tref typ)
  | SetRef (t1, t2), TBase TUnit ->
      ch t1 (make_tref t2.typ);
      ch t2 t2.typ
  | TNone, TConstr (c, _) when c = C.option -> ()
  | TSome t, TConstr (c, [ typ ]) when c = C.option -> ch t typ
  | Lazy t, TConstr (c, [ typ ]) when c = C.lazy_ -> ch t typ
  | _, TConstr (s, _) -> (
      match Tenv.assoc_type s env with
      | _, typ -> ch (make t.desc typ) typ
      | exception Not_found -> () (* externally defined types *))
  | Module _decls, TModSig _sgn ->
      (* TODO *)
      ()
  | Pack t, TPackage ty -> ch t ty
  | Unpack t, ty -> ch t (TPackage ty)
  | MemSet (t1, t2), _ ->
      ch t1 (Ty.set t2.typ);
      ch t2 t2.typ
  | AddSet (t1, t2), _ ->
      ch t1 (Ty.set typ);
      ch t2 typ
  | Subset (t1, t2), _ ->
      if not @@ cu typ Ty.unit then check_failed __LOC__ t;
      ch t1 t1.typ;
      ch t2 t2.typ
  | _ ->
      print_error "check': @[%a,@ %a@." Print.term' t (Color.yellow Print.typ) t.typ;
      check_failed __LOC__ t

let check ?(force = false) ?(env = !!Tenv.init) ?(ty = Ty.unit) t =
  if Flag.Debug.check_typ || force then (
    let t = if !!Debug.check then add_mark t else t in
    try check env [] t ty
    with Failed loc when !!Debug.check ->
      print_error "Failed: %s@.%a@.@." loc Print.term_typ t;
      raise (Failed loc))
