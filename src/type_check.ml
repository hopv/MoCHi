open Util
open Syntax
open Term_util
open Type

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let check_var t x typ =
  if not @@ can_unify (Id.typ x) typ then
    begin
      Format.eprintf "check_var: (%a:%a), %a@." Id.print x Print.typ (Id.typ x) Print.typ typ;
      set_mark t;
      assert false
    end

let not_module ty1 ty2 =
  let check = function TModule _ -> false | _ -> true in
  check ty1 && check ty2

let rec check env t typ =
  if false then Debug.printf "CHECK: @[%a, %a@." Print.term t Print.typ typ;
  if not (can_unify t.typ typ) && not_module t.typ typ then
    (Format.eprintf "check: @[%a,@ %a@." (Color.red Print.term') t (Color.yellow Print.typ) typ;
     set_mark t;
     assert false);
  match t.desc, elim_tattr t.typ with
  | _, TFuns _ -> ()
  | Label(_, t), _ -> check env t typ
  | End_of_definitions, TBase TUnit -> ()
  | Const Unit, TBase TUnit -> ()
  | Const CPS_result, typ when typ = typ_result -> ()
  | Const(True|False), TBase TBool -> ()
  | Const(Int _), TBase TInt -> ()
  | Const _, TBase (TPrim _) -> ()
  | Const(Rand(TBase TInt,false)), TFun(x,TBase TInt)->
      check_var t x Ty.unit
  | Const(Rand(TBase TInt,true)), TFun(x,TFun(k,rtyp)) ->
      if rtyp <> typ_result then (set_mark t; assert false);
      check_var t x @@ TBase TUnit;
      check_var t k Ty.(fun_ int typ_result)
  | Const(Rand(typ1,false)), TFun({Id.typ=TBase TUnit},typ2) ->
      if not @@ can_unify typ1 typ2 then (set_mark t; assert false)
  | Const(Rand(_typ1,true)), TFun({Id.typ=TBase TUnit}, TFun({Id.typ=TFun(_x,_rtyp1)},_rtyp2)) -> ()
  (*
      assert (rtyp1 = typ_result);
      assert (rtyp2 = typ_result);
      assert (typ1 = Id.typ x)*)
  | Const Empty, typ -> ignore (Type.set_typ typ)
  | Var x, typ' ->
      check_var t x typ'
  | Fun(x,t1), TFun(y,typ') ->
      check_var t x (Id.typ y);
      check env t1 typ'
  | App(t1,ts), typ' ->
      let rec aux (ts,typ) =
        match ts, elim_tattr typ with
        | [], _ -> ()
        | t::ts, TFun(x,typ) ->
            check env t (Id.typ x);
            aux (ts,typ)
        | [_], typ when typ = typ_event -> ()
        | _ ->
            Format.eprintf "ts: %a@." Print.(list term) ts;
            Format.eprintf "typ: %a@." Print.typ typ;
            set_mark t;
            assert false
      in
      aux (ts, t1.typ);
      check env t1 @@ List.fold_right (fun t typ -> Ty.fun_ t.typ typ) ts typ'
  | If(t1,t2,t3), typ' ->
      check env t1 Ty.bool;
      check env t2 typ';
      check env t3 typ'
  | Local(Decl_let bindings, t2), typ' ->
      let fv = get_fv t2 in
      List.iter (fun (f,t) -> check env t @@ elim_tattr @@ Id.typ f) bindings;
      let aux' f =
        let aux f' =
          if Id.(f = f') && not @@ can_unify (Id.typ f) (Id.typ f') then
            begin
              Format.eprintf "f: %a@." Print.id_typ f;
              Format.eprintf "f': %a@." Print.id_typ f';
              set_mark t;
              assert false
            end
        in
        List.iter aux fv
      in
      List.iter (aux' -| fst) bindings;
      check env t2 typ'
  | Local(Decl_type decls, t2), typ' ->
      check (decls@env) t2 typ'
  | BinOp(Eq,t1,t2), TBase TBool ->
      if not @@ can_unify t1.typ t2.typ then (set_mark t; assert false);
      check env t1 t1.typ;
      check env t2 t2.typ;
  | BinOp((Lt|Gt|Leq|Geq),t1,t2), TBase TBool ->
      if not @@ can_unify t1.typ t2.typ then (set_mark t; assert false);
      check env t1 t1.typ;
      check env t2 t2.typ
  | BinOp((And|Or),t1,t2), TBase TBool ->
      check env t1 @@ TBase TBool;
      check env t2 @@ TBase TBool
  | BinOp((Add|Sub|Mult|Div),t1,t2), TBase TInt ->
      check env t1 @@ TBase TInt;
      check env t2 @@ TBase TInt
  | Not t, TBase TBool ->
      check env t @@ TBase TBool
  | Event(_,false), typ' ->
      if not (can_unify typ' typ_event || can_unify typ' typ_event) then (set_mark t; assert false)
  | Event(_s,true), typ' ->
      if not @@ can_unify typ' typ_event_cps then (set_mark t; assert false)
  | Tuple ts, TTuple xs ->
      assert (List.length ts = List.length xs);
      List.iter2 (check env) ts @@ List.map Id.typ xs
  | Proj(i,t), typ ->
      if not @@ can_unify typ @@ proj_typ i t.typ then (set_mark t; assert false);
      check env t t.typ
  | Record fields, TRecord tfields ->
      begin
        try
          List.iter (fun (s,t) -> check env t @@ snd @@ List.assoc s tfields) fields
        with Not_found ->
          Format.eprintf "fields: %a@." Print.(list (string * __)) fields;
          Format.eprintf "tfields: %a@." Print.(list (string * __)) tfields;
          set_mark t;
          assert false
      end
  | Field(t1,s), typ ->
      begin
        match t1.typ with
        | TRecord tfields ->
            begin
              try
                if not @@ can_unify typ @@ snd @@ List.assoc s tfields then (set_mark t; assert false)
              with Not_found ->
                set_mark t;
                assert false
            end
        | TData _ -> ()
        | _ ->
            Format.eprintf "%a@." Print.term' t1;
            assert false
      end;
      check env t1 t1.typ
  | SetField(t1,s,t2), typ ->
      if not @@ can_unify typ Ty.unit then (set_mark t; assert false);
      begin
        match t1.typ with
        | TRecord tfields ->
            let f,typ' =
              try
                List.assoc s tfields
              with Not_found ->
                set_mark t;
                assert false
            in
            if f <> Mutable then (set_mark t; assert false);
            check env t2 typ'
        | TData _ -> ()
        | _ -> set_mark t; assert false
      end;
      check env t1 t1.typ
  | Nil, TApp("list", _) -> ()
  | Cons(t1,t2), TApp("list", [typ']) ->
      check env t1 typ';
      check env t2 typ
  | Constr(s,ts), TVariant(_,labels) ->
      begin
        try
          if List.length ts <> List.length (List.assoc s labels) then
           (Format.printf "%s@." s; set_mark t; assert false);
          List.iter2 (check env) ts @@ List.assoc s labels
        with Not_found ->
          Format.printf "Not_found: %s@." s;
          Format.printf "labels: %a@." Print.(list (string * list typ)) labels;
          set_mark t;
          assert false
      end
  | Match(t,pats), typ' ->
      let aux (_p,t) =
        check env t typ'
      in
      check env t t.typ;
      List.iter aux pats
  | Raise t, _ ->
      check env t t.typ
  | TryWith(t1,t2), typ ->
      check env t1 typ;
      check env t2 @@ make_tfun (TVar(ref None, -1)) typ
  | Bottom, _ -> ()
  | Ref t, TApp("ref", [typ]) ->
      check env t typ
  | Deref t, typ ->
      check env t (make_tref typ)
  | SetRef(t1,t2), TBase TUnit ->
      check env t1 (make_tref t2.typ);
      check env t2 t2.typ
  | TNone, TApp("option", _) -> ()
  | TSome t, TApp("option", [typ]) ->
      check env t typ
  | Module decls, TModule {sig_values; sig_types} -> (* TODO: update env, use sig_types to check decls *)
      let vals = List.flatten_map (function Decl_let defs -> List.map fst defs | _ -> []) decls in
      let tys = List.flatten_map (function Decl_type decls -> List.map fst decls | _ -> []) decls in
      if not @@ List.Set.subset ~eq:Id.eq sig_values vals then (set_mark t; assert false);
      if not @@ List.Set.subset (List.map fst sig_types) tys then (set_mark t; assert false);
      check env (List.fold_right Term.local decls Term.eod) Ty.unit
  | MemSet(t1,t2), _ ->
      check env t1 (Type.set_typ t2.typ);
      check env t2 t2.typ
  | AddSet(t1,t2), _ ->
      check env t1 (Type.set_typ typ);
      check env t2 typ
  | Subset(t1,t2), _ ->
      if not @@ can_unify typ Ty.unit then (set_mark t; assert false);
      check env t1 t1.typ;
      check env t2 t2.typ
  | _, TData s when List.mem_assoc s env ->
      let typ = List.assoc s env in
      check env {t with typ} typ
  | _, TData _ -> () (* externally defined types *)
  | _ ->
      Format.eprintf "check': @[%a,@ %a@." Print.term' t (Color.yellow Print.typ) t.typ;
      set_mark t;
      assert false

let check ?(ty=Ty.unit) t =
  if Flag.Debug.check_typ then
    let t = if !!Debug.check then add_mark t else t in
    try
      check [] t ty
    with _ when !!Debug.check ->
      Format.eprintf "%a@.@." Print.term_typ t;
      assert false
