open Util
open Syntax
open Term_util
open Type

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let check_var x typ =
  if Type.can_unify (Id.typ x) typ
  then ()
  else (Format.eprintf "check_var: (%a:%a), %a@." Id.print x Print.typ (Id.typ x) Print.typ typ; assert false)

let rec check env t typ =
  Debug.printf "CHECK: @[%a, %a@." Print.term t Print.typ typ;
  if not (Type.can_unify t.typ typ) then
    (Format.eprintf "check: @[%a,@ %a@." (Color.red Print.term') t (Color.yellow Print.typ) typ;
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
      check_var x Ty.unit
  | Const(Rand(TBase TInt,true)), TFun(x,TFun(k,rtyp)) ->
      assert (rtyp = typ_result);
      check_var x @@ TBase TUnit;
      check_var k Ty.(fun_ int typ_result)
  | Const(Rand(typ1,false)), TFun({Id.typ=TBase TUnit},typ2) ->
      assert (Type.can_unify typ1 typ2)
  | Const(Rand(typ1,true)), TFun({Id.typ=TBase TUnit}, TFun({Id.typ=TFun(x,rtyp1)},rtyp2)) -> ()
  (*
      assert (rtyp1 = typ_result);
      assert (rtyp2 = typ_result);
      assert (typ1 = Id.typ x)*)
  | Var x, typ' ->
      check_var x typ'
  | Fun(x,t), TFun(y,typ') ->
      check_var x (Id.typ y);
      check env t typ'
  | App(t,ts), typ' ->
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
            assert false
      in
      aux (ts, t.typ);
      check env t @@ List.fold_right (fun t typ -> Ty.fun_ t.typ typ) ts typ'
  | If(t1,t2,t3), typ' ->
      check env t1 Ty.bool;
      check env t2 typ';
      check env t3 typ'
  | Local(Decl_let bindings, t2), typ' ->
      List.iter (fun (f,t) -> check env t @@ elim_tattr @@ Id.typ f) bindings;
      let aux' f =
        let check f' =
          if Id.(f = f') && not @@ Type.can_unify (Id.typ f) (Id.typ f') then
            begin
              Format.eprintf "f: %a@." Print.id_typ f;
              Format.eprintf "f': %a@." Print.id_typ f';
              assert false
            end
        in
        List.iter check @@ get_fv t2
      in
      List.iter (aux' -| Pair.fst) bindings;
      check env t2 typ'
  | Local(Decl_type decls, t2), typ' ->
      check (decls@env) t2 typ'
  | BinOp(Eq,t1,t2), TBase TBool ->
      assert (Type.can_unify t1.typ t2.typ);
      check env t1 t1.typ;
      check env t2 t2.typ;
  | BinOp((Lt|Gt|Leq|Geq),t1,t2), TBase TBool ->
      assert (Type.can_unify t1.typ t2.typ);
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
      assert (Type.can_unify typ' typ_event || Type.can_unify typ' typ_event')
  | Event(s,true), typ' ->
      assert (Type.can_unify typ' typ_event_cps)
  | Tuple ts, TTuple xs ->
      List.iter2 (check env) ts @@ List.map Id.typ xs
  | Proj(i,t), typ ->
      assert (Type.can_unify typ @@ proj_typ i t.typ);
      check env t t.typ
  | Record fields, TRecord tfields ->
      List.iter (fun (s,t) -> check env t @@ snd @@ List.assoc s tfields) fields
  | Field(t,s), typ ->
      begin
        match t.typ with
        | TRecord tfields -> assert (Type.can_unify typ @@ snd @@ List.assoc s tfields)
        | TData _ -> ()
        | _ ->
            Format.eprintf "%a@." Print.term' t;
            assert false
      end;
      check env t t.typ
  | SetField(t1,s,t2), typ ->
      assert (Type.can_unify typ Ty.unit);
      begin
        match t1.typ with
        | TRecord tfields ->
            let f,typ' = List.assoc s tfields in
            assert (f = Mutable);
            check env t2 typ'
        | TData _ -> ()
        | _ -> assert false
      end;
      check env t1 t1.typ
  | Nil, TApp(TList, _) -> ()
  | Cons(t1,t2), TApp(TList, [typ']) ->
      check env t1 typ';
      check env t2 typ
  | Constr(s,ts), TVariant(_,labels) ->
      List.iter2 (check env) ts @@ List.assoc s labels
  | Match(t,pats), typ' ->
      let aux (p,t) =
        check env t typ'
      in
      check env t t.typ;
      List.iter aux pats
  | Raise t, _ ->
      check env t t.typ
  | TryWith(t1,t2), typ ->
      check env t1 typ;
      check env t2 @@ make_tfun (TVar(ref None, None)) typ
  | Bottom, typ -> ()
  | Ref t, TApp(TRef, [typ]) ->
      check env t typ
  | Deref t, typ ->
      check env t (make_tref typ)
  | SetRef(t1,t2), TBase TUnit ->
      check env t1 (make_tref t2.typ);
      check env t2 t2.typ
  | TNone, TApp(TOption, _) -> ()
  | TSome t, TApp(TOption, [typ]) ->
      check env t typ
  | Module _, TModule _ -> () (* TODO *)
  | _, TData s when List.mem_assoc s env ->
      let typ = List.assoc s env in
      check env {t with typ} typ
  | _, TData _ -> () (* externally defined types *)
  | _ ->
      Format.eprintf "check': @[%a,@ %a@." Print.term' t (Color.yellow Print.typ) t.typ;
      assert false

let check ?(ty=Ty.unit) t = if Flag.Debug.check_typ then check [] t ty
