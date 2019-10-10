open Util
open CEGAR_syntax
open CEGAR_type
open CEGAR_print
open CEGAR_util

exception EvalFail
exception EvalValue
exception EvalSkip
exception EvalRestart
exception EvalTerminate

module S = Syntax

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let new_id' () =
  let x = "x" in
  new_id @@ Format.sprintf "%s_%d" x !Flag.Log.cegar_loop

let rec decomp_bool t =
  match t with
  | App(App(Const (And|Or), t1), t2) -> decomp_bool t1 @ decomp_bool t2
  | App(App(Const EqInt, t1), t2) when !Flag.PredAbst.decomp_eq_pred -> [make_leq t1 t2; make_geq t1 t2]
  | _ -> [t]

let rec merge_typ env typ typ' =
  match typ,typ' with
  | TBase(b1,ps), TApp(TConstr(TFixPred p), TBase(b2, _))
  | TApp(TConstr(TFixPred p), TBase(b1, _)), TBase(b2, ps) when b1 = b2 ->
      if ps (Var "x") <> [] then
        begin
          Debug.printf "typ: %a@." CEGAR_print.typ typ;
          Debug.printf "typ': %a@." CEGAR_print.typ typ';
          unsupported "merge_typ TFixPred"
        end;
      TApp(TConstr(TFixPred p), TBase(b1, fun _ -> []))
  | TBase(b1,ps1),TBase(b2,ps2) when b1 = b2 ->
      let x = !!new_id' in
      let ps1' = ps1 (Var x) in
      let ps2' = ps2 (Var x) in
      let ps2'' =
        if !Flag.PredAbst.decomp_pred then
          List.flatten_map decomp_bool ps2'
        else
          ps2'
      in
      let add p ps =
        let equiv t1 t2 =
          let t1' = FpatInterface.conv_formula t1 in
          let t2' = FpatInterface.conv_formula t2 in
          FpatInterface.implies [t1'] [t2'] &&
          FpatInterface.implies [t2'] [t1']
        in
        if List.exists (equiv p) ps then
          ps
        else
          normalize_bool_term p :: ps
      in
      let ps = List.fold_right add ps1' ps2'' in
      let ps t = List.map (subst x t) ps in
      TBase(b1, ps)
  | TFun(typ11,typ12), TFun(typ21,typ22) ->
      let x = !!new_id' in
      let env' = (x,typ11)::env in
      let typ12 = typ12 (Var x) in
      let typ22 = typ22 (Var x) in
      let typ1 = merge_typ env typ11 typ21 in
      let typ2 = merge_typ env' typ12 typ22 in
      TFun(typ1, subst_typ x -$- typ2)
  | TBase _, _
  | TFun _, _
  | TConstr _, _
  | TApp _, _ ->
      Format.eprintf "merge_typ: %a,%a@." CEGAR_print.typ typ CEGAR_print.typ typ';
      assert false

(* wrapper for debug *)
let merge_typ typ1 typ2 =
  try
    let r = merge_typ [] typ1 typ2 in
    Debug.printf "MERGE: @[%a@." CEGAR_print.typ typ1;
    Debug.printf "       @[%a@." CEGAR_print.typ typ2;
    Debug.printf "       @[%a@.@." CEGAR_print.typ r;
    r
  with _ when !!Debug.check ->
    Format.eprintf "Cannot merge@.  TYPE 1: %a@.  TYPE 2: %a@." CEGAR_print.typ typ1 CEGAR_print.typ typ2;
    assert false

let rec negate_typ = function
  | TBase(b,ps) -> TBase(b, List.map make_not -| ps)
  | TFun(typ1,typ2) ->
      let typ1 = negate_typ typ1 in
      let typ2 = negate_typ -| typ2 in
      TFun(typ1, typ2)
  | TConstr _ as typ -> Format.eprintf "negate_typ: %a." CEGAR_print.typ typ; assert false
  | TApp _ as typ -> Format.eprintf "negate_typ: %a." CEGAR_print.typ typ; assert false

let add_neg_preds_renv env =
  let aux (f,typ) = if is_randint_var f then (f, merge_typ typ (negate_typ typ)) else (f, typ) in
  List.map aux env

let nil_pred _ = []

let trans_var x = Id.to_string x
let trans_inv_var s = Id.from_string s Type.typ_unknown

let id_prog prog =
  let map = List.rev_map (fun (f,_) -> f, f) prog.env in
  let rmap = List.map (Pair.map_snd trans_inv_var) map in
  prog, map, rmap

(* for predicates *)
let rec trans_inv_term t =
  match t with
  | Const True -> Term_util.true_term
  | Const False -> Term_util.false_term
  | Const (Int n) -> Term_util.make_int n
  | Var x -> Term_util.make_var (trans_inv_var x)
  | App(Const Not, t) ->
      Term_util.make_not (trans_inv_term t)
  | App(App(Const op, t1), t2) ->
      let f =
        let open Term_util in
        match op with
        | And -> make_and
        | Or -> make_or
        | Lt -> make_lt
        | Gt -> make_gt
        | Leq|CmpPoly(_,"<=") -> make_leq (* ? *)
        | Geq -> make_geq
        | EqInt|EqBool -> make_eq
        | Add -> make_add
        | Sub -> make_sub
        | Mul -> make_mul
        | Div -> make_div
        | _ ->
            Format.eprintf "%a@." CEGAR_print.term t;
            assert false
      in
      f (trans_inv_term t1) (trans_inv_term t2)
  | t -> Format.eprintf "%a@." CEGAR_print.term t; assert false


let rec preds_of typ =
  match typ with
  | Type.TAttr(attr,_) ->
      begin
        let ypss = List.filter_map (function Type.TAPred(y,ps) -> Some (y,ps) | _ -> None) attr in
        match ypss with
        | [] -> fun _ -> []
        | [y,ps] ->
            let y' = trans_var y in
            let ps = List.map (snd -| trans_term "" [] []) ps in
            fun z -> List.map (subst y' z) ps
        | _ -> assert false
      end
  | _ -> fun _ -> []

and trans_typ ty =
  match ty with
  | Type.TBase Type.TUnit -> typ_unit
  | Type.TBase Type.TBool -> typ_bool ()
  | Type.TBase Type.TInt -> typ_int
  | Type.TBase (Type.TPrim s) -> TBase(TAbst s, nil_pred)
  | Type.TVar({contents=None},_) -> typ_int
  | Type.TVar({contents=Some typ},_) -> trans_typ typ
  | Type.TFun(x,typ) ->
      let typ1 = trans_typ @@ Id.typ x in
      let typ2 = trans_typ typ in
      TFun(typ1, subst_typ (trans_var x) -$- typ2)
  | Type.TData s -> TBase(TAbst s, nil_pred)
  | Type.TAttr([], typ) -> trans_typ typ
  | Type.TAttr(Type.TAId _::attrs, typ) -> trans_typ @@ Type.TAttr(attrs, typ)
  | Type.TAttr(Type.TAPredShare _::attrs, typ) -> trans_typ @@ Type.TAttr(attrs, typ)
  | Type.TAttr(Type.TARefPred(x,p)::attrs, typ) ->
      let p' y = subst (trans_var x) y @@ snd @@ trans_term "" [] [] p in
      TApp(TConstr (TFixPred p'), trans_typ @@ Type.TAttr(attrs,typ))
  | Type.TAttr(_, typ) when Term_util.get_tapred ty <> None ->
      let x,ps = Option.get @@ Term_util.get_tapred ty in
      begin
        let x' = trans_var x in
        let ps' =
          ps
          |> List.filter S.(function {desc=Const True} -> false | _ -> true)
          |> List.map (snd -| trans_term "" [] [])
        in
        match trans_typ @@ Type.elim_tattr @@ Id.typ x with
        | TBase(b, preds) ->
            let preds' y = List.map (subst x' y) ps' @ preds y in
            TBase(b, preds')
        | typ -> Format.eprintf "trans_typ[TPred]: %a@." CEGAR_print.typ typ; assert false
      end
  | Type.TTuple xs -> make_ttuple @@ List.map (trans_typ -| Id.typ) xs
  | typ ->
      Format.eprintf "trans_typ: %a@." Print.typ typ;
      assert false

and trans_binop = function
  | S.Eq -> assert false
  | S.Lt -> Const Lt
  | S.Gt -> Const Gt
  | S.Leq -> Const Leq
  | S.Geq -> Const Geq
  | S.And -> Const And
  | S.Or -> Const Or
  | S.Add -> Const Add
  | S.Sub -> Const Sub
  | S.Mult -> Const Mul
  | S.Div -> Const Div

and trans_const c typ =
  match c with
  | S.Unit -> Unit
  | S.True -> True
  | S.False -> False
  | S.Int n -> Int n
  | S.Char c -> Char c
  | S.String s -> String s
  | S.Float s -> Float s
  | S.Int32 n -> Int32 n
  | S.Int64 n -> Int64 n
  | S.Nativeint n -> Nativeint n
  | S.CPS_result -> CPS_result
  | S.Rand _ -> assert false

(** App(Temp e, t) denotes execution of App(t,Unit) after happening the event e *)
and trans_term post xs env t =
  match t.S.desc with
  | S.Const(S.Rand _) -> assert false
  | S.Const c -> [], Const (trans_const c t.S.typ)
  | S.App({S.desc=S.Const(S.Rand(Type.TBase Type.TInt,false)); S.attr}, [{S.desc=S.Const S.Unit}]) when List.mem S.AAbst_under attr ->
      unsupported "trans_term RandInt"
  | S.App({S.desc=S.Const(S.Rand(Type.TBase Type.TInt, true)); S.attr}, [t1;t2]) ->
      let under = List.mem S.AAbst_under attr in
      assert (t1.S.desc = S.Const S.Unit);
      let defs1,t1' = trans_term post xs env t1 in
      let defs2,t2' = trans_term post xs env t2 in
      let xs' = List.filter (fun x -> is_base @@ List.assoc x env) xs in
      let head = Const (Rand(TInt, if under then Some 0 else None)) in
      let args =if under then List.map _Var xs' @ [t2'] else [t2'] in
      defs1@defs2, make_app head args
  | S.App({S.desc=S.Const(S.Rand(Type.TData s, true))}, [t1]) ->
      assert false
  (*
      let defs1,t1' = trans_term post xs env t1 in
      defs1, App(t1', Const (RandVal s))
   *)
  | S.App({S.desc=S.Const(S.Rand(typ,true))}, [t1;t2]) ->
      assert (t1.S.desc = S.Const S.Unit);
      let defs1,t1' = trans_term post xs env t1 in
      let defs2,t2' = trans_term post xs env t2 in
      let base =
        match trans_typ typ with
        | TBase(base, _) -> base
        | _ -> assert false
      in
      defs1@defs2, App(t2', Const (Rand(base, None)))
  | S.Var x ->
      let x' = trans_var x in
      [], Var x'
  | S.App({S.desc=S.Event(s,false)}, [t]) ->
      let k = new_id "k" in
      assert (t = Term_util.unit_term);
      let defs = [k, TFun(typ_unit, fun _ -> typ_unit), ["u"], Const True, [], Const Unit] in
      defs, App(Const (Temp s), Var k)
  | S.App({S.desc=S.Event(s,true)}, [t1;t2]) ->
      assert (t1.S.desc = S.Const S.Unit);
      let defs1,t1' = trans_term post xs env t1 in
      let defs2,t2' = trans_term post xs env t2 in
      defs1@defs2, App(Const (Temp s), t2')
  | S.App(t, ts) ->
      let defs,t' = trans_term post xs env t in
      let defss,ts' = List.split_map (trans_term post xs env) ts in
      defs @ (List.flatten defss), make_app t' ts'
  | S.If(t1, t2, t3) ->
      let defs1,t1' = trans_term post xs env t1 in
      let defs2,t2' = trans_term post xs env t2 in
      let defs3,t3' = trans_term post xs env t3 in
      let f = new_id ("br" ^ post) in
      let x = new_id "b" in
      let typ0 = trans_typ t2.S.typ in
      let aux x typ2 = TFun(List.assoc x env, fun y -> subst_typ x y typ2) in
      let typ = List.fold_right aux xs typ0 in
      let typ' = TFun(typ_bool(), fun _ -> typ) in
      let def1 = f, typ', x::xs, Var x, [], t2' in
      let def2 = f, typ', x::xs, make_not (Var x), [], t3' in
      let t = List.fold_left (fun t x -> App(t,Var x)) (App(Var f,t1')) xs in
      def1::def2::defs1@defs2@defs3, t
  | S.Local _ -> assert false
  | S.BinOp(S.Eq, t1, t2) ->
      let defs1,t1' = trans_term post xs env t1 in
      let defs2,t2' = trans_term post xs env t2 in
      let op =
        match Type.elim_tattr t1.S.typ with
        | Type.TBase Type.TUnit -> EqUnit
        | Type.TBase Type.TBool -> EqBool
        | Type.TBase Type.TInt -> EqInt
        | Type.TBase (Type.TPrim ty) -> CmpPoly(ty, "=")
        | Type.TData ty -> CmpPoly(ty, "=")
        | typ -> Format.eprintf "trans_term: %a@." Print.typ typ; assert false
      in
      defs1@defs2, make_app (Const op) [t1'; t2']
  | S.BinOp(op, t1, t2) ->
      let defs1,t1' = trans_term post xs env t1 in
      let defs2,t2' = trans_term post xs env t2 in
      let op' =
        match t1.S.typ with
        | Type.TData typ -> Const (CmpPoly(typ, Print.string_of_binop op))
        | _ -> trans_binop op
      in
      defs1@defs2, make_app op' [t1'; t2']
  | S.Not t ->
      let defs,t' = trans_term post xs env t in
      defs, App(Const Not, t')
  | S.Fun _ -> assert false
  | S.Event _ -> assert false
  | S.Bottom -> [], Const Bottom
  | S.Proj(i, t) ->
      let defs,t' = trans_term post xs env t in
      defs, make_proj (Option.get @@ Type.tuple_num t.S.typ) i t'
  | S.Tuple ts ->
      let defss,ts' = List.split_map (trans_term post xs env) ts in
      List.flatten defss, make_tuple ts'
  | _ ->
      Format.eprintf "%a@." Print.term t;
      assert false

let rec formula_of t =
  match t.S.desc with
  | S.Const(S.Rand(Type.TBase Type.TInt,false)) -> raise Not_found
  | S.Const(S.Rand(Type.TBase Type.TInt,true)) -> assert false
  | S.Const c -> Const (trans_const c t.S.typ)
  | S.Var x -> Var (trans_var x)
  | S.App(t, ts) -> raise Not_found
  | S.If(t1, t2, t3) -> raise Not_found
  | S.Local _ -> assert false
  | S.BinOp(S.Eq, t1, t2) ->
      let t1' = formula_of t1 in
      let t2' = formula_of t2 in
      let op =
        match Type.elim_tattr t1.S.typ with
        | Type.TBase Type.TUnit -> EqUnit
        | Type.TBase Type.TBool -> EqBool
        | Type.TBase Type.TInt -> EqInt
        | Type.TBase (Type.TPrim ty) -> CmpPoly(ty, "=")
        | Type.TData ty -> CmpPoly(ty, "=")
        | _ -> Format.eprintf "%a@." Print.typ t1.S.typ; assert false
      in
      make_app (Const op) [t1'; t2']
  | S.BinOp(op, t1, t2) ->
      let t1' = formula_of t1 in
      let t2' = formula_of t2 in
      App(App(trans_binop op, t1'), t2')
  | S.Not t ->
      let t' = formula_of t in
      App(Const Not, t')
  | S.Proj _ -> raise Not_found
  | S.Tuple _ -> raise Not_found
  | _ -> Format.eprintf "formula_of: %a@." Print.constr t; assert false

let trans_def (f,(xs,t)) =
  let f' = trans_var f in
  let post = "_" ^ Id.name f in
  let xs' = List.map trans_var xs in
  let path = ref [] in
  let env =
    let aux x' x =
      let typ = trans_typ @@ Id.typ x in
      path := 1::!path;
      x', typ
    in
    List.map2 aux xs' xs
  in
  try
    (match t.S.desc with
     | S.If(t1, t2, t3) ->
	 let t1' = formula_of t1 in
	 let defs2,t2' = trans_term post xs' env t2 in
	 let defs3,t3' = trans_term post xs' env t3 in
         let typ' = trans_typ @@ Id.typ f in
	 ((f', typ', xs', t1', [], t2')::defs2) @
         ((f', typ', xs', make_not t1', [], t3')::defs3)
     | _ -> raise Not_found)
  with Not_found ->
    let defs,t' = trans_term post xs' env t in
    let typ' = trans_typ @@ Id.typ f in
    (f', typ', xs', Const True, [], t')::defs


let get_var_arity f env = get_typ_arity (List.assoc f env)

let rec is_CPS_value env = function
  | Const _
  | Var _ -> true
  | App(App(Const And, t1), t2)
  | App(App(Const EqUnit, t1), t2)
  | App(App(Const EqInt, t1), t2)
  | App(App(Const EqBool, t1), t2)
  | App(App(Const (CmpPoly _), t1), t2)
  | App(App(Const Or, t1), t2)
  | App(App(Const Lt, t1), t2)
  | App(App(Const Gt, t1), t2)
  | App(App(Const Leq, t1), t2)
  | App(App(Const Geq, t1), t2)
  | App(App(Const Add, t1), t2)
  | App(App(Const Sub, t1), t2)
  | App(App(Const Mul, t1), t2)
  | App(App(Const Div, t1), t2) -> is_CPS_value env t1 && is_CPS_value env t2
  | App(Const Not, t) -> is_CPS_value env t
  | App _ as t ->
      let t1,ts = decomp_app t in
      let n = match t1 with Var f -> get_var_arity f env | _ -> 0 in
        n > List.length ts && List.for_all (is_CPS_value env) ts
  | Let _ -> assert false
  | Fun _ -> assert false
let is_CPS_def env (f,xs,cond,es,t) =
  let env' = get_arg_env (List.assoc f env) xs @@@ env in
  let b1 = is_CPS_value env' cond in
  let b2 =
    match t with
        Const _ -> true
      | Var _ -> true
      | App _ -> List.for_all (is_CPS_value env') (snd (decomp_app t))
      | Let _ -> assert false
      | Fun _ -> assert false
  in
    b1 && b2
let is_CPS {env=env;defs=defs} = List.for_all (is_CPS_def env) defs




let event_of_temp {env;defs;main;info} =
  if List.mem ACPS info.attr
  then
    let make_event (f,xs,t1,e,t2) =
      assert (e = []);
      match t2 with
      | App(Const (Temp s), t2') when t1 = Const True || not @@ List.mem ACPS info.attr ->
          [], [f, xs, t1, [Event s], App(t2', Const Unit)]
      | App(Const (Temp s), t2') ->
          let g = new_id s in
          let u = new_id "u" in
          let k = new_id "k" in
          [g, TFun(typ_unit,fun _ -> TFun(TFun(typ_unit, fun _ -> typ_result), fun _ -> typ_result))],
          (* cannot refute if u is eliminated, because k cannot have predicates in current impl. *)
          [g, [u; k], Const True, [Event s], App(Var k, Const Unit);
           f, xs, t1, [], Term.(Var g @ [unit; t2'])]
      | _ -> [], [f, xs, t1, [], t2]
    in
    let envs,defss = List.split_map make_event defs in
    {env=List.flatten envs @@@ env; defs=List.flatten defss; main; info}
  else
    let rec aux = function
      | Const (Temp e) -> [e]
      | Const c -> []
      | Var x -> []
      | App(t1, t2) -> aux t1 @@@ aux t2
      | Fun _ -> assert false
      | Let _ -> assert false
    in
    let evts = List.unique @@ List.rev_map_flatten (fun (_,_,_,_,t) -> aux t) defs in
    let map = List.map (fun e -> e, new_id e) evts in
    let evt_env = List.map (fun (_,f) -> f, TFun(typ_unit, fun _ -> typ_unit)) map in
    let evt_defs = List.map (fun (e,f) -> f,["u"],Const True,[Event e],Const Unit) map in
    let rec aux = function
      | Const c -> Const c
      | Var x -> Var x
      | App(Const (Temp e), t) -> App(t, App(Var (List.assoc e map), Const Unit))
      | App(t1, t2) -> App(aux t1, aux t2)
      | Fun _ -> assert false
      | Let _ -> assert false
    in
    let defs' = List.map (map_body_def aux) defs in
    {env=evt_env@@@env; defs=evt_defs@@@defs'; main; info}


let rec uniq_env = function
  | [] -> []
  | (f,typ)::env ->
      if List.exists (fun (g,_) -> f = g) env
      then uniq_env env
      else (f,typ) :: uniq_env env


let remove_id_event = map_def_prog (fun (f,xs,t1,e,t2) -> f, xs, t1, List.remove_all e (Event "id"), t2)

let rename_prog prog =
  Debug.printf "@.BEFORE RENAMING:@.%a@." CEGAR_print.prog_typ prog;
  let vars = List.map (fun (f,_,_,_,_) -> f) prog.defs in
  let var_names = List.rev_map id_name (List.unique vars) in
  let rename_id' x var_names =
    let x_name = id_name x in
    if List.length (List.filter ((=) x_name) var_names) <= 1 &&
         x_name <> "l0" && x_name <> "l1" (* for labels in model-checking *)
    then x_name
    else rename_id x
  in
  let make_map_fun (f,_) =
    f, rename_id' f var_names
  in
  let fun_map = List.rev_map make_map_fun prog.env in
  List.iter (fun (f,f') -> Debug.printf "rename: %s ==> %s@." f f') fun_map;
  Debug.printf "@.";
  let rename_var map x = List.assoc_default x x map in
  let env = List.map (Pair.map_fst @@ rename_var fun_map) prog.env in
  let defs =
    let rename_def (f,xs,t1,e,t2) =
      Id.save_counter ();
      Id.clear_counter ();
      let var_names' =
        fun_map
        |> List.map snd
        |> (@@@) (List.rev_map id_name xs)
      in
      let arg_map =
        xs
        |> List.map (fun x -> x, rename_id' x var_names')
        |> List.unique ~eq:(Compare.eq_on fst)
        |> List.unique ~eq:(Compare.eq_on snd)
      in
      Debug.printf "f: %s@." f;
      List.iter (fun (f,f') -> Debug.printf "  rename: %s ==> %s@." f f') arg_map;
      Debug.printf "@.";
      let rename_term t =
        let smap = List.map (Pair.map_snd _Var) (arg_map @@@ fun_map) in
        subst_map smap t
      in
      let check_uniq xs = (* for debug *)
        let rec check xs =
          match xs with
          | [] -> ()
          | [_] -> ()
          | x1::(x2::_ as xs') -> assert (x1 <> x2); check xs'
        in
        check @@ List.sort compare xs
      in
      let def =
        rename_var fun_map f,
        List.map (rename_var arg_map) xs |@> check_uniq,
        rename_term t1,
        e,
        rename_term t2
      in
      Id.reset_counter();
      def
    in
    List.map rename_def prog.defs
  in
  let main = rename_var fun_map prog.main in
  let prog = {env; defs; main; info=prog.info} in
  Debug.printf "@.RENAMED:@.%a@." CEGAR_print.prog_typ prog;
  ignore @@ Typing.infer prog;
  let rmap = List.map (Pair.map_snd trans_inv_var) fun_map in
  prog, fun_map, rmap

let id_prog prog =
  let map = List.rev_map (fun (f,_) -> f, f) prog.env in
  let rmap = List.map (fun (f,f') -> f', trans_inv_var f) map in
  prog, map, rmap



module CRT = CEGAR_ref_type
module RT = Ref_type

let rec revert_typ ty =
  match ty with
  | TBase(TUnit, _) -> Type.Ty.unit
  | TBase(TBool, _) -> Type.Ty.bool
  | TBase(TInt, _) -> Type.Ty.int
  | TBase(TAbst s, _) -> Type.TData s
  | TConstr _ -> unsupported "CEGAR_trans.revert_typ: TConstr"
  | TApp _ -> unsupported "CEGAR_trans.revert_typ: TApp"
  | TFun(typ1, typ2) -> Type.TFun(Id.new_var (revert_typ typ1), revert_typ @@ typ2 @@ Const Unit)

let rec trans_ref_type = function
  | CRT.Base(b,x,p) ->
      let b' =
        match b with
        | CRT.Unit -> Type.TUnit
        | CRT.Bool -> Type.TBool
        | CRT.Int -> Type.TInt
        | CRT.Abst s -> Type.TPrim s
      in
      RT.Base(b', trans_inv_var x, trans_inv_term p)
  | CRT.Fun(x,typ1,typ2) ->
      RT.Fun(trans_inv_var x, trans_ref_type typ1, trans_ref_type typ2)
  | CRT.Inter(typ, typs) ->
      let typs' = List.map trans_ref_type typs in
      let typ' = revert_typ typ in
      RT.Inter(typ', typs')


let trans_term = trans_term "" [] []

let trans_prog ?(spec=[]) {Problem.term=t; attr} =
  let pr p s t = Debug.printf "##[trans_prog] %s:@.%a@.@." s p t in
  let pr1 = pr Print.term' in
  let pr2 = pr CEGAR_print.prog_typ in
  let main = new_id "main" in
  let (defs,t_main),get_rtyp =
    t
    |> Trans.trans_let
    |> Trans.remove_obstacle_type_attribute_for_pred_share
    |> Lift.lift
  in
  let defs_t,t_main' = trans_term t_main in
  let is_cps = List.mem Problem.ACPS attr in
  let defs' =
    let typ = if is_cps then typ_result else typ_unit in
    (main,typ,[],Const True,[],t_main') :: defs_t @ List.flatten_map trans_def defs
  in
  let env,defs'' = List.split_map (fun (f,typ,xs,t1,e,t2) -> (f,typ), (f,xs,t1,e,t2)) defs' in
  let env' = uniq_env env in
  let info =
    let attr = if is_cps then [ACPS] else [] in
    let pred_share =
      let aux (f,_) =
        let f' = trans_var f in
        Id.typ f
        |> Term_util.get_pred_share
        |> List.map (fun (prefix1,paths,prefix2) -> f', prefix1, paths, f', prefix2)
      in
      List.flatten_map aux defs
    in
    {init_info with attr; pred_share}
  in
  let max_id = List.fold_left (fun m x -> max m @@ snd @@ decomp_id x) 0 @@ List.flatten_map (fun (f,xs,_,_,_) -> f::xs) defs'' in
  Id.set_counter max_id;
  let prog,map,rmap =
    {env=env'; defs=defs''; main; info}
    |@> pr2 "PROG_A"
    |> event_of_temp
    |@> pr2 "PROG_B"
    |> eta_expand
    |@> pr2 "PROG_C"
    |> pop_main
    |@> pr2 "PROG_D"
    |> assign_id_to_rand
    |@> pr2 "PROG_E"
    |> remove_id_event
    |@> pr2 "PROG_F"
    |> id_prog
  in
  let rrmap = List.map Pair.swap rmap in
  let make_get_rtyp get_rtyp f =
    Debug.printf "make_get_rtyp f: %a@." Print.id f;
    Id.assoc f rrmap
    |@> Debug.printf "rrmap(f): %a@." CEGAR_print.var
    |> get_rtyp
    |@> Debug.printf "get_rtyp rrmap(f): %a@." CEGAR_ref_type.print
    |> trans_ref_type
    |@> Debug.printf "trans_ref_type get_rtyp rrmap(f): %a@." Ref_type.print
  in
  prog, map, rmap, make_get_rtyp

let add_env spec prog =
  let env =
    let spec' = List.map (Pair.map trans_var trans_typ) spec in
    let aux (f,typ) =
      let ty =
        try
          merge_typ typ @@ List.assoc f spec'
        with
          Not_found -> typ
      in
      f, ty
    in
    uniq_env @@ List.map aux prog.env
  in
  {prog with env}


let assoc_def_aux defs n t =
  let defs' = List.filter (fun (f,_,_,_,_) -> Var f = t) defs in
    List.nth defs' n

let assoc_def labeled t ce defs =
  if List.exists (fun f -> Var f = t) labeled
  then List.tl ce, assoc_def_aux defs (List.hd ce) t
  else ce, assoc_def_aux defs 0 t


let rec is_value env = function
  | Const Bottom -> false
  | Const (Rand(TBool,_)) -> false
  | Const _ -> true
  | Var x -> get_arg_num (get_typ env (Var x)) > 0
  | App(App(App(Const If, _), _), _) -> false
  | App _ as t ->
      let t1,ts = decomp_app t in
        List.for_all (is_value env) (t1::ts) && get_arg_num (get_typ env t) = List.length ts
  | Let _ -> assert false
  | Fun _ -> assert false

let rec read_bool () =
  Format.printf "RandBool (t/f/r/s): @?";
  match read_line () with
  | "t" -> true
  | "f" -> false
  | "r" -> raise EvalRestart
  | "s" -> raise EvalSkip
  | s -> read_bool ()

let rec step_eval_abst_cbn ce labeled env_abst defs = function
  | Const Bottom -> raise TypeBottom
  | Const (Rand(TBool,_)) ->
      let t =
        if read_bool ()
        then Const True
        else Const False
      in
      ce, t
  | Const Unit -> ce, Const Unit
  | Var x ->
      let ce',(f,xs,tf1,es,tf2) = assoc_def labeled (Var x) ce defs in
      assert (tf1 = Const True);
      if List.mem (Event "fail") es then raise EvalFail;
      ce', tf2
  | App(App(App(Const If, Const True), t2), _) -> ce, t2
  | App(App(App(Const If, Const False), _), t3) -> ce, t3
  | App(App(App(Const If, t1), t2), t3) ->
      let ce',t1' = step_eval_abst_cbn ce labeled env_abst defs t1 in
      ce', App(App(App(Const If, t1'), t2), t3)
  | App(Const (Label n), t) ->
      step_eval_abst_cbn ce labeled env_abst defs t
  | App _ as t ->
      let t1,ts = decomp_app t in
      if t1 = Const If
      then
        match ts with
          t1::t2::t3::ts' ->
          let t2' = make_app t2 ts' in
          let t3' = make_app t3 ts' in
          step_eval_abst_cbn ce labeled env_abst defs (make_if t1 t2' t3')
        | _ -> assert false
      else
        let ce',(f,xs,tf1,es,tf2) = assoc_def labeled t1 ce defs in
        let ts1,ts2 = List.split_nth (List.length xs) ts in
        assert (tf1 = Const True);
        if List.mem (Event "fail") es then raise EvalFail;
        ce', make_app (List.fold_right2 subst xs ts1 tf2) ts2
  | _ -> assert false

let rec eval_abst_cbn prog labeled abst ce =
  Format.printf "Program with abstraction types::@.%a@." CEGAR_print.prog abst;
  Format.printf "CE: %a@." CEGAR_print.ce ce;
  let env_orig = prog.env in
  let env_abst = abst.env in
  let defs = abst.defs in
  let main = abst.main in
  let ce' = ce in
  let rec loop ce t =
    Format.printf "%a -->@\n" CEGAR_print.term t;
    assert (match get_typ env_abst t with TBase(TUnit,_) -> true | _ -> false);
    begin
      try
        match decomp_app t with
          Var x, _ ->
          Format.printf "  %s:: %a@\n" x CEGAR_print.typ (List.assoc x env_orig)
        | _ -> ()
      with Not_found -> ()
    end;
    let ce',t' = step_eval_abst_cbn ce labeled env_abst defs t in
    if t' = Const Unit then raise EvalTerminate;
    loop ce' t'
  in
  let rec confirm () =
    Format.printf "(s)kip/(r)estart: @?";
    match read_line () with
    | "s" -> ()
    | "r" -> eval_abst_cbn prog labeled abst ce
    | s -> confirm ()
  in
  Format.printf "Evaluation of abstracted program::@.";
  try
    loop ce' (Var main)
  with
  | EvalRestart -> eval_abst_cbn prog labeled abst ce
  | EvalFail ->
      Format.printf "ERROR!@.@.";
      confirm ()
  | EvalSkip -> ()
  | EvalTerminate ->
      Format.printf "TERMINATES!@.@.";
      confirm ()
  | TypeBottom ->
      Format.printf "DIVERGES!@.@.";
      confirm ()







let assoc_def labeled defs ce acc rand_num t =
  if ce = [] && Flag.(Method.(!mode = FairNonTermination) && !FairNonTermination.break_expansion_ref) then
    None
  else
    let f = match t with Var f -> f | _ -> assert false in
    let defs' = List.filter (fun (g,_,_,_,_) -> g = f) defs in
    let aux (_,_,_,_,t) = (* In fair nonterm mode, trans_ce ends just before 'read_int' *)
      rand_num = Some 0 && is_app_read_int t in
    if List.mem f labeled
    then
      if ce = [] then
        None
      else
        let c = List.hd ce in
        let ce' = List.tl ce in
        let acc' = c::acc in
        let def = List.nth defs' c in
        if aux def then
          None
        else
          Some (ce', acc', def)
    else
      let acc' = 0::acc in
      let def = List.hd defs' in
      assert (List.length defs' = 1);
      if aux def then
        None
      else
        Some(ce, acc', def)

let init_cont _ acc _ _ = List.rev acc

let rec trans_ce_aux labeled ce acc defs rand_num t k =
  Debug.printf "trans_ce_aux[%d,%d]: %a@." (List.length ce) (List.length acc) CEGAR_print.term t;
  match t with
  | Const (Rand(TInt, _)) -> assert false
  | Const c -> k ce acc rand_num (Const c)
  | Var x -> k ce acc rand_num (Var x)
  | App(Const Not, t) ->
      trans_ce_aux labeled ce acc defs rand_num t (fun ce acc rand_num t ->
      k ce acc rand_num (make_app (Const Not) [t]))
  | App(App(Const (And|Or|Lt|Gt|Leq|Geq|EqUnit|EqBool|EqInt|Add|Sub|Mul|Div as op),t1),t2) ->
      trans_ce_aux labeled ce acc defs rand_num t1 (fun ce acc rand_num t1 ->
      trans_ce_aux labeled ce acc defs rand_num t2 (fun ce acc rand_num t2 ->
      k ce acc rand_num (make_app (Const op) [t1;t2])))
  | App _ when is_app_randint t ->
      let _,ts = decomp_app t in
      let t' = List.last ts in
      let r = new_id "r" in
      let rand_num' =
        if is_app_read_int t then
          Option.map pred rand_num
        else rand_num in
      if rand_num = Some 0 then (* fair non-termination *)
        init_cont ce acc rand_num' t
      else
        trans_ce_aux labeled ce acc defs rand_num' (App(t', Var r)) k
  | App(t1,t2) ->
      trans_ce_aux labeled ce acc defs rand_num t1 (fun ce acc rand_num t1 ->
      trans_ce_aux labeled ce acc defs rand_num t2 (fun ce acc rand_num t2 ->
      let t1',ts = decomp_app (App(t1,t2)) in
      let _,xs,_,_,_ = List.find (fun (f,_,_,_,_) -> Var f = t1') defs in
      if List.length xs > List.length ts
      then k ce acc rand_num (App(t1,t2))
      else
         match assoc_def labeled defs ce acc rand_num t1' with
          | None ->
             init_cont ce acc rand_num t1'
          | Some (ce',acc',(f,xs,tf1,e,tf2)) ->
             let ts1,ts2 = List.split_nth (List.length xs) ts in
             let aux = List.fold_right2 subst xs ts1 in
             let tf2' = make_app (aux tf2) ts2 in
             assert (List.length xs = List.length ts);
             if e = [Event "fail"]
             then init_cont ce' acc' rand_num tf2'
             else trans_ce_aux labeled ce' acc' defs rand_num tf2' k))
  | Let _ -> assert false
  | Fun _ -> assert false

let trans_ce labeled {defs; main} ce rand_num =
  let _,_,_,_,t = List.find (fun (f,_,_,_,_) -> f = main) defs in
  let ce' = trans_ce_aux labeled ce [] defs rand_num t init_cont in
  assert (not (List.mem main labeled));
  0::ce'

let eq_not t1 t2 = t1 = make_not t2 || make_not t1 = t2

let rec has_rand t =
  match t with
  | Const (Rand(_,_)) -> true
  | Const _ -> false
  | Var _ -> false
  | App(t1,t2) -> has_rand t1 || has_rand t2
  | Let(_,t1,t2) -> has_rand t1 || has_rand t2
  | Fun(_, _, t) -> has_rand t


let implies env t =
  try
    let pre = List.map FpatInterface.conv_formula env in
    let p = FpatInterface.conv_formula t in
    FpatInterface.implies pre [p]
  with _ -> false

(* fv = FV(env) *)
let rec simplify_if_term env fv t =
  match t with
  | Const c -> Const c
  | Var x -> Var x
  | App(App(App(Const If, Const True), t2), t3) ->
      simplify_if_term env fv t2
  | App(App(App(Const If, Const False), t2), t3) ->
      simplify_if_term env fv t3
  | App(App(App(Const If, t1), t2), t3) ->
      let add_env t env = if has_rand t then env else t::env in
      let t1' =
        t1
        |> simplify_if_term env fv
        |> normalize_bool_term
      in
      let fv_t1 = get_fv t1' in
      let fv' = fv_t1 @ fv in
      let b = List.Set.inter fv fv_t1 <> [] in
      if b && implies env t1' then
        simplify_if_term env fv t2
      else if b && implies env (make_not t1') then
        simplify_if_term env fv t3
      else
        let t2' = simplify_if_term (add_env t1' env) fv' t2 in
        let t3' = simplify_if_term (add_env (make_not t1') env) fv' t3 in
        let t1'',t2'',t3'' =
          match t1' with
          | App(Const Not, t1'') -> t1'', t3', t2'
          | _ -> t1', t2', t3'
        in
        make_if t1'' t2'' t3''
  | App(t1,t2) -> App(simplify_if_term env fv t1, simplify_if_term env fv t2)
  | Let(x, t1, t2) -> Let(x, simplify_if_term env fv t1, simplify_if_term env fv t2)
  | Fun(x,typ,t) -> Fun(x, typ, simplify_if_term env fv t)
let simplify_if_term t = simplify_if_term [] [] t

let simplify_if {env; defs; main; info} =
  let defs' = List.map (fun (f,xs,t1,e,t2) -> f, xs, simplify_if_term t1, e, simplify_if_term t2) defs in
  {env; defs=defs'; main; info}


let add_fail_to_end prog =
  let aux (f, args, cond, e, t) =
    if t = Const(CPS_result)
    then (f, args, cond, [Event "fail"], t)
    else (f, args, cond, e, t)
  in
  map_def_prog aux prog


let rec beta_subst_aux x (y,t1) t2 =
  match t2 with
  | Const c -> Const c
  | Var y when x = y -> t1
  | Var y -> Var y
  | App(t21,t22) ->
      let t21' = beta_subst_aux x (y,t1) t21 in
      let t22' = beta_subst_aux x (y,t1) t22 in
      begin
        match t21' with
        | Fun(y',_,t211) -> beta_subst y' t22' t211
        | _ -> App(t21', t22')
      end
  | Let(y,t21,t22) ->
      let t22' =
        if x = y then
          t22
        else
          beta_subst_aux x (y,t1) t22
      in
      Let(y, beta_subst_aux x (y,t1) t21, t22')
  | Fun(y,typ,t21) ->
      let t21' =
        if x = y then
          t1
        else
          beta_subst_aux x (y,t1) t21
      in
      Fun(y, typ, t21')
and beta_subst x t1 t2 =
  match t1 with
  | Fun(y,_,t11) -> beta_subst_aux x (y,t11) t2
  | _ -> subst x t1 t2
