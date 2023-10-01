open Util
open Type
open Syntax
open Type_util
open Term_util

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type env =
  {mutable constraints: (effect * effect) list;
   mutable counter: int;
   for_cps: bool}

let initial_env for_cps =
  let counter = 0 in
  let constraints = [] in
  {counter; constraints; for_cps}

let new_evar env =
  env.counter <- env.counter + 1;
  EVar env.counter

let add_effect_typ es ty =
  _TAttr [TAEffect es] ty

let add_constr es1 es2 env =
  List.iter (fun e1 -> List.iter (fun e2 -> env.constraints <- (e1,e2)::env.constraints) es2) es1

let rec make_template env ty =
  let ty' =
    match ty with
    | TBase _ -> ty
    | TFun(x, ty2) ->
        let x' = Id.map_typ (make_template env) x in
        let ty2' = make_template env ty2 in
        (if env.for_cps then
           match elim_tattr ty2 with
           | TBase _ -> add_constr [EEvent] (effect_of_typ ty2') env
           | _ -> ());
        TFun(x', ty2')
    | TTuple xs -> TTuple (List.map (Id.map_typ (make_template env)) xs)
    | TAttr(attr, ty1) -> _TAttr attr (make_template env ty1)
    | TConstr(s,tys) -> TConstr(s, List.map (make_template env) tys)
    | _ -> unsupported "Effect.make_template (%a)" Print.typ ty
  in
  match ty with
  | TAttr _ -> ty'
  | _ -> add_effect_typ [new_evar env] ty'

let set_effect es t =
  let ty =
    match t.typ with
    | TAttr(TAEffect _::attrs, ty1) -> TAttr(TAEffect es::attrs, ty1)
    | _ -> add_effect_typ es t.typ
  in
  add_attr (AEffect es) (Syntax.set_typ t ty)

let add_evar env t =
  let typ = make_template env t.typ in
  let es = effect_of_typ typ in
  set_effect es @@ make t.desc typ

let rec force_cont ty =
  let attrs,ty1 =
    match ty with
    | TAttr(attrs, ty1) ->
        List.map (function TAEffect _ -> TAEffect [EEvent] | a -> a) attrs,
        ty1
    | _ ->
        assert false
  in
  let ty1' =
    match ty1 with
    | TBase _ -> ty
    | TFun(x, ty2) -> TFun(Id.map_typ force_cont x, force_cont ty2)
    | TTuple xs -> TTuple (List.map (Id.map_typ force_cont) xs)
    | TAttr _ -> assert false
    | _ -> unsupported "%s (%a)" __FUNCTION__  Print.typ ty1
  in
  TAttr(attrs, ty1')

let rec flatten_sub ?(ignore_top=false) env ty1 ty2 =
  if not ignore_top then
    add_constr (effect_of_typ ty1) (effect_of_typ ty2) env;
  match elim_tattr ty1, elim_tattr ty2 with
  | TBase _, _ -> ()
  | TFun(x1,ty12), TFun(x2,ty22) ->
      flatten_sub_var ~ignore_top:true env x2 x1;
      flatten_sub env ty12 ty22
  | TFun _, _ -> [%invalid_arg]
  | TTuple xs1, TTuple xs2 ->
      List.iter2 (flatten_sub_var env) xs1 xs2
  | TTuple _, _ -> [%invalid_arg]
  | TConstr(c1, [ty1]), TConstr(c2, [ty2]) when Path.(c1 = C.set && c2 = C.set) ->
      flatten_sub env ty1 ty2
  | TAttr _, _ -> [%invalid_arg]
  | ty1, _ ->
      unsupported "%s (%a)" __FUNCTION__ Print.typ ty1
and flatten_sub_var ?(ignore_top=false) env x y = flatten_sub ~ignore_top env (Id.typ x) (Id.typ y)

let get_tfun_effect ty =
  match elim_tattr ty with
  | TFun(_, ty2) -> effect_of_typ ty2
  | _ -> assert false

let rec gen_constr env tenv t =
  let flatten_sub' t ?(ignore_top=false) env ty1 ty2 =
    Dbg.printf "[%a] @[%a@ <: %a@." Print.term t Print.typ ty1 Print.typ ty2;
    flatten_sub ~ignore_top env ty1 ty2
  in
  let gen2 t1 t2 f =
    let t1' = gen_constr env tenv t1 in
    let t2' = gen_constr env tenv t2 in
    let typ = make_template env t.typ in
    let es = effect_of_typ typ in
    add_constr (effect_of t1') es env;
    add_constr (effect_of t2') es env;
    Some es, make (f t1' t2') typ
  in
  let es,t' =
    match t.desc with
    | Const (Rand(_, false)) ->
        let t' = add_evar env t in
        let e = get_tfun_effect t'.typ in
        add_constr [ENonDet] e env;
        None, t'
    | Const (Rand(_, true)) -> [%unsupported]
    | Const _ -> None, add_evar env t
    | Bottom ->
        let t' = add_evar env t in
        let es = effect_of t' in
        add_constr [EDiv] es env;
        None, t'
    | Var (LId x) ->
        let typ =
	  try
	    Id.List.assoc x tenv
	  with
	  | Not_found when Fpat.RefTypInfer.is_parameter (Id.name x) ->
              add_effect_typ [] Ty.int
	  | Not_found ->
              Format.eprintf "%a@." Print.id x;
              assert false
        in
        let x' = Id.set_typ x typ in
        Some [], Term.var x'
    | Fun(x, t1) ->
        let x_typ = make_template env (Id.typ x) in
        let x' = Id.set_typ x x_typ in
        let tenv' = (x, x_typ) :: tenv in
        let t1' = gen_constr env tenv' t1 in
        Some [], Term.fun_ x' t1'
    | App(_, []) -> assert false
    | App(t1, t2::t3::ts) ->
        let typ = (make_app_raw t1 [t2]).typ in
        let t12 = make (App(t1,[t2])) typ in
        let t' = make (App(t12, t3::ts)) t.typ in
        None, gen_constr env tenv t'
    | App(t1, [t2]) ->
        let t1' = gen_constr env tenv t1 in
        let t2' = gen_constr env tenv t2 in
        let ty_arg,es1 =
          match elim_tattr t1'.typ with
          | TFun(x,ty2) -> Id.typ x, effect_of_typ ty2
          | _ -> assert false
        in
        let e = new_evar env in
        add_constr es1 [e] env;
        add_constr (effect_of t1') [e] env;
        add_constr (effect_of t2') [e] env;
        flatten_sub' t ~ignore_top:true env t2'.typ ty_arg;
        Some [e], make_app t1' [t2']
    | If(t1, t2, t3) ->
        let t1' = gen_constr env tenv t1 in
        let t2' = gen_constr env tenv t2 in
        let t3' = gen_constr env tenv t3 in
        let typ = make_template env t.typ in
        let es = effect_of_typ typ in
        add_constr (effect_of t1') es env;
        flatten_sub' t env t2'.typ typ;
        flatten_sub' t env t3'.typ typ;
        if env.for_cps then add_constr [EEvent] es env;
        Some es, make (If(t1', t2', t3')) typ
    | Local(Decl_let bindings, t1) ->
        let tenv' =
          let make_env = fst |- Pair.add_right (make_template env -| Id.typ) in
          List.map make_env bindings @@@ tenv
        in
        let e = new_evar env in
        let bindings' =
           bindings
           |> List.map (fun (f, t1) ->
               let f_typ = Id.List.assoc f tenv' in
               let f' = Id.set_typ f f_typ in
               let t1' = gen_constr env tenv' t1 in
               let rec aux_div t =
                 match t.desc with
                 | Fun(_,t') -> aux_div t'
                 | _ when Id.List.mem f' (get_fv ~force:true t) -> add_constr [EDiv] (effect_of t) env
                 | _ -> ()
               in
               aux_div t1';
               flatten_sub' t env t1'.typ f_typ;
               add_constr (effect_of t1') [e] env;
               f', t1')
        in
        let t1' = gen_constr env tenv' t1 in
        add_constr (effect_of t1') [e] env;
        let typ = add_effect_typ [e] @@ elim_tattr t1'.typ in
        Some [e], make (Local(Decl_let bindings', t1')) typ
    | BinOp(op, t1, t2) ->
        gen2 t1 t2 (_BinOp op)
    | Not t1 ->
        let t1' = gen_constr env tenv t1 in
        let typ = make_template env t.typ in
        let es = effect_of_typ typ in
        add_constr (effect_of t1') es env;
        Some es, make (Not t1') typ
    | Event(_,true) -> [%unsupported]
    | Event(_,false) ->
        let t' = add_evar env t in
        let es = get_tfun_effect t'.typ in
        add_constr [EEvent] es env;
        None, t'
    | Proj(i,t1) ->
        let t1' = gen_constr env tenv t1 in
        let typ = make_template env t.typ in
        let es = effect_of_typ typ in
        add_constr (effect_of t1') es env;
        flatten_sub' t env (Type_util.proj_typ i t1'.typ) typ;
        Some es, make (Proj(i,t1')) typ
    | Tuple ts ->
        let ts' = List.map (gen_constr env tenv) ts in
        let ty = make_template env t.typ in
        let es = effect_of_typ ty in
        let ty' = make_ttuple @@ List.map Syntax.typ ts' in
        flatten_sub' t ~ignore_top:true env ty' ty;
        List.iter (fun t -> add_constr (effect_of t) es env) ts';
        Some es, make (Tuple ts') ty
    | TryWith(t1, t2) ->
        let t1' = gen_constr env tenv t1 in
        let t2' = gen_constr env tenv t2 in
        let ty = make_template env t2.typ in
        let _ty_exn, ty' = Type.ValE._TFun @@ elim_tattr ty in
        let es = effect_of_typ ty in
        flatten_sub' t env t1'.typ ty';
        flatten_sub' t env t2'.typ ty;
        add_constr (effect_of t1') es env;
        add_constr (effect_of_typ ty) es env;
        Some es, make (TryWith(t1',t2')) ty'
    | Raise t1 ->
        let t1' = gen_constr env tenv t1 in
        let ty = make_template env t.typ in
        let es = effect_of_typ ty in
        add_constr [EExcep] es env;
        Some es, make (Raise t1') ty
    | MemSet(t1, t2) -> gen2 t1 t2 _MemSet
    | AddSet(t1, t2) -> gen2 t1 t2 _AddSet
    | Subset(t1, t2) -> gen2 t1 t2 _Subset
    | _ ->
        Format.eprintf "%a@." Print.term t;
        assert false
  in
  t'
  |> add_attrs t.attr
  |> Option.map_default set_effect Fun.id es


let solve env =
  let n = env.counter + 1 in
  let upper = Array.make n [] in
  let sol = Array.make n [] in
  let init (nondets,events,divs,exceps) (x,y) =
    match x,y with
    | EVar i,  EVar j -> upper.(i) <- j::upper.(i); nondets, events, divs, exceps
    | ENonDet, EVar i -> i::nondets, events, divs, exceps
    | EEvent,  EVar i -> nondets, i::events, divs, exceps
    | EDiv,    EVar i -> nondets, events, i::divs, exceps
    | EExcep,  EVar i -> nondets, events, divs, i::exceps
    | _ ->
        unsupported "Effect.infer: external functions with raise-throwable function arguments?"
  in
  let nondets,events,divs,exceps = List.fold_left init ([],[],[],[]) env.constraints in
  Dbg.printf "nondets: %a@." (List.print Format.pp_print_int) nondets;
  Dbg.printf "events: %a@." (List.print Format.pp_print_int) events;
  Dbg.printf "divs: %a@." (List.print Format.pp_print_int) divs;
  Dbg.printf "exceps: %a@." (List.print Format.pp_print_int) exceps;
  let set c xs = List.iter (fun y -> sol.(y) <- c::sol.(y)) xs in
  let rec solve c rest =
    match rest with
    | [] -> ()
    | x::rest' ->
        let up = List.filter (fun y -> not @@ List.mem c sol.(y)) upper.(x) in
        Dbg.printf "up: %a@." (List.print Format.pp_print_int) up;
        set c up;
        solve c (up@rest')
  in
  let solve' c xs =
    solve c xs;
    set c xs
  in
  solve' EExcep exceps;
  solve' EEvent events;
  solve' ENonDet nondets;
  solve' EDiv divs;
  Array.iteri (fun i x -> Dbg.printf  "  e_%d := %a@." i (Print.list Print_typ.effect) x) sol;
  fun x ->
    if x < 0 || n < x then invalid_arg "solve";
    sol.(x)



let apply_sol =
  let app = Tr2.make () in
  let tr_effects sol es =
    es
    |> List.flatten_map (function EVar x -> sol x | e -> [e])
    |> List.unique
  in
  let tr_attr sol attrs =
    let aux = function
      | AEffect es -> AEffect (tr_effects sol es)
      | a -> a
    in
    List.map aux attrs
  in
  let tr_typ sol ty =
    match ty with
    | TAttr(attrs, ty1) ->
        let attrs' = List.map (function TAEffect es -> TAEffect(tr_effects sol es) | a -> a) attrs in
        let ty1' = app.typ sol ty1 in
        TAttr(attrs', ty1')
    | _ -> app.typ_rec sol ty
  in
  app.attr <- tr_attr;
  app.typ <- tr_typ;
  app.term



let infer ?(for_cps=false) t =
  let env = initial_env for_cps in
  let ext_funs =
    let eq x y = Id.(x = y) && (can_unify (Id.typ x) (Id.typ y) || Id.typ x = Id.typ y) in
    get_fv_unique ~eq ~force:true t
  in
  if List.length ext_funs <> List.length (List.unique ~eq:Id.eq ext_funs) then
    begin
      Format.eprintf "External functions:@.";
      ext_funs
      |> List.sort compare
      |> List.iter (Format.eprintf "  %a@." Print.id_typ);
      unsupported "Effect: polymorphic use of external functions";
    end;
  let tenv =
    let make x =
      x
      |> Id.typ
      |> make_template env
      |&for_cps&> force_cont
    in
    List.map (Pair.add_right make) ext_funs
  in
  let t' = gen_constr env tenv t in
  Dbg.printf "Add evar: %a@." Print.term' t';
  Dbg.printf "CONSTRAINTS:@.";
  List.iter (fun (e1,e2) -> Dbg.printf "  %a <: %a@." Print_typ.effect e1 Print_typ.effect e2) env.constraints;
  Dbg.printf "@.";
  let sol = solve env in
  apply_sol sol t'





let mark =
  let tr = Tr.make () in
  let rec can_have_pred ty =
    match decomp_tattr ty with
    | attrs, TBase _ -> List.for_all (function TARefPred _ -> false | _ -> true) attrs
    | _, TTuple xs -> List.exists (can_have_pred -| Id.typ) xs
    | _ -> false
  in
  let mark_id x =
    let ty = Id.typ x in
    let ty' =
      if is_base_typ (Id.typ x) then
        _TAttr [TARefPred(Id.new_var_id x, Term.true_)] ty
      else
        ty
    in
    Id.set_typ x ty'
  in
  tr.term <- (fun t ->
    match t.desc with
    | Const (Dummy _) ->
        let desc = Const (Dummy t.typ) in
        tr.term_rec (set_desc t desc)
          [@alert "-unsafe"]
    | _ -> tr.term_rec t);
  tr.typ <- (fun ty ->
    match ty with
    | _ when is_base_typ ty -> ty
    | TTuple xs ->
        let xs' = List.map tr.var xs in
        let xs'' =
          let mark x acc =
            let x' =
              if can_have_pred (TTuple acc) then
                mark_id x
              else
                x
            in
            x'::acc
          in
          List.fold_right mark xs' []
        in
        TTuple xs''
    | TAttr(attr, TFun(x,ty2)) when List.mem TAPureFun attr ->
        let x' = mark_id @@ tr.var x in
        TAttr(attr, TFun(x', tr.typ ty2))
    | TFun(x,ty2) ->
        let ty2' = tr.typ ty2 in
        let x' = tr.var x in
        let x'' =
          if [] = effect_of_typ ty2 && can_have_pred ty2' then
            mark_id x'
          else
            x'
        in
        TFun(x'', ty2')
    | _ -> tr.typ_rec ty);
  tr.attr <- Fun.id;
  tr.term

let mark_safe_fun_arg t =
  t
  |> Trans.instansiate_randval (* To remove rand_val[... -> ...] *)
  |> Trans.remove_match
  |> infer
  |@> Dbg.printf "INFERRED: %a@." Print.term'
  |> mark
  |> Trans.remove_effect_attribute
  |> Trans.reconstruct
  |@> Dbg.printf "MARKED: %a@." Print.term'
