open Syntax
open Term_util
open Type
open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type env =
  {constr: (int * int) list;
   counter: int;
   tenv: (id * typ) list;
   fv: id list;
   ty_exn: typ option}

(* id 0 represents "CARE"*)
let initial_env fv =
  let counter = 1 in
  let constr = [] in
  let tenv = [] in
  let ty_exn = None in
  {counter; constr; tenv; fv; ty_exn}

let new_id env =
  let counter = env.counter + 1 in
  {env with counter}, counter

let label = "slice"
let _TAId id = TAId(label,id)

let add_id id ty =
  _TAttr [_TAId id] ty

let add_new_id env ty =
  let env', id = new_id env in
  env', add_id id ty

(** `add_constr l1 l2` means if `l1` is used then so is `l2` *)
let add_constr l1 l2 env =
  Debug.printf "ADD_CONSTR: %d <: %d@." l1 l2;
  {env with constr = (l1,l2)::env.constr}

let get_id_attr attrs =
  List.get @@ List.filter_map (function TAId(s,x) when s = label -> Some x | _ -> None) attrs

let get_id ty =
  ty
  |> decomp_tattr
  |> fst
  |> get_id_attr

let set_id id ty =
  let attr,ty' = decomp_tattr ty in
  let attr' = List.map (function TAId(s,_) when s = label -> TAId(label,id) | a -> a) attr in
  TAttr(attr', ty')

let force ty ?(default=0) env =
  ty
  |> col_tid
  |> List.filter_map (fun (s,l) -> if s=label then Some l else None)
  |> List.fold_left (fun env l -> add_constr l default env) env

let rec make_template env ty =
  match ty with
  | TBase _ -> add_new_id env ty
  | TVar _ -> unsupported __MODULE__
  | TFun(x, ty2) ->
      let env,ty = make_template env @@ Id.typ x in
      let x' = Id.set_typ x ty in
      let env,ty2' = make_template env ty2 in
      let env,l = new_id env in
      env, _TAttr [TAId(label,l)] @@ TFun(x', ty2')
  | TTuple xs ->
      let env,l = new_id env in
      let env,xs' =
        let aux (env,xs) x =
          let env,ty = make_template env @@ Id.typ x in
          let x' = Id.set_typ x ty in
          let env = add_constr l (get_id ty) env in
          env, xs@[x']
        in
        List.fold_left aux (env,[]) xs
      in
      env, _TAttr [_TAId l] @@ TTuple xs'
  | TAttr(attr, ty1) ->
      let env,ty1' = make_template env ty1 in
      env, _TAttr attr ty1'
  | TFuns _ -> unsupported __MODULE__
  | TData _ -> unsupported __MODULE__
  | TVariant _ -> unsupported __MODULE__
  | TRecord _ -> unsupported __MODULE__
  | TApp(s,tys) ->
      let env,l = new_id env in
      let env,tys' =
        let aux (env,tys) ty =
          let env,ty' = make_template env ty in
          let env = add_constr l (get_id ty') env in
          env, tys@[ty']
        in
        List.fold_left aux (env,[]) tys
      in
      env, _TAttr [_TAId l] @@ TApp(s,tys')
  | TModule _ -> unsupported __MODULE__

let get_ty_exn env ty =
  match env.ty_exn with
  | None ->
      let env,ty_exn = make_template env ty in
      Debug.printf "ty_exn: %a@." Print.typ ty_exn;
      {env with ty_exn=Some ty_exn}, ty_exn
  | Some ty_exn ->
      env, ty_exn

let flatten_sub_attr attr1 attr2 env =
  let x = get_id_attr attr1 in
  let y = get_id_attr attr2 in
  add_constr x y env

let rec flatten_sub ty1 ty2 constr =
  Debug.printf "FLATTEN: @[@[%a@] <:@ @[%a@." Print.typ ty1 Print.typ ty2;
  match ty1, ty2 with
  | TAttr(attr1, TBase _), TAttr(attr2, TBase _) ->
      flatten_sub_attr attr1 attr2 constr
  | TBase _, _ -> assert false
  | TVar _, _ -> unsupported __MODULE__
  | TAttr(attr1, TFun(x1,ty12)), TAttr(attr2, TFun(x2,ty22)) ->
      constr
      |> flatten_sub_attr attr2 attr1
      |> flatten_sub (Id.typ x2) (Id.typ x1)
      |> flatten_sub ty12 ty22
  | TFun _, _ -> assert false
  | TFuns _, _ -> unsupported __MODULE__
  | TAttr(attr1, TTuple xs1), TAttr(attr2, TTuple xs2) ->
      constr
      |> flatten_sub_attr attr1 attr2
      |> List.fold_right2 (fun x1 x2 -> flatten_sub (Id.typ x1) (Id.typ x2)) xs1 xs2
  | TTuple _, _ -> assert false
  | TData _, _ -> unsupported __MODULE__
  | TVariant _, _ -> unsupported __MODULE__
  | TRecord _, _ -> unsupported __MODULE__
  | TAttr(attr1,TApp(_,tys1)), TAttr(attr2,TApp(_,tys2)) ->
      constr
      |> flatten_sub_attr attr1 attr2
      |> List.fold_right2 flatten_sub tys1 tys2
  | TApp _, _ -> assert false
  | TAttr(_,ty1'), ty2'
  | ty1', TAttr(_, ty2') -> flatten_sub ty1' ty2' constr
  | TModule _, _ -> unsupported __MODULE__

let rec gen_constr env l t ty =
  let env,l_t = new_id env in
  let env,typ = make_template env t.typ in
  if false then
    begin
      Debug.printf "gen_constr:@.";
      Debug.printf "  l, l_t: %d, %d@." l l_t;
      Debug.printf "  t: @[%a@." Print.term t;
      Debug.printf "  ty @[%a@." Print.typ ty;
      Debug.printf "  typ @[%a@." Print.typ typ;
    end;
  let env =
    env
    |> add_constr l l_t
    |> flatten_sub typ ty
  in
  let env,desc =
    match t.desc with
    | Const (Rand(_, true)) -> unsupported __MODULE__
    | Const (Rand(_, false))
    | Const _
    | Bottom ->
        let env = add_constr l_t (get_id typ) env in
        env, t.desc
    | Var x ->
        let typ' =
          if Id.mem x env.fv then
            set_id 0 ty
          else
	    try
	      Id.assoc x env.tenv
	    with
	    | Not_found ->
                Format.eprintf "%a@." Print.id x;
                assert false
        in
        let env =
          env
          |> flatten_sub typ' typ
          |> add_constr l_t (get_id typ)
        in
        env, Var (Id.set_typ x typ)
    | Fun(x, t1) ->
        let tenv = env.tenv in
        let l_f,x_ty,r_ty =
          match decomp_tattr typ with
          | attr, TFun(x', ty) -> get_id_attr attr, Id.typ x', ty
          | _ -> assert false
        in
        let l' = get_id ty in
        let x' = Id.set_typ x x_ty in
        let env = {env with tenv = (x, x_ty) :: env.tenv} in
        let env,t1' = gen_constr env l' t1 r_ty in
        let env =
          env
          |> add_constr l_t l'
          |> add_constr l_t l_f
        in
        {env with tenv}, Fun(x',t1')
    | App(_, []) -> assert false
    | App(t1, t2::t3::ts) ->
        let t12 = {(make_app_raw t1 [t2]) with attr=[]} in
        let t' = {t with desc=App(t12, t3::ts)} in
        let env,t'' = gen_constr env l_t t' ty in
        env, t''.desc
    | App(t1, [t2]) ->
        let env, x' =
          match elim_tattr t1.typ with
          | TFun(x,_) ->
              let env,ty1 = make_template env (Id.typ x) in
              env, Id.set_typ x ty1
          | _ -> assert false
        in
        let env,t1' =
          let ty_1 = add_id l_t @@ TFun(x', typ) in
          gen_constr env l_t t1 ty_1
        in
        let env,t2' = gen_constr env l_t t2 (Id.typ x') in
        let env = add_constr l_t (get_id t1'.typ) env in
        env, App(t1', [t2'])
    | If(t1, t2, t3) ->
        let env,l' = new_id env in
        Debug.printf "IF l': %d@." l';
        let env,l'' = new_id env in
        let env = add_constr l' l'' env in
        let env,t1' = gen_constr env l_t t1 (add_id l' Ty.bool) in
        let env,t2' = gen_constr env l'' t2 typ in
        let env,t3' = gen_constr env l'' t3 typ in
        env, If(t1', t2', t3')
    | Local(Decl_let bindings, t1) ->
        let tenv = env.tenv in
        let env =
          let aux env (f,_) =
            let env,ty' = make_template env (Id.typ f) in
            {env with tenv = (f,ty')::env.tenv}
          in
          List.fold_left aux env bindings
        in
        let aux (f, t1) (env,bindings) =
          let f_typ = Id.assoc f env.tenv in
          let f' = Id.set_typ f f_typ in
          let env,t1' = gen_constr env l_t t1 f_typ in
          Debug.printf "f: %a@." Print.id f;
          let env = flatten_sub t1'.typ f_typ env in
          env, (f', t1')::bindings
        in
        let env,bindings' = List.fold_right aux bindings (env,[]) in
        let env,t1' = gen_constr env l_t t1 typ in
        let desc = Local(Decl_let bindings', t1') in
        {env with tenv}, desc
    | BinOp(op, t1, t2) ->
        let l' = get_id typ in
        Debug.printf "BINOP l': %d@." l';
        let env = add_constr l' l env in
        let env,t1' = gen_constr env l_t t1 (add_id l' t1.typ) in
        let env,t2' = gen_constr env l_t t2 (add_id l' t2.typ) in
        env, BinOp(op,t1',t2')
    | Not t1 ->
        let l' = get_id typ in
        let env = add_constr l_t l' env in
        let env,t1' = gen_constr env l_t t1 (add_id l' t1.typ) in
        env, Not t1'
    | Event(_,false) ->
        let env = add_constr l_t 0 env in
        env, t.desc
    | Event(_,true) -> unsupported __MODULE__
    | Proj(i,t1) ->
        let env,ty' = make_template env t1.typ in
        let env = flatten_sub (proj_typ i ty') typ env in
        let env,t1' = gen_constr env l_t t1 ty' in
        env, Proj(i,t1')
    | Tuple ts ->
        let env,ts' =
          let tys = decomp_ttuple typ in
          let l = get_id typ in
          let aux t_i ty_i (env,acc) =
            let env,t_i' = gen_constr env l_t t_i ty_i in
            let env = add_constr l (get_id ty_i) env in
            env, t_i'::acc
          in
          List.fold_right2 aux ts tys (env,[])
        in
        env, Tuple ts'
    | TryWith(t1, t2) ->
        let env,ty2 = make_template env t2.typ in
        let env = add_constr l_t (get_id ty2) env in
        let env =
          match elim_tattr ty2 with
          | TFun(x,_) ->
              let env,ty_exn = get_ty_exn env (elim_tattr_all @@ Id.typ x) in
              flatten_sub ty_exn (Id.typ x) env
          | _ -> assert false
        in
        let env,t1' = gen_constr env l_t t1 typ in
        let env,t2' = gen_constr env l_t t2 ty2 in
        env, TryWith(t1',t2')
    | Raise t1 ->
        let env,ty' = make_template env t1.typ in
        let env,t1' = gen_constr env l_t t1 ty' in
        let env = add_constr l_t 0 env in
        let env,ty_exn = get_ty_exn env t1.typ in
        let env = flatten_sub t1'.typ ty_exn env in
        env, Raise t1'
    | MemSet(t1, t2) -> (* TODO: Refine *)
        let env,ty1 = make_template env t1.typ in
        let env,ty2 = make_template env t2.typ in
        let env,t1' = gen_constr env l_t t1 ty1 in
        let env,t2' = gen_constr env l_t t2 ty2 in
        let env = force ty1 ~default:l_t env in
        let env = force ty2 ~default:l_t env in
        let env = add_constr l_t (get_id typ) env in
        env, MemSet(t1', t2')
    | AddSet(t1, t2) -> (* TODO: Refine *)
        let env,ty1 = make_template env t1.typ in
        let env,ty2 = make_template env t2.typ in
        let env,t1' = gen_constr env l_t t1 ty1 in
        let env,t2' = gen_constr env l_t t2 ty2 in
        let env = force ty1 ~default:l_t env in
        let env = force ty2 ~default:l_t env in
        let env = add_constr l_t (get_id typ) env in
        env, AddSet(t1', t2')
    | Subset(t1, t2) -> (* TODO: Refine *)
        let env,ty1 = make_template env t1.typ in
        let env,ty2 = make_template env t2.typ in
        let env,t1' = gen_constr env l_t t1 ty1 in
        let env,t2' = gen_constr env l_t t2 ty2 in
        let env = force ty1 ~default:l_t env in
        let env = force ty2 ~default:l_t env in
        let env = add_constr l_t (get_id typ) env in
        env, Subset(t1', t2')
    | _ ->
        Format.eprintf "%a@." Print.term t;
        assert false
  in
  env, {desc; typ; attr = AId l_t::t.attr}


(* sol.(x) holds if "id x" is "DONT CARE" *)
(* t is used just for debug *)
let solve env t =
  let n = env.counter + 1 in
  let lower = Array.make n [] in
  let sol = Array.make n true in
  sol.(0) <- false;
  List.iter (fun (x,y) -> lower.(y) <- x::lower.(y)) env.constr;
  let rec solve rest =
    match rest with
    | [] -> ()
    | x::rest' ->
        let low = List.filter ((<>) 0) lower.(x) in
        let low' = List.filter (fun y -> sol.(y)) low in
        Debug.printf "low: %a <: %d@." Print.(list int) low x;
        List.iter (fun y -> sol.(y) <- false) low;
        solve (low'@rest')
  in
  solve [0];
  let ids = col_id t in
  Debug.printf  "DONT CARE (\"*\" means it is a label for some term):@.";
  Array.iteri (fun i x -> if x then Debug.printf  "  %d%s@." i (if List.mem i ids then "*" else "")) sol;
  fun x ->
    if x < 0 || n < x then invalid_arg "solve";
    sol.(x)


let gen_constr_init t =
  assert (is_base_typ t.typ);
  let fv = get_fv t in
  let env = initial_env fv in
  let env,x = new_id env in
  let env,ty = make_template env t.typ in
  gen_constr env x t ty


let infer t =
  let env,t' = gen_constr_init t in
  Debug.printf "Add evar: %a@." Print.term' t';
  Debug.printf "CONSTRAINTS:@.";
  List.iter (fun (e1,e2) -> Debug.printf "  %d <: %d@." e1 e2) env.constr;
  Debug.printf "@.";
  let sol = solve env t' in
  sol, t'

let can_remove sol t =
  let ty = t.typ in
  let effect = effect_of_typ ty in
  is_base_typ ty &&
  sol (get_id ty) &&
  effect = []

let remove_dont_care =
  let tr = make_trans2 () in
  let tr_term sol t =
    if can_remove sol t then
      let () = Debug.printf "REMOVE %d@." (get_id t.typ) in
      let () = Debug.printf "%a@.@." Print.term' t in
      make_term t.typ
    else
      let attr = List.filter (function AId _ -> false | _ -> true) t.attr in
      {(tr.tr2_term_rec sol t) with attr}
  in
  tr.tr2_term <- tr_term;
  tr.tr2_typ <- Fun.snd;
  Fun.uncurry tr.tr2_term

let slice t =
  Debug.printf "SLICE: %d@." (size t);
  t
  |> Effect.infer
  |@> Debug.printf "EFFECT: %a@." Print.term
  |> infer
  |@> Debug.printf "INFERRED: %a@." Print.term -| snd
  |@> Debug.printf "INFERRED: %a@." Print.term' -| snd
  |> remove_dont_care
  |@> Debug.printf "SLICED: %a@." Print.term
  |> Trans.remove_tid label
  |> Trans.remove_effect_attribute
  |> Trans.elim_unused_let
  |> Trans.reconstruct
  |@> Debug.printf "SLICED: %d@." -| size

(*
let collect =
  let col = make_col2 [] (@@@) in
  let col_term (f,bv) t =
    if f t then
      [bv,t]
    else
      match t.desc with
      | Fun(x,t') -> col.col2_term (f,x::bv) t'
      | Local(decl, t') ->
          let bv' =
            match decl with
            | Decl_let bindings -> List.map fst bindings
            | _ -> bv
          in
          col.col2_decl (f,bv) decl @@@ col.col2_term (f,bv') t'
      | _ -> col.col2_term_rec (f,bv) t
  in
  col.col2_term <- col_term;
  col.col2_typ <- Fun.const2 [];
  fun f t -> col.col2_term (f,[]) t
 *)

let remove_unrelated =
  let tr = make_trans2 () in
  let tr_term (dist,longest) t =
    let d = dist t in
    let effects = effect_of_typ t.typ in
    if d < 0 && is_base_typ t.typ && List.Set.(effects <= [ENonDet;EDiv]) then
      let () = Debug.printf "REMOVE CONTEXT %d@." (get_id t.typ) in
      make_term t.typ
    else if d > longest && is_base_typ t.typ && List.Set.(effects <= [ENonDet;EDiv]) then
      let () = Debug.printf "REMOVE FAR %d@." (get_id t.typ) in
      let () = Debug.printf "%a@.@." Print.term' t in
      make_rand_unit @@ elim_tid label t.typ
    else
      let attr = List.filter (function AId _ -> false | _ -> true) t.attr in
      {(tr.tr2_term_rec (dist,longest) t) with attr}
  in
  tr.tr2_term <- tr_term;
  tr.tr2_typ <- Fun.snd;
  Fun.curry tr.tr2_term


let make_slice_sub t =
  let env,t' = gen_constr_init @@ Effect.infer t in
  let graph = Graph.from_directed_edges env.constr in
  if !!Debug.check then Graph.save_as_dot "test.dot" graph;
  let hops = Graph.hops_to graph [0] in
  Array.iteri (fun i x -> Debug.printf "hops(%d) = %d@." i x) hops;
  let dist t = hops.(get_id t.typ) in
  let longest = Graph.fold_node (fun i l -> max l hops.(i)) graph (-1) in
  fun p ->
    let far = int_of_float (p *. float_of_int longest) in
    Debug.printf "longest: %d@." longest;
    Debug.printf "far: %d@." far;
    Debug.printf "INFER_ORIG: @[%a@." Print.term' t';
    let t'' = Trans.remove_effect_attribute @@ remove_unrelated dist far t' in
    Debug.printf "ORIG: @[%a@." Print.term t;
    Debug.printf "INFER: @[%a@." Print.term' t';
    Debug.printf "REMOVE_UNRELATED: @[%a@." Print.term t'';
    let t'' =
      t''
      |> Trans.remove_tid label
      |> Trans.reconstruct
      |@> Type_check.check
      |> Trans.reduce_rand
    in
    Debug.printf "SIMPLIFIED: @[%a@." Print.term t'';
    t''

let slice_sub t p =
  make_slice_sub t p

let slice_subs t p =
  let make = make_slice_sub t in
  let n = int_of_float (ceil (1. /. p)) in
  let p_of i =
    let p' = min 1. (float_of_int i *. p) in
    make p'
    |&!!Debug.check&> add_comment (Format.sprintf "SLICE_SUB %.3f" p')
  in
  List.init n p_of


let normalize =
  let aux t =
    match decomp_assert t with
    | None -> t
    | Some(t', _) ->
        let u = Id.new_var Ty.unit in
        Term.(let_ [u, assert_ t'] unit)
  in
  Trans.map_main aux
  |- Trans.elim_unused_let
  |- Trans.top_def_to_funs

let get_top_fun_dependencies unsafe_ext_funs t =
  let decls,_ = decomp_decls t in
  let defs = List.flatten_map (function Decl_let defs -> defs | _ -> []) decls in
  let id_of,fun_of =
    let module IDMap = Map.Make(ID) in
    let module IDRevMap = Map.Make(struct type t = int let compare = compare end) in
    let fs = get_fv t @ List.map fst defs in
    let map = List.fold_lefti (fun acc cnt f -> IDMap.add f cnt acc) IDMap.empty fs in
    let rev_map = List.fold_lefti (fun acc cnt f -> IDRevMap.add cnt f acc) IDRevMap.empty fs in
    assert (List.is_unique fs);
    IDMap.find -$- map,
    IDRevMap.find -$- rev_map
  in
  let check t =
    let has_target_exn t =
      if !Flag.Method.target_exn = [] then
        false
      else
        let aux = function
          | None -> true
          | Some s -> List.mem s !Flag.Method.target_exn
        in
        List.exists aux (col_raise t)
    in
    has_event t || has_target_exn t
  in
  let goals = (* "goals" are functions that have fail or raise syntactically *)
    let unsafe_ext_funs' = List.filter (Exception.not_raise id_of) unsafe_ext_funs in
    defs
    |> List.filter_map (fun (f,t) -> if check t then Some f else None)
    |@> Debug.printf "GOALS: %a@." Print.(list id)
    |> (@) unsafe_ext_funs'
    |> List.map id_of
  in
  let deps =
    defs
    |> List.flatten_map (fun (f,t) -> List.map (Pair.pair -$- f) @@ get_fv t)
    |> List.map (Pair.map_same id_of)
  in
  id_of, fun_of, goals, deps

(** remove function `f` in `t` if `dist f < 0 || far < dist f` *)
let rec remove_unrelated_funs dist far may_call_goal t =
  let ruf = remove_unrelated_funs dist far in
  let removed,target,desc =
    match t.desc with
    | Local(Decl_type decl, t') ->
        let removed,target,t'' = ruf may_call_goal t' in
        removed, target, Local(Decl_type decl, t'')
    | Local(Decl_let defs, t1) ->
        let defs_unrelated,defs' =
          let check (f,_) =
            let d = dist f in
            d < 0 || far < d
          in
          List.partition check defs
        in
        let removed1 = List.map fst defs_unrelated in
        if defs' <> [] then Debug.printf "Dom(defs'): @[%a@." Print.(list id) (List.map fst defs');
        let may_call_goal1 =
          let check (_,t) = List.exists (Id.mem -$- may_call_goal) (get_fv t) in
          if List.exists check defs then
            List.map fst defs
          else
            []
        in
        if may_call_goal1 <> [] then Debug.printf "may_call_goal1: %a@." Print.(list id) may_call_goal1;
        let removed2,target2,t1' = ruf (may_call_goal1@may_call_goal) t1 in
        let desc =
          if defs' = [] then
            t1'.desc
          else
            Local(Decl_let defs', t1')
        in
        let target1 =
          let fv = get_fv ~eq:(Fun.const2 false) @@ Term.tuple (t1 :: List.map snd defs_unrelated) in
          let fv' = get_fv ~eq:(Fun.const2 false) t1' in
          let check f = List.count (Id.(=) f) fv <> List.count (Id.(=) f) fv' in
          let (&&) = List.Set.inter ~eq:Id.eq in
          (List.map fst defs' && may_call_goal1)
          |> List.filter check
        in
        if target1 <> [] then
          (Debug.printf "Dom(defs): @[%a@." Print.(list id) (List.map fst defs);
           Debug.printf "target1: @[%a@." Print.(list id) target1);
        removed1@removed2, target1@target2, desc
    | _ -> [], [], t.desc
  in
  removed, target, {t with desc}

let add_raise_attr =
  let tr = make_trans2 () in
  let tr_typ exn ty =
    match tr.tr2_typ_rec exn ty with
    | TFun(x, ty2) -> TAttr([TARaise exn], TFun(x, ty2))
    | ty -> ty
  in
  tr.tr2_typ <- tr_typ;
  tr.tr2_typ


let rec may_raise_funs acc t =
  match t.desc with
  | Local(decl, t') ->
      let acc' =
        let check (_,t) =
          has_raise ~target:!Flag.Method.target_exn t || List.exists (Id.mem -$- get_fv t) acc
        in
        match decl with
        | Decl_let defs when List.exists check defs -> List.map fst defs @ acc
        | _ -> acc
      in
      may_raise_funs acc' t'
  | _ -> acc
let may_raise_funs t = may_raise_funs [] t

let calc_dist unsafe_ext_funs t =
  let id_of,fun_of,goals,deps = get_top_fun_dependencies unsafe_ext_funs t in
  let graph = Graph.from_edges deps in
  let hops = Graph.hops_to graph goals in
  Array.iteri (fun i x -> Debug.printf "hops(%d) = %d@." i x) hops;
  let dist f =
    let x = id_of f in
    let n = hops.(x) in
    if true then Debug.printf "hops(%a : #%d) = %d@." Print.id f x n;
    n
  in
  let longest = Graph.fold_node (fun i l -> max l hops.(i)) graph (-1) in
  List.map fun_of goals, dist, longest

let slice_top_fun unsafe_ext_funs t =
  let t = normalize t in
  Debug.printf "normalized: %a@." Print.term t;
  let goals,dist,longest = calc_dist unsafe_ext_funs t in
  let typ_exn = find_exn_typ t in
  let may_raise = may_raise_funs t in
  Debug.printf "MAY_RAISE: %a@." Print.(list id) may_raise;
  fun p ->
    Debug.printf "p: %f@." p;
    let far = int_of_float (ceil (p *. float_of_int longest)) in
    Debug.printf "longest: %d@." longest;
    Debug.printf "far: %d@." far;
    let removed,target,t' = remove_unrelated_funs dist far goals t in
    Debug.printf "TARGET: %a@." Print.(list id) target;
    let t'' =
      t'
      |> Trans.remove_effect_attribute
      |> Trans.replace_main ~main:Term.(tuple (vars target))
      |&!!Debug.check&> add_comment (Format.sprintf "SLICE_TOP_FUN %.3f" p)
    in
    Debug.printf "REMOVE_UNRELATED: @[%a@." Print.term t'';
    Debug.printf "REMOVED[%.3f]: %a@." p Print.(list id) removed;
    let decls,body = split_type_decl_and_body t'' in
    let body' =
      let used_but_removed = List.filter (Id.mem -$- get_fv t'') removed in
      let aux t x =
        let ty = Id.typ x in
        let ty =
          match typ_exn with
          | Some typ_exn when Id.mem x may_raise -> add_raise_attr typ_exn ty (* Should deal with target_exn *)
          | _ -> ty
        in
        Term.(let_ [x, rand ty] t)
      in
      List.fold_left aux body used_but_removed
    in
    let t'' = List.fold_right (fun decl t -> Term.local (Decl_type decl) t) decls body' in
    {t'' with attr=t''.attr}
