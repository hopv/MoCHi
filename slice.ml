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

let rec force ty env =
  ty
  |> col_tid
  |> List.filter_map (fun (s,l) -> if s=label then Some l else None)
  |> List.fold_left (fun env l -> add_constr l 0 env) env

let rec make_template env ty =
  match ty with
  | TBase _ -> add_new_id env ty
  | TVarLazy _ -> assert false
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
  | TApp _ -> unsupported __MODULE__
  | TModule _ -> unsupported __MODULE__

let get_ty_exn env ty =
  match env.ty_exn with
  | None ->
      let env,ty_exn = make_template env ty in
      Debug.printf "ty_exn: %a@." Print.typ ty_exn;
      {env with ty_exn=Some ty_exn}, ty_exn
  | Some ty_exn ->
      env, ty_exn

let rec flatten_sub_attr attr1 attr2 env =
  let x = get_id_attr attr1 in
  let y = get_id_attr attr2 in
  add_constr x y env

let rec flatten_sub ty1 ty2 constr =
  Debug.printf "FLATTEN: @[@[%a@] <:@ @[%a@." Print.typ ty1 Print.typ ty2;
  match ty1, ty2 with
  | TAttr(attr1, TBase _), TAttr(attr2, TBase _) ->
      flatten_sub_attr attr1 attr2 constr
  | TBase _, _ -> assert false
  | TVarLazy _, _ -> assert false
  | TVar _, _ -> unsupported __MODULE__
  | TAttr(attr1, TFun(x1,ty12)), TAttr(attr2, TFun(x2,ty22)) ->
      constr
      |> flatten_sub_attr attr2 attr1
      |> flatten_sub (Id.typ x2) (Id.typ x1)
      |> flatten_sub ty12 ty22
  | TFun _, _ ->
      assert false
  | TFuns _, _ -> unsupported __MODULE__
  | TAttr(attr1, TTuple xs1), TAttr(attr2, TTuple xs2) ->
      constr
      |> flatten_sub_attr attr1 attr2
      |> List.fold_right2 (fun x1 x2 -> flatten_sub (Id.typ x1) (Id.typ x2)) xs1 xs2
  | TTuple _, _ -> assert false
  | TData _, _ -> unsupported __MODULE__
  | TVariant _, _ -> unsupported __MODULE__
  | TRecord _, _ -> unsupported __MODULE__
  | TApp _, _ -> unsupported __MODULE__
  | TAttr(attr,ty1'), ty2'
  | ty1', TAttr(attr, ty2') -> flatten_sub ty1' ty2' constr
  | TModule _, _ -> unsupported __MODULE__

let rec gen_constr env l t ty =
  let env,l_t = new_id env in
  let env,typ = make_template env t.typ in
  let env =
    env
    |> add_constr l l_t
    |> flatten_sub typ ty
  in
  if false then
    begin
      Debug.printf "gen_constr:@.";
      Debug.printf "  l, l_t: %d, %d@." l l_t;
      Debug.printf "  t: @[%a@." Print.term t;
      Debug.printf "  ty @[%a@." Print.typ ty;
    end;
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
    | App(t1, []) -> assert false
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
    | Event(s,false) ->
        let env = add_constr l_t 0 env in
        env, t.desc
    | Event(s,true) -> unsupported __MODULE__
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
  Debug.printf  "DONT CARE:@.";
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

let rec can_remove sol t =
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
    if d < 0 && is_base_typ t.typ && List.Set.subset effects [ENonDet;EDiv] then
      let () = Debug.printf "REMOVE CONTEXT %d@." (get_id t.typ) in
      make_term t.typ
    else if d > longest && is_base_typ t.typ && List.Set.subset effects [ENonDet;EDiv] then
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


let get_top_fun_dependencies t =
  let decls,t' = decomp_decls t in
  if t'.desc <> Const Unit && t'.desc <> End_of_definitions then
    unsupported "Slice.slice_top_fun";
  let defs = List.flatten_map (function Decl_let defs -> defs | Decl_type _ -> []) decls in
  let module IDMap = Map.Make(ID) in
  let fs = get_fv t @ List.map fst defs in
  let map,_ = List.fold_left (fun (acc,cnt) f -> IDMap.add f cnt acc, cnt + 1) (IDMap.empty,0) fs in
  let id_of f = IDMap.find f map in
  let goals =
    defs
    |> List.filter_map (fun (f,t) -> if has_event t then Some f else None)
    |@> Debug.printf "GOALS: %a@." Print.(list id)
    |> List.map id_of
  in
  let deps =
    defs
    |> List.flatten_map (fun (f,t) -> List.map (Pair.pair -$- f) @@ get_fv t)
    |> List.map (Pair.map_same id_of)
  in
  id_of, goals, deps

let rec remove_unrelated_funs dist far t =
  let ruf = remove_unrelated_funs dist far in
  let removed,target,desc =
    match t.desc with
    | Local(Decl_type decl, t') ->
        let removed,target,t'' = ruf t' in
        removed, target, Local(Decl_type decl, t'')
    | Local(Decl_let defs, t') ->
        let defs1,defs2 =
          let check (f,_) =
            let d = dist f in
            d < 0 || d > far
          in
          List.partition check defs
        in
        let removed1 = List.map fst defs1 in
        if defs2 <> [] then Debug.printf "Dom(defs2): @[%a@." Print.(list id) (List.map fst defs2);
        let removed2,target2,t'' = ruf t' in
        let desc =
          if defs2 = [] then
            t''.desc
          else
            Local(Decl_let defs, t'')
        in
        let fv = get_fv t'' in
        let target1 = List.map fst @@ List.filter_out (fun (f,_) -> Id.mem f fv) defs2 in
        removed1@removed2, target1@target2, desc
    | Const Unit
    | End_of_definitions -> [], [], End_of_definitions
    | _ -> assert false
  in
  removed, target, {t with desc}

let slice_top_fun t =
  let id_of,goals,deps = get_top_fun_dependencies t in
  if List.length goals >= 2 then unsupported "Slice.slice_top_fun";
  let graph = Graph.from_edges deps in
  let hops = Graph.hops_to graph goals in
  Array.iteri (fun i x -> Debug.printf "hops(%d) = %d@." i x) hops;
  let dist f =
    let x = id_of f in
    let n = hops.(x) in
    if false then Debug.printf "hops(%a : #%d) = %d@." Print.id f x n;
    n
  in
  let longest = Graph.fold_node (fun i l -> max l hops.(i)) graph (-1) in
  fun p ->
    Debug.printf "p: %f@." p;
    let far = int_of_float (ceil (p *. float_of_int longest)) in
    Debug.printf "longest: %d@." longest;
    Debug.printf "far: %d@." far;
    let removed,target,t' =
      t
      |*> Trans.elim_unused_let
      |> remove_unrelated_funs dist far
    in
    Debug.printf "TARGET: %a@." Print.(list id) target;
    if List.length target >= 2 then unsupported "Slice.slice_top_fun";
    let t'' =
      t'
      |> Trans.remove_effect_attribute
      |> Trans.set_main
      |&!!Debug.check&> add_comment (Format.sprintf "SLICE_TOP_FUN %.3f" p)
    in
    Debug.printf "REMOVE_UNRELATED: @[%a@." Print.term t'';
    removed, t''

let slice_top_fun_subs dp problem =
  let make = slice_top_fun problem.Problem.term in
  let rec go p =
    let _,term = make p in
    let problem' = {problem with Problem.term} in
    problem' :: if p > 1.0 then [] else go (p +. dp)
  in
  go 0.
