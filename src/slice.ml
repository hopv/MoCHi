open Type
open Type_util
open Syntax
open Term_util
open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type env =
  {constr: (int * int) list;
   counter: int;
   tenv: (id * typ) list;
   fv: id list;
   ty_exn: typ option;
   respect_div: bool}

(* id 0 represents "CARE"*)
let care = 0
let initial_env respect_div fv =
  let counter = 1 in
  let constr = [] in
  let tenv = [] in
  let ty_exn = None in
  {counter; constr; tenv; fv; ty_exn; respect_div}

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

let force ty ?(default=care) env =
  ty
  |> col_tid
  |> List.filter_map (fun (s,l) -> if s=label then Some l else None)
  |> List.fold_left (fun env l -> add_constr l default env) env

let rec make_template env ty =
  match ty with
  | TBase _ -> add_new_id env ty
  | TVar _ -> unsupported "%s" __FUNCTION__
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
  | TFuns _ -> unsupported "%s" __FUNCTION__
  | TVariant _ -> unsupported "%s" __FUNCTION__
  | TRecord _ -> unsupported "%s" __FUNCTION__
  | TConstr(s,tys) ->
      let env,l = new_id env in
      let env,tys' =
        let aux (env,tys) ty =
          let env,ty' = make_template env ty in
          let env = add_constr l (get_id ty') env in
          env, tys@[ty']
        in
        List.fold_left aux (env,[]) tys
      in
      env, _TAttr [_TAId l] @@ TConstr(s,tys')
  | TModSig _ -> unsupported "%s" __FUNCTION__
  | TModLid _ -> unsupported "%s" __FUNCTION__
  | TPackage _ -> unsupported "%s" __FUNCTION__
  | TPoly _ -> unsupported "%s" __FUNCTION__
  | TConstraint _ -> unsupported "%s" __FUNCTION__
  | TOpen -> unsupported "%s" __FUNCTION__

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
  | TVar _, _ -> unsupported "%s" __FUNCTION__
  | TAttr(attr1, TFun(x1,ty12)), TAttr(attr2, TFun(x2,ty22)) ->
      constr
      |> flatten_sub_attr attr2 attr1
      |> flatten_sub (Id.typ x2) (Id.typ x1)
      |> flatten_sub ty12 ty22
  | TFun _, _ -> assert false
  | TFuns _, _ -> unsupported "%s" __FUNCTION__
  | TAttr(attr1, TTuple xs1), TAttr(attr2, TTuple xs2) ->
      constr
      |> flatten_sub_attr attr1 attr2
      |> List.fold_right2 (fun x1 x2 -> flatten_sub (Id.typ x1) (Id.typ x2)) xs1 xs2
  | TTuple _, _ -> assert false
  | TVariant _, _ -> unsupported "%s" __FUNCTION__
  | TRecord _, _ -> unsupported "%s" __FUNCTION__
  | TAttr(attr1,TConstr(_,tys1)), TAttr(attr2,TConstr(_,tys2)) ->
      constr
      |> flatten_sub_attr attr1 attr2
      |> List.fold_right2 flatten_sub tys1 tys2
  | TConstr _, _ -> assert false
  | TAttr(_,ty1'), ty2'
  | ty1', TAttr(_, ty2') -> flatten_sub ty1' ty2' constr
  | TModSig _, _ -> unsupported "%s" __FUNCTION__
  | TModLid _, _ -> unsupported "%s" __FUNCTION__
  | TPackage _, _ -> unsupported "%s" __FUNCTION__
  | TPoly _, _ -> unsupported "%s" __FUNCTION__
  | TConstraint _, _ -> unsupported "%s" __FUNCTION__
  | TOpen, _ -> unsupported "%s" __FUNCTION__

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
    | Const (Rand(_, true)) -> unsupported "%s" __FUNCTION__
    | Const (Rand(_, false))
    | Const _
    | Bottom ->
        let env = add_constr l_t (get_id typ) env in
        env, t.desc
    | Var (LId x) ->
        let typ' =
          if Id.List.mem x env.fv then
            set_id 0 ty
          else
	    try
	      Id.List.assoc x env.tenv
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
        env, Var (LId (Id.set_typ x typ))
    | Var _ -> unsupported "Slice"
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
        let t12 = make_app_raw t1 [t2] in
        let t' = make (App(t12, t3::ts)) t.typ in
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
        let env =
          let effect = effect_of_typ ty in
          if env.respect_div && List.mem EDiv effect then
            add_constr l' care env
          else
            env
        in
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
          let f_typ = Id.List.assoc f env.tenv in
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
    | Event(_,true) -> unsupported "%s" __FUNCTION__
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
  env, make desc typ ~attr:(AId l_t::t.attr)


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
  Debug.printf {|DONT CARE ("*" means it is a label for some term):@.|};
  Array.iteri (fun i x -> if x then Debug.printf  "  %d%s@." i (if List.mem i ids then "*" else "")) sol;
  fun x ->
    if x < 0 || n < x then invalid_arg "solve";
    sol.(x)


let gen_constr_init respect_div t =
  assert (is_base_typ t.typ);
  let fv = get_fv t in
  let env = initial_env respect_div fv in
  let env,x = new_id env in
  let env,ty = make_template env t.typ in
  gen_constr env x t ty


let infer respect_div t =
  let env,t' = gen_constr_init respect_div t in
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
  let tr = Tr2.make () in
  let tr_term sol t =
    if can_remove sol t then
      let () = Debug.printf "REMOVE %d@." (get_id t.typ) in
      let () = Debug.printf "%a@.@." Print.term' t in
      make_default_term t.typ
    else
      tr.term_rec sol t
      |> remove_attr_if (function AId _ -> true | _ -> false)
  in
  tr.term <- tr_term;
  tr.typ <- Fun.snd;
  Fun.uncurry tr.term

let pr s t =
  Debug.printf "%s: %a@." s Print.term' t

let slice ?(respect_div=true) t =
  Debug.printf "SLICE: %d@." (size t);
  t
  |> Effect.infer
  |@> pr "EFFECT"
  |> infer respect_div
  |@> pr "INFERRED" -| snd
  |> remove_dont_care
  |@> pr "SLICED"
  |> Trans.remove_tid label
  |> Trans.remove_effect_attribute
  |> Trans.elim_unused_let
  |> Trans.reconstruct
  |@> Debug.printf "SLICED: %d@." -| size

let slice_problem p =
  LazyList.of_lazy_list
    [(*lazy (Problem.map (slice ~respect_div:false) p);*) (* BUGGY *)
     lazy (Problem.map (slice ~respect_div:true) p)]
