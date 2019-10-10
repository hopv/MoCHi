open Util
open CEGAR_syntax
open CEGAR_type
open CEGAR_util
open CEGAR_abst_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let abst_arg x ty =
  if false then Debug.printf "abst_arg: %a, %a;;@." CEGAR_print.var x CEGAR_print.typ ty;
  match decomp_base ty with
  | None -> [x]
  | Some(_,ps) ->
      match ps (Var x) with
      | [] -> []
      | [_] -> [x]
      | ps -> List.mapi (fun i _ -> add_name x @@ Format.sprintf "_%d" @@ i+1) ps

let make_pts x ty =
  let xs = abst_arg x ty in
  let ps =
    match decomp_base ty with
    | None -> [Const True] (* to match the length of ps and xs *)
    | Some(_, ps) -> ps (Var x)
  in
  List.filter (fun (p,_) -> p <> Const True) @@ List.map2 (fun p x -> p, Var x) ps xs

let rec decomp_typ_var typ xs =
  match xs with
  | [] -> typ, []
  | x::xs' ->
      let typ1,typ2 = match typ with TFun(typ1,typ2) -> typ1,typ2 (Var x) | _ -> assert false in
      let typ',env' = decomp_typ_var typ2 xs' in
      typ', (x,typ1)::env'

let rec decomp_typ_term ts typ =
  match ts,typ with
  | [], _ when is_typ_result typ -> []
  | t2::ts', TFun(typ1,typ2) ->
      typ1 :: decomp_typ_term ts' (typ2 t2)
  | _,typ ->
      assert false

let rec beta_reduce_term = function
  | Const c -> Const c
  | Var x -> Var x
  | App(App(App(Const If, Const True), t2), _) -> beta_reduce_term t2
  | App(App(App(Const If, Const False), _), t3) -> beta_reduce_term t3
  | App(t1, t2) ->
      let t1' = beta_reduce_term t1 in
      begin
        match t1' with
        | Fun(x,_,t1') -> beta_reduce_term @@ subst x t2 t1'
        | _ -> App(t1', beta_reduce_term t2)
      end
  | Fun(x, typ, t) -> Fun(x, typ, beta_reduce_term t)
  | Let _ -> assert false
let beta_reduce_def (f,xs,t1,e,t2) =
  f, xs, beta_reduce_term t1, e, beta_reduce_term t2

let rec expand_non_rec {env;defs;main;info} =
  let non_rec = info.non_rec in
  let aux (f,xs,t1,e,t2) =
    let non_rec' = List.filter_out (fst |- List.mem -$- xs) non_rec in
    f, xs, subst_map non_rec' t1, e, subst_map non_rec' t2 in
  let defs' =
    defs
    |> List.filter_out (fun (f,_,_,_,_) -> List.mem_assoc f non_rec)
    |> List.map aux
    |> List.map beta_reduce_def
  in
  {env; defs=defs'; main; info}





let rec trans_eager_bool f = function
  | Const True
  | Const False
  | Var _ as t -> App(Var f, t)
  | Const (Rand(TBool,_))
  | App(App(App(Const If, Const (Rand(TBool,_))), Const True), Const False) ->
      Term.(br (var f @ [true_]) (var f @ [false_]))
  | App(App(Const Or, t1), t2) ->
      let x = new_id "b" in
      let f' = new_id "f" in
      let t1' = trans_eager_bool f' t1 in
      let t2' = trans_eager_bool f t2 in
      Term.(let_ f' (fun_ x (if_ (var x) (var f @ [true_]) t2')) t1')
  | App(App(Const And, t1), t2) ->
      let x = new_id "b" in
      let f' = new_id "f" in
      let t1' = trans_eager_bool f' t1 in
      let t2' = trans_eager_bool f t2 in
      Term.(let_ f' (fun_ x (if_ (var x) t2' (var f @ [false_]))) t1')
  | App(Const Not, t) ->
      let x = new_id "b" in
      let f' = new_id "f" in
      let t' = trans_eager_bool f' t in
      Term.(let_ f' (fun_ x (if_ (var x) (var f @ [false_]) (var f @ [true_]))) t')
  | App(App(App(Const If, t1), t2), t3) ->
      let x = new_id "b" in
      let f' = new_id "f" in
      let t1' = trans_eager_bool f' t1 in
      let t2' = trans_eager_bool f t2 in
      let t3' = trans_eager_bool f t3 in
      Term.(let_ f' (fun_ x (if_ (var x) t2' t3')) t1')
  | t -> Format.eprintf "trans_eager_bool: %a@." CEGAR_print.term t; assert false

let is_bool env t =
  try
    match get_typ env t with
    | TBase(TBool,_) -> true
    | _ -> false
  with TypeBottom -> false

let rec trans_eager_term env c t =
  match t with
  | App(App(Const And, _), _)
  | App(App(Const Or, _), _)
  | App(Const Not, _)
  | App(App(App(Const If, _), _), _) when is_bool env t ->
      let x = new_id "b" in
      begin
        match c (Var x) with
        | App(Var k, Var y) when x = y ->
            trans_eager_bool k t
        | t' ->
            let f = new_id "f" in
            Term.(let_ f (fun_ x t') (trans_eager_bool f t))
      end
  | Const (Rand(TBool,_)|And|Or|Not|Lt|Gt|Leq|Geq|EqUnit|EqInt|EqBool) -> assert false
  | Const _
  | Var _ -> c t
  | Fun(x,ty,t) ->
      let env' =
        match ty with
        | None -> env
        | Some ty' -> (x,ty')::env
      in
      c (_Fun x @@ trans_eager_term env' Fun.id t)
  | App(App(App(Const If, t1), t2), t3) ->
      let x = new_id "b" in
      let f = new_id "f" in
      let t2' = trans_eager_term env Fun.id t2 in
      let t3' = trans_eager_term env Fun.id t3 in
      let t' = make_if (Var x) t2' t3' in
      let t1' = trans_eager_bool f t1 in
      Term.(let_ f (fun_ x t') (c t1'))
  | App(t1, t2) ->
      let t1' = trans_eager_term env Fun.id t1 in
      let c' x = c (App(t1', x)) in
      trans_eager_term env c' t2
  | Let(x, t1, t2) ->
      let f = new_id "f" in
      let t2' = trans_eager_term env Fun.id t2 in
      let t1' = trans_eager_term env (_App (Var f)) t1 in
      c Term.(let_ f (fun_ x t2') t1')

let trans_eager_def env (f,xs,t1,e,t2) =
  let env' = get_arg_env (List.assoc f env) xs @@@ env in
  assert (t1 = Const True);
  f, xs, t1, e, trans_eager_term env' Fun.id t2

let trans_eager prog = map_def_prog (trans_eager_def prog.env) prog


let rec eta_expand_term_aux env t typ =
  if true then Debug.printf "  ETA_AUX: %a: %a@." CEGAR_print.term t CEGAR_print.typ typ;
  match typ with
  | TBase _ -> t
  | TFun(typ1,typ2) ->
      let x = new_id "x_" in
      let typ2 = typ2 (Var x) in
      let env' = (x,typ1)::env in
      let typ1' =
        match get_typ env' t with
        | TFun(typ,_) -> typ
        | typ -> Format.eprintf "%a: %a@." CEGAR_print.term t CEGAR_print.typ typ; assert false
      in
      let t' = App(t, eta_expand_term_aux env' (Var x) typ1') in
      Fun(x, Some typ1, eta_expand_term_aux env' t' typ2)
  | _ -> assert false

let rec eta_expand_term env t typ =
  if true then Debug.printf "ETA: %a: %a@." CEGAR_print.term t CEGAR_print.typ typ;
  match t with
  | Const Bottom
  | Const (Rand(TInt,_))
  | Const CPS_result -> t
  | (Var _ | Const _ | App _) when is_base_term env t -> t
  | Var x -> eta_expand_term_aux env t typ
  | App(App(App(Const If, t1), t2), t3) ->
      make_if t1 (eta_expand_term env t2 typ) (eta_expand_term env t3 typ)
  | App(Const (Label n), t) -> make_label n @@ eta_expand_term env t typ
  | App _ ->
      let t1,ts = decomp_app t in
      let rec aux ts typ =
        match ts,typ with
        | [], _ -> []
        | t::ts', TFun(typ1,typ2) ->
            let typ2 = typ2 t in
            let ts'' = aux ts' typ2 in
            eta_expand_term env t typ1 :: ts''
        | t::_, _ ->
            Format.eprintf "ERROR: %a, %a@." CEGAR_print.term t1 CEGAR_print.term t;
            assert false
      in
      let t' = make_app t1 (aux ts @@ get_typ env t1) in
      eta_expand_term_aux env t' typ
  | Const _ -> assert false
  | Let _ -> assert false
  | Fun(x,_,t') ->
      match typ with
      | TFun(typ1,typ2) ->
          let env' = (x,typ1)::env in
          let t'' = eta_expand_term env' t' (typ2 (Var x)) in
          Fun(x, Some typ1, t'')
      | _ ->
          Format.eprintf "%a, %a@." CEGAR_print.term t CEGAR_print.typ typ;
          assert false
let eta_expand_def env (f,xs,t1,e,t2) =
  let typ,env' = decomp_typ_var (List.assoc f env) xs in
  let t2' = eta_expand_term (env' @ env) t2 typ in
  f, xs, t1, e, t2'
let eta_expand prog =
  {prog with defs = List.map (eta_expand_def prog.env) prog.defs}

let fixpred_to_abstpred prog =
  let env =
    let rec aux ty =
      match ty with
      | TBase _ -> ty
      | TFun(ty1,ty2) -> TFun(aux ty1, aux -| ty2)
      | TApp(TConstr(TFixPred p), TBase(b,_)) -> TBase(b, fun x -> [p x])
      | _ -> Format.eprintf "%a@." CEGAR_print.typ ty; assert false
    in
    List.map (Pair.map_snd aux) prog.env
  in
  {prog with env}


let rec eta_reduce_term = function
  | Const _
  | Var _ as t -> t
  | App(t1,t2) -> App(eta_reduce_term t1, eta_reduce_term t2)
  | Let(x, t1, t2) -> Let(x, eta_reduce_term t1, eta_reduce_term t2)
  | Fun(x, typ, t) ->
      let t' = eta_reduce_term t in
      match t' with
      | App(App(App(Const If,_),_),_) -> Fun(x, typ, t')
      | App(Const (Label _), _) -> Fun(x, typ, t')
      | App(t, Var y) when x = y && not (List.mem y (get_fv t)) -> t
      | _ -> Fun(x, typ, t')

let print_env fm env =
  List.iter (fun (f,typ) -> Format.fprintf fm "%a:%a,@ " CEGAR_print.var f CEGAR_print.typ typ) env;
  Format.fprintf fm "@."

let rec propagate_fun_arg_typ typ t =
  match typ, t with
  | TFun(typ1, typ2), Fun(x,_,t') -> Fun(x, Some typ1, propagate_fun_arg_typ (typ2 @@ Var x) t')
  | _ -> t

let filter_wrap env cond pts t =
  if !Flag.PredAbst.use_filter then
    filter env cond pts t
  else
    t

let get (pts,defs,ts) =
  assert (defs = []);
  match ts with
  | [x] -> x
  | _ -> assert false

let expand (pts, defs, ts) =
  match ts with
  | [t] -> List.fold_right (Fun.uncurry subst) defs t
  | _ -> assert false

let make_let' (pts,defs,ts) =
  let t = List.get ts in
  match defs with
  | [] -> t
  | [x,t1] -> subst x t1 t
  | _ ->
      let aux (x,t1) t =
        match t1 with
        | Const _ -> subst x t1 t
        | _ -> Let(x,t1,t)
      in
      List.fold_right aux defs t

let rec abstract_rand_int n env cond pts xs t =
  let _,preds = decomp_rand_typ ~xs:(Some xs) @@ assoc_renv n env in
  let typ' = TFun(TBase(TInt, preds), fun _ -> typ_result) in
  let t' = get @@ abstract_term env cond pts t typ' in
  let x = new_id "r" in
  let preds' = preds (Var x) in
  Debug.printf "preds': %a@." (List.print CEGAR_print.term) preds';
  let rec make_combs n =
    if n <= 0
    then [[]]
    else List.flatten_map (fun acc -> [true::acc; false::acc]) @@ make_combs (n-1)
  in
  let f = new_id "f" in
  let cond_combs = make_combs @@ List.length pts in
  let pred_combs = make_combs @@ List.length preds' in
  let cts =
    let aux cond_comb =
      let cond' = List.map2 (fun b (p,_) -> if b then p else make_not p) cond_comb pts @ cond in
      if check_aux env cond' (Const False)
      then None
      else
        let argss =
          let aux' pred_comb =
            let bs,ps = List.split @@ List.map2 (fun b p -> b, if b then p else make_not p) pred_comb preds' in
            if check_exist env cond' x @@ List.fold_right make_and ps (Const True)
            then Some (bs, List.map (fun b -> if b then Const True else Const False) bs)
            else None
          in
          List.filter_map aux' pred_combs
        in
        let cs = List.map2 (fun b (_,t) -> if b then t else make_not t) cond_comb pts in
        Some (List.fold_right make_and cs (Const True), make_br_exists n @@ List.map (Pair.map_snd @@ make_app (Var f)) argss)
    in
    List.filter_map aux cond_combs
  in
  Let(f, t', List.fold_right (fun (b,t) t' -> make_if b t t') cts (Const Bottom))

(** env: type environment *)
(** cond: assumption (environment) *)
(** pts: enviroment for predicates
    (e.g., [x >= 0, b] means that the abstracted variable b corresponds "x >= 0" in the original program) *)
and abstract_term env cond pts t typ =
  match t with
  | Const CPS_result -> pts, [], [Const Unit]
  | Const Bottom ->
      assert (is_typ_result typ);
      pts, [], [Const Bottom]
  | (Var _ | Const _ | App _) when is_base_term env t ->
      let btyp,ps = Option.get @@ decomp_base typ in
      if btyp = typ_result_base then
        pts, [], [Const Unit]
      else
        if !Flag.PredAbst.cartesian then
          pts, [], List.map (abst env cond pts) (ps t)
        else
          let pts',defs,xs =
            let rec aux p (pts,defs,xs) =
              let x = new_id "b" in
              (p, Var x)::pts, (x,abst env cond pts p)::defs, x::xs
            in
            List.fold_right aux (ps t) (pts,[],[])
          in
          pts', List.rev defs, List.map _Var xs
  | Var x when congruent env cond (List.assoc x env) typ ->
      pts, [], [Var x]
  | App(App(App(Const If, t1), t2), t3) ->
      let t1' = expand @@ abstract_term env cond pts t1 typ_bool_id in
      let t2' = get @@ abstract_term env (t1::cond) pts t2 typ in
      let t3' = get @@ abstract_term env (make_not t1::cond) pts t3 typ in
      pts, [], [make_if t1' t2' t3']
  | App(Const (Label n), t) ->
      pts, [], [make_label n @@ make_let' @@ abstract_term env cond pts t typ]
  | App(Const (Rand(TInt,None)), t) ->
      abstract_term env cond pts t (TFun(typ_int, fun _ -> typ))
  | App _ when is_app_randint t ->
      let t',ts = decomp_app t in
      let n =
        match t' with
        | Const (Rand(TInt,Some n)) -> n
        | _ -> assert false
      in
      let ts',t'' = List.decomp_snoc ts in
      pts, [], [abstract_rand_int n env cond pts ts' t'']
  | App _ ->
      let t1,ts = decomp_app t in
      let typs = decomp_typ_term ts @@ get_typ env t1 in
      let pts',defs,args =
        let aux t typ (pts,defs,args) =
          let pts',defs',ts = abstract_term env cond pts t typ in
          pts', defs @ defs', ts @ args
        in
        List.fold_right2 aux ts typs (pts,[],[])
      in
      (** there is room for improving the precision by using defs *)
      pts', defs, [filter_wrap env cond pts' @@ make_app t1 args]
  | Fun _ ->
      let env',t0 = decomp_annot_fun t in
      let env' = List.map (Pair.map_snd Option.get) env' in
      let pts'' =
        let pts' = List.flatten_map (Fun.uncurry make_pts) env' in
        pts' @@@ pts
      in
      let xs' = List.flatten_map (Fun.uncurry abst_arg) env' in
      let env'' = env' @@@ env in
      let typ' = CEGAR_type.app typ (List.map (_Var -| fst) env') in
      let t' =
        t0
        |> abstract_term env'' cond pts'' -$- typ'
        |> make_let'
        |> filter_wrap env'' cond pts''
        |> make_fun_temp xs'
      in
      pts, [], [t']
  | Var _ -> assert false
  | Const _ -> assert false
  | Let _ -> assert false



let rec abstract_typ = function
  | TBase(base,ps) when base = typ_result_base -> [typ_unit]
  | TBase(_,ps) -> List.map (fun _ -> typ_bool_empty) (ps (Const Unit))
  | TFun(typ1,typ2) ->
      let typ2 = typ2 (Const Unit) in
      let typs = abstract_typ typ1 in
      let aux typ1 typ2 = TFun(typ1, fun _ -> typ2) in
      [List.fold_right aux typs @@ List.get @@ abstract_typ typ2]
  | TApp(TConstr (TFixPred _), ty) -> abstract_typ ty
  | _ -> assert false

let abstract_typ typ = List.get @@ abstract_typ typ


let abstract_def env (f,xs,t1,e,t2) =
  let xs,t1,t2 =
    if List.exists (fun x -> x = "l0" || x = "l1") xs then
      let xs' = List.map (fun x -> x ^ "___") xs in
      let map = List.map2 (fun x x' -> x, Var x') xs xs' in
      let t1' = subst_map map t1 in
      let t2' = subst_map map t2 in
      xs', t1', t2'
    else
      xs, t1, t2
  in
  let typ,env' = decomp_typ_var (List.assoc f env) xs in
  if false then Debug.printf "%a: ENV: %a@." CEGAR_print.var f print_env env';
  let env'' = env' @@@ env in
  let pts = List.flatten_map (Fun.uncurry make_pts) env' in
  let xs' = List.flatten_map (Fun.uncurry abst_arg) env' in
  if false then Debug.printf "%a: %a ===> %a@." CEGAR_print.var f CEGAR_print.term t2 CEGAR_print.term t2;
  if Debug.check() then Flag.Print.fun_arg_typ := true;
  if false then Debug.printf "%s:: %a@." f CEGAR_print.term t2;
  let t2' =
    abstract_term env'' [t1] pts t2 typ
    |> make_let'
    |> eta_reduce_term
  in
  if e <> [] && t1 <> Const True then
    let g = rename_id f in
    let fv = List.Set.diff (get_fv t2') (List.map fst env) in
    [g, fv, Const True, e, t2';
     f, xs', Const True, [], assume env' [] pts t1 @@ make_app (Var g) (List.map _Var fv)]
  else
    [f, xs', Const True, e, assume env' [] pts t1 t2']

let abstract_prog prog =
  let env =
    get_ext_funs prog
    |> List.filter_out is_randint_var
    |> List.map (fun f -> f, abstract_typ @@ List.assoc f prog.env)
  in
  let defs = List.flatten_map (abstract_def prog.env) prog.defs in
  let attr = List.remove_all prog.info.attr ACPS in
  {env; defs; main=prog.main; info={prog.info with attr}}

let pr s prog = Debug.printf "@.##[%.3f][CEGAR_abst_CPS] %a:@.%a@.@." !!Time.get Color.s_red s CEGAR_print.prog prog

let abstract prog preprocessed =
  let labeled,prog = add_label prog in
  let b = not !Flag.PredAbst.no_simplification in
  let preprocessed =
    match preprocessed with
    | None ->
        prog
        |@> pr "INPUT"
        |&b&> expand_non_rec
        |@b&> pr "EXPAND_NONREC"
        |&b&> CEGAR_trans.simplify_if
        |@b&> pr "SIMPLIFY_IF"
    | Some p -> p
  in
  let abstracted =
    {preprocessed with env=prog.env}
    |> fixpred_to_abstpred
    |> eta_expand (* assign types to arguments *)
    |@> pr "ETA_EXPAND"
    |> abstract_prog
    |@> pr "ABST"
    |&b&> CEGAR_trans.simplify_if
    |@b&> pr "SIMPLIFY_IF"
    |> Typing.infer ~fun_annot:true ~rename:true -| initialize_env
    |@!Flag.Debug.abst&> eval_step_by_step
    |> trans_eager
    |@> pr "TRANS_EAGER"
    |&b&> put_arg_into_if
    |&b&> Typing.infer
    |@b&> pr "PUT_INTO_IF"
    |> CEGAR_lift.lift2
    |@> pr "LIFT"
  in
  labeled, Some preprocessed, abstracted
