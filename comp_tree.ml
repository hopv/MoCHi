open Util
open Syntax
open Term_util
open Type
open Modular_common

module RT = Rose_tree

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type nlabel =
  | App of id * (id * value) list
  | Let of id * term
  | Assume of term
  | Branch of label option
  | Spawn of id
  | Fail
  | End
and t = node RT.t
and node =
  {nid : nid; (* ID of node *)
   val_env : val_env; (* Value environment *)
   var_env : var_env; (* Scope environment: var_env(x) is a set of variables which are visible from x *)
   ce_env : ce_env; (* Counterexamples *)
   nlabel : nlabel}
and nid = int
and var_env = (id * id list) list
and val_env = (id * value) list
and ce_env = ce list
and value = Closure of var_env * val_env * term



let rec pr_bind depth fm (x,vl) =
  let Closure(var_env,val_env,t) = vl in
  if false then
    Format.fprintf fm "@[%a%a@]" (List.print Id.print) (List.map fst var_env) Print.term t
  else if depth <= 0 then
    Format.fprintf fm "@[%a := %a@]" Id.print x Print.term t
  else
    Format.fprintf fm "@[%a := %a%a@]" Id.print x (pr_env (depth-1)) val_env Print.term t
and pr_env depth fm env = List.print (pr_bind depth) fm env
let pr_env fm env = pr_env 0 fm env

let rec print_tid = Format.pp_print_int
and print_nlabel fm nlabel =
  match nlabel with
  | App(f,map) when true ->
      Format.fprintf fm "@[App %a %a@]" Id.print f pr_env map
  | App(f,map) ->
      Format.fprintf fm "@[App %a ...@]" Id.print f
  | Let(f,t) when false ->
      Format.fprintf fm "@[Let %a =@ %a@]" Id.print f Print.term t
  | Let(f,t) ->
      Format.fprintf fm "@[Let %a =@ ...@]" Id.print f
  | Assume t -> Format.fprintf fm "@[Assume %a@]" Print.term t
  | Branch None -> Format.fprintf fm "Branch"
  | Branch (Some label) -> Format.fprintf fm "Branch %d" label
  | Spawn f -> Format.fprintf fm "Spawn %a" Id.print f
  | Fail -> Format.fprintf fm "Fail"
  | End -> Format.fprintf fm "End"
and print_value fm (Closure(var_env,val_env,t)) =
  Format.fprintf fm "Value %a" Print.term t
and print_node fm {nid;var_env;val_env;ce_env;nlabel} =
  if false then
    Format.fprintf fm "%d,@ @[(*%a*)@],@ @[%a@]" nid (List.print Id.print) (List.map fst val_env) print_nlabel nlabel
  else
    Format.fprintf fm "%d,@ @[%a@],@ %a" nid print_nlabel nlabel (List.print print_ce) ce_env
let rec print fm (Rose_tree.Node(node,ts)) =
  Format.fprintf fm "(@[<hov>%a,@ %a@])" print_node node (List.print print) ts


let counter = Counter.create ()
let make_new_tid () = Counter.gen counter

let get_tid t = get_id t
let get_tid_option t = get_id_option t

let rename_tid_if = make_trans2 ()
let rename_tid_if_term map t =
  match t.desc, get_tid_option t with
  | If _, Some tid ->
      replace_id tid (List.assoc tid map) @@ rename_tid_if.tr2_term_rec map t
  | _ -> rename_tid_if.tr2_term_rec map t
let () = rename_tid_if.tr2_term <- rename_tid_if_term
let rename_tid_if = rename_tid_if.tr2_term

let term_of_value (Closure(_,_,t)) = t
let var_env_of_value (Closure(env,_,_)) = env
let val_env_of_value (Closure(_,env,_)) = env

let is_fail t =
  match t.desc with
  | App({desc=Event("fail",_)}, [_]) -> true
  | _ -> false

let rec arity fun_env val_env t =
  assert (is_value t);
  match t.desc with
  | Var f when Id.mem_assoc f fun_env -> List.length @@ fst @@ Id.assoc f fun_env
  | App(t1, ts) -> arity fun_env val_env t1 - List.length ts
  | _ -> assert false

let rec is_value fun_env val_env t =
  match t.desc with
  | BinOp(And, _, _) -> assert false
  | BinOp(Or, _, _) -> assert false
  | Var _ -> assert false
  | Const _ -> true
  | BinOp(_, t1, t2) -> is_value fun_env val_env t1 && is_value fun_env val_env t2
  | Not t -> is_value fun_env val_env t
  | Fun _ -> true
  | Event _ -> true
  | App(t1, ts) ->
      is_value fun_env val_env t1 &&
      arity fun_env val_env t < List.length ts &&
      List.for_all (is_value fun_env val_env) ts
  | _ -> false

let rename_var nid x =
  let name = Format.asprintf "%a@%d" Id.print x nid in
  let id = 0 in
  {x with Id.name; id}
let rename_var _ x = Id.new_var_id x

let assoc_fun nid f var_env val_env =
  let Closure(var_env_f, val_env_f, t) = Id.assoc f val_env in
  let ys,t' =  match t.desc with
    | Var f ->
        let xs,_ = Type.decomp_tfun @@ Id.typ f in
        xs, make_app (make_var f) @@ List.map make_var xs
    | _ -> decomp_funs t
  in
  let ys' = List.mapi (fun i y -> Id.make 0 (Format.asprintf "%a@%d" Id.print f i) [] (Id.typ y)) ys in
  Debug.printf "    ALPHA: %a => %a@\n" (List.print Id.print) ys (List.print Id.print) ys';
  let t'' = List.fold_right2 subst_var ys ys' t' in
  var_env_f, val_env_f, (ys', t'')

let ends = RT.exists (fun {nlabel} -> nlabel = Fail || nlabel = End)

let make_arg_map var_env val_env _ xs ts =
  let value_of t = Closure(var_env, val_env, t) in
  List.combine xs @@ List.map value_of ts

let filter_extend extend = List.filter_out (fun (_,n) -> n <= 0) extend

let rec from_app_term
          nid f ts
          (cnt : Counter.t)  (* counter for nid *)
          (fun_env : (id * (term * ce list)) list)
          (var_env : var_env)  (* scope environment *)
          (val_env : val_env)  (* value environment *)
          (ce_env : ce_env)  (* counterexamples *)
          (spawned : Syntax.id list)  (* list of ids spawned *)
          (depth : int)
          (t : term)  (* term to be reduced *) =
  Debug.printf "  APP: %a@\n" Print.term t;
  let var_env_f,val_env_f,(ys,t_f) = assoc_fun nid f var_env val_env in
  Debug.printf "    APP (ys -> t_f): %a, %d@\n" Print.term (make_funs ys t_f) (List.length ts);
  Debug.printf "    APP var_env_f: %a@\n" (List.print @@ Pair.print Id.print @@ List.print Id.print) var_env_f;
  let arg_map = make_arg_map var_env val_env f ys ts in
  Debug.printf "    APP arg_map: %a@\n" pr_env arg_map;
  let val_env' = List.rev arg_map @ val_env_f in
  Debug.printf "    APP val_env': %a@\n" pr_env val_env';
  let vars_f = Id.assoc f var_env in
  let var_env',_ = List.fold_left (fun (acc,vars) x -> (x, vars)::acc, x::vars) (var_env_f,vars_f) ys in
  Debug.printf "    APP var_env': %a@\n" (List.print @@ Pair.print Id.print @@ List.print Id.print) var_env';
  let node = {nid; var_env; val_env; ce_env; nlabel = App(f, arg_map)} in
  assert (List.Set.eq ~eq:Id.eq (List.map fst var_env') (List.map fst val_env'));
  let ce_env' = ce_env in
  RT.Node(node, [from_term cnt fun_env var_env' val_env' ce_env' spawned depth t_f])

(* 't' must be a CPS term *)
and from_term
      (cnt : Counter.t)  (* counter for nid *)
      (fun_env : (id * (term * ce list)) list)
      (var_env : var_env)  (* scope environment *)
      (val_env : val_env)  (* value environment *)
      (ce_env : ce_env)  (* counterexamples *)
      (spawned : Syntax.id list)  (* list of ids spawned *)
      (depth : int)
      (t : term)  (* term to be reduced *)
    : t =
  let nid = Counter.gen cnt in
  Debug.printf "TERM: %a@\n" Print.term t;
  Debug.printf "  val_env: %a@\n" pr_env val_env;
  Debug.printf "  Dom(var_env): %a@\n" (List.print Id.print) @@ List.map fst var_env;
  Debug.printf "  Dom(val_env): %a@\n" (List.print Id.print) @@ List.map fst val_env;
  Debug.printf "  ce_env: %a@\n" (List.print @@ print_ce) ce_env;
  assert (List.Set.eq ~eq:Id.eq (List.map fst var_env) (List.map fst val_env));
  match t.desc with
  | Const Unit ->
      let node = {nid; var_env; val_env; ce_env; nlabel = End} in
      RT.Node(node, [])
  | App({desc=Const(Rand(TBase TInt, true))}, [{desc=Const Unit}; {desc=Fun(x,t2)}]) ->
      let t2' = subst_var x (rename_var nid x) t2 in
      from_term cnt fun_env var_env val_env ce_env spawned depth t2'
  | App({desc=Var f}, ts) when Id.mem_assoc f fun_env -> (* Top-level functions *)
      Debug.printf "  APP2,%a@\n" Id.print f;
      let t_f,ce_env_f = Id.assoc f fun_env in
      let f' = Id.make 0 (Format.asprintf "%a:%d" Id.print f nid) [] (Id.typ f) in
      Debug.printf "    SPAWN: %a => %a@\n" Id.print f Id.print f';
      let tid_map =
        t_f
        |> col_id
        |> List.map (fun x -> x, make_new_tid ())
      in
      Debug.printf "tid_map: %a@." (List.print @@ Pair.print Format.pp_print_int Format.pp_print_int) tid_map;
      let t' = make_app (make_var f') ts in
      let child =
        let var_env' = (f', []) :: var_env in
        let val_env' =
          let t_f' =
            t_f
            |*> Trans.alpha_rename
            |> subst_var f f'
            |> rename_tid_if tid_map
          in
          let rec val_env_f' = [f', Closure([f', []], val_env_f', t_f')] in
          val_env_f' @ val_env
        in
        let ce_env' =
          let ce_env_f' = List.map (List.map (fun (n,t) -> List.assoc_default n n tid_map, t)) ce_env_f in
          ce_env_f' @ ce_env
        in
        from_app_term (Counter.gen cnt) f' ts cnt fun_env var_env' val_env' ce_env' spawned depth t' in
      let node = {nid; var_env; val_env; ce_env; nlabel=Spawn f} in
      RT.Node(node, [child])
  | App({desc=Fun(x,t); typ}, t2::ts) ->
      assert ( is_simple_aexp t2 || is_simple_bexp t2 || is_randint_unit t2 || is_randbool_unit t2 || is_var t2);
      let var_env' = (x, List.map fst val_env)::var_env in
      let val_env' = (x, Closure(var_env, val_env, t2))::val_env in
      from_term cnt fun_env var_env' val_env' ce_env spawned depth (make_app t ts)
  | App({desc=Var f}, ts) ->
      let f',var_env',val_env',t' =
        if true || List.exists (fst |- same_top_fun f) fun_env then
          let f' = compose_id ~nid f in
          let var_env' = (f',Id.assoc f var_env)::var_env in
          let val_env' = (f',Id.assoc f val_env) :: val_env in
          let t' = subst_var f f' t in
          f',var_env', val_env', t'
        else
          f,var_env, val_env, t
      in
      from_app_term nid f' ts cnt fun_env var_env' val_env' ce_env spawned depth t'
  | If(t1, t2, t3) ->
      Debug.printf "  IF t1: %a@\n" Print.term t1;
      let tid = get_id_option t in
      let aux br ce_env' depth =
        let nid = Counter.gen cnt in
        let cond,t23 = if br then t1, t2 else make_not t1, t3 in
        Debug.printf "    t23: %a@\n" Print.term t23;
        let node = {nid; var_env; val_env; ce_env=ce_env'; nlabel=Assume cond} in
        RT.Node(node, [from_term cnt fun_env var_env val_env ce_env' spawned depth t23])
      in
      let children =
        match tid with
        | None -> [aux true ce_env depth; aux false ce_env depth]
        | Some tid ->
            Debug.printf "    tid: %d@\n" tid;
            let ce_env1,ce_env2 = List.partition (List.mem_assoc tid) ce_env in
            let ce_env2' = List.filter_out ((=) []) ce_env2 in
            let then_ce_env,else_ce_env =
              let peek ce = List.assoc tid ce in
              let pop ce = List.remove_assoc tid ce in
              let aux (t_acc,e_acc) ce =
                let ce' = pop ce in
                if peek ce then
                  ce'::t_acc,e_acc
                else
                  t_acc, ce'::e_acc
              in
              List.fold_left aux ([],[]) ce_env1
            in
            let child1 =
              if then_ce_env = [] then
                if is_fail t3 then
                  [aux true ce_env2' depth]
                else
                  []
              else
                [aux true (then_ce_env@ce_env2') depth]
            in
            let child2 =
              if else_ce_env = [] then
                if then_ce_env = [] && is_fail t3 then
                  [aux false [] depth]
                else
                  []
              else
                [aux false (else_ce_env@ce_env2') depth]
            in
            if child1 = [] && child2 = [] && ce_env2' <> [] && depth > 0 then
              (Debug.printf "STUCK@."; [aux true ce_env2' (depth-1); aux false ce_env2' (depth-1)])
            else
              child1 @ child2
      in
      let node = {nid; val_env; var_env; ce_env; nlabel = Branch tid} in
      RT.Node(node, children)
  | Local(Decl_let [f,({desc=Bottom} as t1)], _) ->
      from_term cnt fun_env var_env val_env ce_env spawned depth t1
  | Local(Decl_let [f,t1], t2) ->
      let xs,t1 = decomp_funs t1 in
      Debug.printf "  LET@\n";
      Debug.printf "    t: %a@\n" Print.term t;
      assert (xs <> []);
      let f' = Id.make 0 (Format.asprintf "%a:%d" Id.print f nid) [] (Id.typ f) in
      let t1' = subst_var f f' t1 in
      let t2' = subst_var f f' t2 in
      let var_env' = (f', List.map fst val_env)::var_env in
      let rec val_env' = (f', Closure(var_env', val_env', make_funs xs t1'))::val_env in
      let node = {nid; var_env; val_env; ce_env; nlabel = Let(f', make_funs xs t1')} in
      RT.Node(node, [from_term cnt fun_env var_env' val_env' ce_env spawned depth t2'])
  | _ when is_fail t ->
      let node = {nid; var_env; val_env; ce_env; nlabel = Fail} in
      RT.Node(node, [])
  | _ when t.desc = Bottom ->
      let node = {nid; var_env; val_env; ce_env; nlabel = End} in
      RT.Node(node, [])
  | _ ->
      Format.eprintf "@.t: @[%a@." Print.term t;
      Format.eprintf "Dom(val_env): %a@." (List.print Id.print) @@ List.map fst val_env;
      let f = match t.desc with App({desc=Var f},_) -> f | _ -> assert false in
      Format.eprintf "%a is in Dom(val_env)?: %b@." Id.print f (Id.mem_assoc f val_env);
      unsupported "Comp_tree.from_term"
let from_term fun_env var_env val_env ce_env t =
  from_term (Counter.create()) fun_env var_env val_env ce_env t

let rec filter_ends (RT.Node(node,ts)) =
  let check (RT.Node({nlabel},ts)) =
    ts <> [] || nlabel = Fail(* || nlabel = End*)
  in
  let ts' =
    ts
    |> List.map filter_ends
    |> List.filter check
  in
  RT.Node(node, ts')

let from_program (fun_env: (id * term) list) (ce_set:ce_set) depth t =
  Counter.reset counter;
  Debug.printf "@.CE_SET: %a@." print_ce_set ce_set;
  Debug.printf "FUN_ENV: %a@." (List.print @@ Pair.print Id.print Print.term) fun_env;
  Debug.printf "from_program: %a@." Print.term t;
  let fun_env' =
    List.map (fun (f,t) -> f, (t, List.assoc_all ~eq:Id.eq f ce_set)) fun_env
  in
  let var_env = [] in
  let val_env = [] in
  let ce_env = [] in
  t
  |> from_term fun_env' var_env val_env ce_env [] depth
  |@> Debug.printf "@.@.comp_tree:@.%a@.@." print
  |*> filter_ends (* "filter_ends" causes NoProgress *)
  |*@> Debug.printf "@.@.comp_tree':@.%a@.@." print
