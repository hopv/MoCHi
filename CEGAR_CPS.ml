open CEGAR_syntax
open CEGAR_type
open CEGAR_print
open CEGAR_util
open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let is_head_tuple t =
  match decomp_app t with
  | Const (Tuple _), _::_ -> true
  | _ -> false

let and_cps = "and_cps"
let or_cps = "or_cps"
let not_cps = "not_cps"
let and_def = and_cps, ["x"; "y"; "k"], Const True, [], (make_if (Var "x") (App(Var "k", Var "y")) (App(Var "k", Const False)))
let or_def = or_cps, ["x"; "y"; "k"], Const True, [], (make_if (Var "x") (App(Var "k", Const True)) (App(Var "k", Var "y")))
let not_def = not_cps, ["x"; "k"], Const True, [], (make_if (Var "x") (App(Var "k", Const False)) (App(Var "k", Const True)))

let rec trans_const = function
  | Const (Int _ | Unit | True | False | Rand(TBool,_) | If | Tuple _ | Bottom | Label _ as c) -> Const c
  | Const Not -> Var not_cps
  | Const c -> Format.eprintf "TRANS_CONST: %a@." CEGAR_print.const c; assert false
  | Var x -> Var x
(*
  | App(App(Const (Label n), t1), t2) -> App(Const (Label n), App(t2, t1))
*)
(*
  | App _ as t when is_head_tuple t ->
      let t',ts = decomp_app t in
      let ts' = List.map trans_const ts in
      let n = match t' with Const (Tuple n) -> n | _ -> assert false in
        if List.length ts' = n
        then make_app t' ts'
        else
          let ts1,ts2 = take2 ts' n in
            if ts2 = [] then (Format.eprintf "%a@." print_term t; assert false);
            make_app (List.hd ts2) ((make_app t' ts1)::List.tl ts2)
*)
  | App(App(Const (Proj(n,i)), t1), t2) -> App(trans_const t2, App(Const (Proj(n,i)), trans_const t1))
  | App(t1,t2) -> App(trans_const t1, trans_const t2)
  | Let(x,t1,t2) -> Let(x, trans_const t1, trans_const t2)
  | Fun(x,typ,t) -> Fun(x, typ, trans_const t)

let rec trans_simpl c = function
  | Const x -> c (Const x)
  | Var x -> c (Var x)
  | App(App(App(Const If, t1), t2), t3) ->
      let k = new_id "k" in
      let x = new_id "b" in
      let t2' = trans_simpl (fun y -> App(Var k, y)) t2 in
      let t3' = trans_simpl (fun y -> App(Var k, y)) t3 in
      let c' y =
        match c (Var x) with
        | App(Var k', Var x') when x = x' -> subst k (Var k') (make_if y t2' t3')
        | tk -> Let(k, Fun(x, None, tk), make_if y t2' t3')
      in
      trans_simpl c' t1
  | App(App(Const And, t1), t2) ->
      let x = new_id "b" in
      let c1 t1' t2' =
        let k' =
          match c (Var x) with
          | App(Var k', Var x') when x = x' -> Var k'
          | tk -> Fun(x, None, tk)
        in
        make_app (Var and_cps) [t1';t2';k']
      in
      let c2 y1 = trans_simpl (fun y2 -> c1 y1 y2) t2 in
      trans_simpl c2 t1
  | App(App(Const Or, t1), t2) ->
      let x = new_id "b" in
      let c1 t1' t2' =
        let k' =
          match c (Var x) with
          | App(Var k', Var x') when x = x' -> Var k'
          | tk -> Fun(x, None, tk)
        in
        make_app (Var or_cps) [t1';t2';k']
      in
      let c2 y1 = trans_simpl (fun y2 -> c1 y1 y2) t2 in
      trans_simpl c2 t1
  | App _ as t when is_head_tuple t ->
      let t',ts = decomp_app t in
      let n = match t' with Const (Tuple n) -> n | _ -> assert false in
      assert (List.length ts = n);
      let c' = List.fold_right (fun t cc -> fun x -> trans_simpl (fun y -> cc (App(x, y))) t) ts c in
      trans_simpl c' (Const (Tuple n))
  | App(Const (Label n) as lbl, t) ->
      App(lbl, trans_simpl c t)
  | App(t1, t2) ->
      let r = new_id "r" in
      let c' y =
        let k' =
          match c (Var r) with
            App(Var k', Var r') when r = r' -> Var k'
          | tk -> Fun(r, None, tk)
        in
        trans_simpl (fun x -> make_app y [x; k']) t2
      in
      trans_simpl c' t1
  | Let(x,t1,t2) ->
      let c' t = subst x t (trans_simpl c t2) in
      trans_simpl c' t1
  | Fun(x,_,t) ->
      let k = new_id "k" in
      c (Fun(x, None, Fun(k, None, trans_simpl (fun x -> App(Var k, x)) t)))

let trans_simpl_def (f,xs,t1,e,t2) =
  assert (xs = []);
  let t2 = trans_simpl (fun x -> x) t2 in
  Debug.printf "TRANS1: %a@." CEGAR_print.term t2;
  let t2 = trans_const t2 in
  Debug.printf "TRANS2: %a@." CEGAR_print.term t2;
  (f, [], t1, e, t2)



let hd x = assert (List.length x = 1); List.hd x

let rec extract_tuple_var env x =
  match List.assoc x env with
  | TConstr TTuple -> [x]
  | TApp _ as typ when is_ttuple typ ->
      let typ,typs = decomp_tapp typ in
      let n = List.length typs in
      Array.to_list (Array.init n (fun i -> x ^ string_of_int i))
  | _ -> [x]
let rec extract_tuple_term env = function
    Const (Tuple 0) -> [Const Unit]
  | Const c -> [Const c]
  | Var x -> List.map (fun x -> Var x) (extract_tuple_var env x)
  | App(Const (Proj(_,i)), t2) when is_head_tuple t2 ->
      let t,ts = decomp_app t2 in
      let n = match t with Const (Tuple n) -> n | _ -> assert false in
        assert (List.length ts = n);
        extract_tuple_term env (List.nth (snd (decomp_app t2)) i)
  | App(Const (Proj(_,i)), Var x) ->
      let xs = extract_tuple_var env x in
        [Var (List.nth xs i)]
  | App(t1,t2) when is_head_tuple t2 ->
      let t',ts = decomp_app t2 in
        [make_app t1 ts]
  | App(t1,t2) ->
      [make_app (hd (extract_tuple_term env t1)) (extract_tuple_term env t2)]
(*
  | Let(x,t1,t2) ->
      let t1' = hd (extract_tuple_term env t1) in
      let t2' = hd (extract_tuple_term env t2) in
        [Let(x, t1', t2')]
  | Fun(x,t) ->
      let xs = extract_tuple_var env x in
*)
  | Let _ -> assert false
  | Fun _ -> assert false


let extract_tuple_def env (f,xs,t1,e,t2) =
  let env' = get_arg_env (List.assoc f env) xs @@@ env in
  let xs' = List.flatten (List.map (extract_tuple_var env') xs) in
  let t1' = hd (extract_tuple_term env t1) in
  let t2' = hd (extract_tuple_term env' t2) in
    f, xs', t1', e, t2'
let extract_tuple {env;defs;main;info} =
  let defs = List.map (extract_tuple_def env) defs in
  let () = if false then Format.printf "EXTRACTED:\n%a@." CEGAR_print.prog {env=[];defs;main;info} in
  Typing.infer {env=[];defs;main;info}



let to_funs_def (f,xs,t1,e,t2) = f, [], t1, e, List.fold_right (fun x t-> Fun(x,None,t)) xs t2
let to_funs defs = List.map to_funs_def defs


let rec reduce = function
    Const c -> Const c
  | Var x -> Var x
  | App(Fun(x,_,t1),t2) -> reduce (subst x t2 t1)
  | App(t1,t2) -> App(reduce t1, reduce t2)
  | Fun(x,typ,t) -> Fun(x, typ, reduce t)
  | Let(x,t1,t2) -> reduce (subst x t1 t2)
let reduce_def (f,xs,t1,e,t2) = f,xs,t1,e,reduce t2

let trans {env;defs;main;info} lift_opt =
  let _ = Typing.infer {env;defs;main;info} in
  let defs = to_funs defs in
  let _ = Typing.infer {env;defs;main;info} in
  let defs = List.map trans_simpl_def defs in
  let defs = List.map reduce_def defs in
  let defs = and_def::or_def::not_def::defs in
  let prog = {env; defs; main; info} in
  let () = if false then Format.printf "BEFORE LIFT:\n%a@." CEGAR_print.prog prog in
  let _ = Typing.infer prog in
  let prog = if lift_opt then CEGAR_lift.lift prog else CEGAR_lift.lift2 prog in
  let () = if false then Format.printf "LIFTED:\n%a@." CEGAR_print.prog prog in
  extract_tuple prog
