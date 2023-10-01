open Util
open Mochi_util
open CEGAR_syntax
open CEGAR_type
open CEGAR_util

type result =
  | Feasible of int list
  | FeasibleNonTerm of bool * (string * CEGAR_syntax.typ) list * int list
  | Infeasible of CEGAR_syntax.ce

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type env =
  {ce : int list;                                      (* counterexample: list of integers whose element represents which branch is taken *)
   sat : bool;                                         (* true denotes constr is satisfiable *)
   n : int;                                            (* length of infeasible prefix *)
   constr : CEGAR_syntax.t;                            (* constraints of which we will check the satisfiability *)
   tenv : (string * CEGAR_syntax.t CEGAR_type.t) list} (* type environment (actually, types are unused as all variables are assumed to be integers) *)

let init_env ce =
  {ce;
   sat = true;
   n = 0;
   constr = Const True;
   tenv = []}

let checksat {constr; _} =
  constr
  |> Encode_set_theory.add
  |> FpatInterface.conv_formula
  |> Fpat.SMTProver.is_sat_dyn

let get_solution {tenv; constr; _} =
  let sol =
    constr
    |> FpatInterface.conv_formula
    |> Fpat.PolyConstrSolver.solve_dyn
    |> List.map (Pair.map Fpat.Idnt.string_of Fpat.IntTerm.int_of)
  in
  let sol' = List.map (fun (x,_) -> x, List.assoc_default 0 x sol) tenv in
  List.map snd @@ List.sort compare sol'

let init_cont (env,_) =
  assert (Flag.(!mode <> FairNonTermination && not !Debug.input_cex) => (env.ce=[]));
  env

let assoc_def defs n t =
  let defs' = List.filter (fun def -> Var def.fn = t) defs in
  List.length defs', List.nth defs' n

let add_randint_precondition map_randint_to_preds ext_ce rand_precond r = function
  | None -> rand_precond, ext_ce
  | Some(n) ->
    let new_var = Var(r) in
    let abst_preds = try (List.assoc n map_randint_to_preds) new_var with Not_found -> Format.fprintf !Flag.Print.target "not found: %d@." n; [] in
    let _rand_var = FpatInterface.conv_var r in
    match ext_ce with
    | (m, bs)::ext_ce' when m=n ->
       Verbose.printf "add_randint %d %d@." (List.length abst_preds) (List.length bs);
       let asm_cond = List.fold_left2 (fun acc p b -> make_and (if b then p else make_not p) acc) (Const True) abst_preds bs in
       make_and rand_precond asm_cond, ext_ce'
    | _ -> assert false

let map_randint_to_preds_ref = ref []
let ext_ce_ref = ref []
let rand_precond_ref = ref (Const True)
let init_refs mrtp ec = begin
  map_randint_to_preds_ref := mrtp;
  ext_ce_ref := ec;
  rand_precond_ref := Const True;
end
let add_randint_precondition r n =
  let (c, e) = add_randint_precondition !map_randint_to_preds_ref !ext_ce_ref !rand_precond_ref r n in
  ext_ce_ref := e;
  rand_precond_ref := c

let rec check_aux
          ?(pr : (CEGAR_syntax.t -> int -> int -> unit) = fun _ _ _ -> ()) (* printer; see print_ce_reduction *)
          (env : env)
          (defs : CEGAR_syntax.fun_def list) (* function definitions*)
          (t : CEGAR_syntax.t) (* the term to be reduced *)
          k (* continuation *)
  =
  Debug.printf "check_aux[%d]: %a@." (List.length env.ce) CEGAR_print.term t;
  match t with
  | Const (Rand(TInt,_)) -> assert false
  | Const c -> k (env, Const c)
  | Var x -> k (env, Var x)
  | App(Const Not, t) ->
      let@ env,t = check_aux ~pr env defs t in
      k (env, Term.(not t))
  | App(App(Const op,t1),t2) when is_binop op ->
      let@ env,t1 = check_aux ~pr env defs t1 in
      let@ env,t2 = check_aux ~pr env defs t2 in
      k (env, Term.(t1 <|op|> t2))
  | App _ when is_app_randint t ->
      pr t 0 1;
      if Flag.(!mode = FairNonTermination) && !ext_ce_ref = [] then
        init_cont (env,t)
      else
        let t',randnum =
          let t_rand,ts = decomp_app t in
          match t_rand with
          | Const (Rand(TInt,randnum)) -> List.last ts, randnum
          | _ -> assert false
        in
        let r = new_id "r" in
        add_randint_precondition r randnum;
        let tenv = (r,typ_int)::env.tenv in
        check_aux ~pr {env with tenv} defs (App(t',Var r)) k
  | App(Const (Event "fail"), t) -> init_cont (env, t)
  | App(t1,t2) ->
      let@ env,t1 = check_aux ~pr env defs t1 in
      let@ env,t2 = check_aux ~pr env defs t2 in
      begin
        match env.ce with
        | [] ->
            if Flag.(!mode = FairNonTermination) then
              init_cont (env, App (t1, t2))
            else
              assert false
        | c::ce' ->
            let t1',ts = decomp_app (App(t1,t2)) in
            let {args=xs} = List.find (fun def -> Var def.fn = t1') defs in
            if List.length xs > List.length ts then
              k (env, App(t1,t2))
            else
              let num,{args=xs;cond=tf1;body=tf2} = assoc_def defs c t1' in
              let ts1,ts2 = List.split_nth (List.length xs) ts in
              let aux = List.fold_right2 subst xs ts1 in
              rand_precond_ref := aux !rand_precond_ref;
              let tf1' = aux tf1 in
              let tf2' = make_app (aux tf2) ts2 in
              let constr = make_and tf1' env.constr in
              let n = if env.sat then env.n+1 else env.n in
              let sat = env.sat && checksat {env with constr} in
              assert (List.length xs = List.length ts);
              assert (ts2 = []);
              pr t1' c num;
              let env = {env with ce=ce'; sat; n; constr} in
              check_aux ~pr env defs tf2' k
      end
  | Let _ -> assert false
  | Fun _ -> assert false

let rec get_prefix ce n =
  match ce with
  | [] -> assert (n=0); ce
  | _::_ when n = 0 -> []
  | c::ce' -> c::get_prefix ce' (n-1)

let check ce {defs; main} =
  Verbose.printf "Spurious counterexample::@.  %a@.@." CEGAR_print.ce ce;
  let time_tmp = Time.get () in
  Verbose.printf ~color:Green "%a(%d-3)[%.3f] Checking counterexample ...%t @?" Color.set Green !Flag.Log.cegar_loop !!Time.get Color.reset;
  set_status @@ Flag.Log.Other (Format.sprintf "(%d-3) Feasibility checking" !Flag.Log.cegar_loop);
  if false then Format.fprintf !Flag.Print.target "ce:	  %a@." CEGAR_print.ce ce;
  let ce' = List.tl ce in
  let {body=t} = List.find (fun def -> def.fn = main) defs in
  let env = check_aux (init_env ce') defs t init_cont in
  let prefix = get_prefix ce (env.n+1) in
  Debug.printf "constr: %a@." CEGAR_print.term env.constr;
  let result =
    if checksat env
    then
      let solution = get_solution env in
      Feasible solution
    else Infeasible prefix
  in
  Verbose.printf ~color:Green "DONE!@.@.";
  Time.add time_tmp Flag.Log.Time.cegar;
  result

let check_non_term ?(map_randint_to_preds = []) ?(ext_ce = []) ce {defs; main} =
  (* List.iter (fun (n, bs) -> Format.fprintf !Flag.Print.target "C.E.: %d: %a@." n (print_list Format.pp_print_bool ",") bs) ext_ce; *)
  Verbose.printf "Spurious counterexample::@.  %a@.@." CEGAR_print.ce ce;
  let time_tmp = Time.get () in
  Verbose.printf ~color:Green "(%d-3)[%.3f] Checking counterexample ... @?" !Flag.Log.cegar_loop !!Time.get;
  set_status @@ Flag.Log.Other (Format.sprintf "(%d-3) Feasibility checking" !Flag.Log.cegar_loop);
  if false then Format.fprintf !Flag.Print.target "ce:        %a@." CEGAR_print.ce ce;
  let ce' = List.tl ce in
  let {body=t} = List.find (fun def -> def.fn = main) defs in
  init_refs map_randint_to_preds ext_ce; (* initialize abstraction predicate path of randint *)
  let env = check_aux (init_env ce') defs t init_cont in

  let prefix = get_prefix ce (env.n+1) in
  let result =
    if checksat {env with constr = (make_and env.constr !rand_precond_ref)} then
      let solution = get_solution env in
(* @master branch
      let env' = List.sort ~cmp:(Compare.on fst) env' in
      let solution = List.map (fun (x,_) -> List.assoc_default 0 x solution) env'' in
*)
      FeasibleNonTerm (FpatInterface.implies [FpatInterface.conv_formula !rand_precond_ref] [FpatInterface.conv_formula env.constr], env.tenv, solution)
    else Infeasible prefix
  in
  Verbose.printf ~color:Green "Feasibility constraint: %a@." CEGAR_print.term env.constr;
  Verbose.printf ~color:Green "Randint constraint: %a@." CEGAR_print.term !rand_precond_ref;
  Verbose.printf ~color:Green "DONE!@.@.";
  Time.add time_tmp Flag.Log.Time.cegar;
  result





let init_cont (ce, ce_br, _env, _) = assert (ce=[]); List.rev ce_br

let assoc_def defs n t ce_br =
  let defs' = List.filter (fun def -> Var def.fn = t) defs in
  let len = List.length defs' in
  let ce_br' = if len > 1 then (n=0)::ce_br else ce_br in
  ce_br', List.nth defs' n

let rec trans_ce ce ce_br env defs t k =
  Debug.printf "trans_ce[%d]: %a@." (List.length ce) CEGAR_print.term t;
  match t with
  | Const (Rand(TInt,_)) -> assert false
  | Const c -> k (ce, ce_br, env, Const c)
  | Var x -> k (ce, ce_br, env, Var x)
  | App(App(Const (And|Or|Lt|Gt|Leq|Geq|EqUnit|EqBool|EqInt|Add|Sub|Mul|Div as op),t1),t2) ->
      let@ ce,ce_br,env,t1 = trans_ce ce ce_br env defs t1 in
      let@ ce,ce_br,env,t2 = trans_ce ce ce_br env defs t2 in
      k (ce, ce_br, env, Term.(t1 <|op|> t2))
(*
  | App(Const (Event s), t) -> trans_ce ce constr env defs (App(t,Const Unit)) k
*)
  | App(Const (Rand(TInt,None)), t) ->
      let r = new_id "r" in
      let env' = (r,typ_int)::env in
      trans_ce ce ce_br env' defs (App(t,Var r)) k
  | App(Const (Rand(_,Some _)), _) -> assert false
  | App(Const (Rand(_,None)), _) -> assert false
  | App(Const (Event "fail"), t1) -> init_cont (ce, ce_br, env, t1)
  | App(t1,t2) ->
      let@ ce,ce_br,env,t1 = trans_ce ce ce_br env defs t1 in
      let@ ce,ce_br,env,t2 = trans_ce ce ce_br env defs t2 in
      let t1',ts = decomp_app (App(t1,t2)) in
      let {args=xs} = List.find (fun def -> Var def.fn = t1') defs in
      if List.length xs > List.length ts then
        k (ce, ce_br, env, App(t1,t2))
      else
        let ce_br',{args=xs;body=tf2} = assoc_def defs (List.hd ce) t1' ce_br in
        let ts1,ts2 = List.split_nth (List.length xs) ts in
        let aux = List.fold_right2 subst xs ts1 in
        let tf2' = make_app (aux tf2) ts2 in
        let ce' = List.tl ce in
        assert (List.length xs = List.length ts);
        assert (ts2 = []);
        trans_ce ce' ce_br' env defs tf2' k
  | Let _ -> assert false
  | Fun _ -> assert false

let trans_ce ce {defs=defs;main=main} =
  Debug.printf "ce:        %a@." CEGAR_print.ce ce;
  let ce' = List.tl ce in
  let {body=t} = List.find (fun def -> def.fn = main) defs in
  trans_ce ce' [] [] defs t init_cont







let print_ce_reduction ?(map_randint_to_preds = []) ?(ext_ce = []) ce {defs=defs;main=main} =
  let ce' = List.tl ce in
  let {body} = List.find (fun def -> def.fn = main) defs in
  (* t: Term to be printed *)
  (* br: branch will be taken *)
  (* n: Number of the branches *)
  let pr t br n =
    let s1 = if n = 1 then "" else " [" ^ string_of_int (br+1) ^ "/" ^ string_of_int n ^ "]" in
    Format.fprintf !Flag.Print.target "%a%s ... --> @\n" CEGAR_print.term t s1
  in
  init_refs map_randint_to_preds ext_ce; (* initialize abstraction predicate path of randint *)
  Format.fprintf !Flag.Print.target "Error trace::@\n  @[";
  pr (Var main) 0 1;
  (match body with
   | App(Const (Event "fail"), _) -> ()
   | _ -> ignore (check_aux ~pr (init_env ce') defs body (fun _ -> assert false)));
  Format.fprintf !Flag.Print.target "ERROR!@.@."
