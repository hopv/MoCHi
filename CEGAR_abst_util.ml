open Util
open CEGAR_syntax
open CEGAR_type
open CEGAR_print
open CEGAR_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let hd (defs,ts) =
  assert (defs = []);
  match ts with
  | [] -> assert false
  | [x] -> x
  | _ -> assert false

let check_aux _ cond p =
  let cond' = List.map FpatInterface.conv_formula cond in
  let p' = FpatInterface.conv_formula p in
  Fpat.SMTProver.implies_dyn cond' [p']

let check env cond pbs p =
  let ps,_ = List.split pbs in
  check_aux env (cond@@@ps) p

let equiv env cond t1 t2 =
  check_aux env (t1::cond) t2 && check_aux env (t2::cond) t1

let satisfiable env cond t =
  not @@ check_aux env cond @@ make_not t


let print_pb fm (p,b) =
  Format.fprintf fm "%a := %a" CEGAR_print.term b CEGAR_print.term p

let print_pbs fm pbs =
  print_list print_pb ";@\n" fm pbs

let min_unsat_cores _ cond ds =
  let ds =
    if !Fpat.PredAbst.use_neg_pred then (* TODO: remove this if statement after Fpat is fixed *)
      List.map (Pair.map make_not make_not) ds @ ds
    else
      ds in
  let cond' = List.map FpatInterface.conv_formula cond in
  let ds' = List.map (Fpat.Pair.lift FpatInterface.conv_formula) ds in
  FpatInterface.inv_formula @@ Fpat.PredAbst.min_unsat_cores cond' ds'

let weakest _ cond ds p =
  let cond' = List.map FpatInterface.conv_formula cond in
  let ds' = List.map (Fpat.Pair.lift FpatInterface.conv_formula) ds in
  let p' = FpatInterface.conv_formula p in
  Fpat.PredAbst.weakest cond' ds' p' |>
    Fpat.Pair.lift FpatInterface.inv_formula




let filter_pbs env cond pbs =
  pbs
  |& !Flag.PredAbst.remove_false &> List.filter_out (check_aux env cond -| fst)
  |> List.filter_out (check_aux env cond -| make_not -| fst)

let filter env cond pbs t =
  Debug.printf "filter@.";
  let pbs' = if !Flag.PredAbst.remove_false then filter_pbs env cond pbs else pbs in
  Debug.printf "  cond: %a@." (print_list  CEGAR_print.term "; ") cond;
(*
  Debug.printf "  orig pbs: @[<hv>%a@." print_pbs pbs;
  let pbss =
    let rec aux sets (p,b) =
      let fv = get_fv p in
      let sets1,sets2 = List.partition (fun set -> List.exists (VarSet.mem -$- set) fv) sets in
      match sets1 with
      | [] -> List.fold_right VarSet.add fv VarSet.empty :: sets
      | _ ->
          let set1 = List.fold_left VarSet.union VarSet.empty sets1 in
          List.fold_right VarSet.add fv set1 :: sets2
    in
    let xss = List.map VarSet.elements @@ List.fold_left aux [] pbs' in
    List.map (fun xs -> List.filter (List.exists (List.mem -$- xs) -| get_fv -| fst) pbs') xss
  in
*)
  let pbss = [pbs'] in
  let aux pbs =
    Debug.printf "  pbs: @[<hv>%a@." print_pbs pbs;
    min_unsat_cores env cond pbs
  in
  let unsats1 = List.map aux pbss in
  let unsats2 = List.filter_map (fun (p,b) -> if check env cond [p,b] @@ Const False then Some b else None) pbs' in
  let unsat = List.fold_left make_or (Const False) (unsats2 @ unsats1) in
  Debug.printf "  unsat:%a@.@." CEGAR_print.term unsat;
  make_if unsat (Const Bottom) t



let abst env cond pbs p =
  Debug.printf "abst@.";
  Debug.printf "  cond: %a@." (print_list  CEGAR_print.term "; ") cond;
  let pbs' = filter_pbs env cond pbs in
  Debug.printf "  pbs: @[<hv>%a@]@.  p:%a@." print_pbs pbs' CEGAR_print.term p;
  if has_bottom p
  then Const Bottom
  else
    let tt, ff = weakest env cond pbs' p in
    Debug.printf "  tt:%a@.  ff:%a@.@." CEGAR_print.term tt CEGAR_print.term ff;
    if make_not tt = ff || tt = make_not ff
    then tt
    else make_if tt (Const True) (make_if ff (Const False) (make_br (Const True) (Const False)))


let assume env cond pbs t1 t2 = filter env (t1::cond) pbs t2


let rec congruent env cond typ1 typ2 =
  match typ1,typ2 with
  | TBase(b1,ps1), TBase(b2,ps2) when b1=b2 ->
      let x = new_id "x_abst" in
      let env' = (x,typ1)::env in
      let ps1' = ps1 (Var x) in
      let ps2' = ps2 (Var x) in
      List.length ps1' = List.length ps2' && List.for_all2 (equiv env' cond) ps1' ps2'
  | TFun(typ11,typ12), TFun(typ21,typ22) ->
      let x = new_id "x_abst" in
      let typ12 = typ12 (Var x) in
      let typ22 = typ22 (Var x) in
      let env' = (x,typ11)::env in
      congruent env cond typ11 typ21 && congruent env' cond typ12 typ22
  | _ -> Format.eprintf "CONGRUENT: %a,%a@." CEGAR_print.typ typ1 CEGAR_print.typ typ2; assert false


let rec is_base_term env t =
  match t with
  | Const (Unit | True | False | Int _ | Rand _ | Char _ | String _ | Float _ | Int32 _ | Int64 _ | Nativeint _) -> true
  | Const _ -> false
  | Var x ->
      (try
          is_base @@ List.assoc x env
        with Not_found ->
          Format.eprintf "%s not found@." x;
          assert false)
  | App(App(Const (And|Or|Lt|Gt|Leq|Geq|EqUnit|EqInt|EqBool|CmpPoly _|Add|Sub|Mul|Div),t1),t2) ->
      assert (is_base_term env t1);
      assert (is_base_term env t2);
      true
  | App(Const Not,t) -> is_base_term env t
  | App _ -> false
  | Let _ -> false
  | Fun _ -> false



let rec make_arg_let_term = function
  | Const c -> [], Const c
  | Var x -> [], Var x
  | App _ as t ->
      let t',ts = decomp_app t in
      let aux t (bind,ts) =
        let bind',t' = make_arg_let_term t in
        bind'@bind, t'::ts
      in
      let bind,ts' = List.fold_right aux ts ([],[]) in
      let xs = List.map (fun _ -> new_id "a") ts in
      let t'' = List.fold_left (fun t x -> App(t, Var x)) t' xs in
      bind @ List.combine xs ts', t''
  | Let _ -> assert false
  | Fun _ -> assert false
let make_arg_let_term t =
  let bind,t' = make_arg_let_term t in
  List.fold_right (fun (x,t) t' -> Let(x, t, t')) bind t'

let rec reduce_let env = function
  | Const c -> Const c
  | Var x -> Var x
  | App(t1,t2) -> App(reduce_let env t1, reduce_let env t2)
  | Fun _ -> assert false
  | Let(x,t1,t2) ->
      match t1,get_typ env t1 with
      | Var _, _
      | Const _, _
      | _, TFun _ -> reduce_let env (subst x t1 t2)
      | _, (TBase _ as typ) -> Let(x, reduce_let env t1, reduce_let ((x,typ)::env) t2)
      | _ -> assert false

let make_arg_let_def env (f,xs,t1,e,t2) =
    f, xs, t1, e, reduce_let (get_arg_env (List.assoc f env) xs @@@ env) (make_arg_let_term t2)

let make_arg_let prog =
  {prog with defs = List.map (make_arg_let_def prog.env) prog.defs}



let has_branch {defs} =
  let fs = List.sort compare @@ List.map (fun (f,_,_,_,_) -> f) defs in
  let rec aux fs =
    match fs with
    | [] -> []
    | [f] -> []
    | f::g::fs' when f = g -> f :: aux fs'
    | f::fs' -> aux fs'
  in
  List.unique @@ aux fs

let rec add_label prog =
  let merge = function
    | [] -> assert false
    | [f,xs,t1,e,t2] -> assert (t1 = Const True); [f, xs, t1, e, t2]
    | [f1,xs1,t11,e1,t12; f2,xs2,t21,e2,t22] when f1=f2 && xs1=xs2 && t11=make_not t21 ->
        [f1,xs1,t11,e1, make_label 1 t12; f2,xs2,t21,e2,make_label 0 t22]
    | [f1,xs1,t11,e1,t12; f2,xs2,t21,e2,t22] when f1=f2 && xs1=xs2 && make_not t11=t21 ->
        [f1,xs1,t11,e1,make_label 0 t12; f2,xs2,t21,e2,make_label 1 t22]
    | [f1,xs1,t11,e1,t12; f2,xs2,t21,e2,t22] as defs->
        Format.eprintf "%a@." CEGAR_print.prog {env=[]; defs; main=""; info=init_info};
        assert false
    | (f,_,_,_,_)::defs -> fatal @@ Format.sprintf "Not implemented (CEGAR_abst_util.add_label) %s %d" f (1 + List.length defs)
  in
  let rec aux = function
    | [] -> []
    | (f,xs,t1,e,t2)::defs ->
        let defs1,defs2 = List.partition (fun (g,_,_,_,_) -> f = g) defs in
        let defs' = merge ((f,xs,t1,e,t2)::defs1) in
        defs' @ aux defs2
  in
  let defs = aux prog.defs in
  let labeled = List.unique @@ List.rev_flatten_map (function (f,_,_,_,App(Const (Label _),_)) -> [f] | _ -> []) defs in
  assert (List.Set.eq labeled @@ has_branch prog);
  labeled, {prog with defs=defs}



let rec use_arg x typ t =
  match typ with
  | TBase _ -> t
  | TFun(typ1,typ2) ->
      let u = new_id "u" in
      let t' = make_br (Const Unit) (App(Var x, make_ext_fun typ1)) in
      App(Fun(u, None, t), t')
  | _ -> assert false

and make_ext_fun = function
  | TBase(TUnit, _) -> Const Unit
  | TBase(TBool, _) -> make_br (Const True) (Const False)
  | TFun(typ1,typ2) ->
      let x = new_id "x" in
      Fun(x, None, use_arg x typ1 (make_ext_fun (typ2 (Const Unit))))
  | _ -> assert false


let add_ext_funs prog =
  let env = get_ext_fun_env prog in
  let defs = List.map (fun (f,typ) -> f, [], Const True, [], make_ext_fun typ) env in
  let defs' = defs@prog.defs in
  ignore @@ Typing.infer {prog with env=[]; defs=defs'};
  {prog with defs=defs'}


let check_exist env cond x p =
  Debug.printf "check_exists:@.";
  Debug.printf "  cond: %a@." (List.print CEGAR_print.term) cond;
  Debug.printf "  \\exists r. %a@." CEGAR_print.term @@ subst x (Var "r") p;
  let xs = List.filter_out ((=) x) @@ (get_fv_list (p::cond)) in
  if !Flag.NonTermination.use_omega_first then
    try
      OmegaInterface.is_valid_forall_exists xs [x] cond p
      |@> Debug.printf "check_exists: %b@."
    with OmegaInterface.Unknown ->
      Debug.printf "check_exists: OmegaInterface.Unknown@.";
      Debug.printf "Try checking by z3...@.";
      try
        let b = FpatInterface.is_valid_forall_exists xs [x] cond p in
        Debug.printf "check_exists: %b@." b;
        ignore @@ read_line();
        b
      with Fpat.SMTProver.Unknown ->
        Debug.printf "check_exists: FpatInterface.Unknown@.";
        if Flag.Method.exists_unknown_false
        then false
        else raise Fpat.SMTProver.Unknown
  else
    try
      FpatInterface.is_valid_forall_exists xs [x] cond p
      |@> Debug.printf "check_exists: %b@."
    with
    | Fpat.SMTProver.Unknown when !Flag.NonTermination.use_omega ->
        Debug.printf "check_exists: Fpat.SMTProver.Unknown@.";
        Debug.printf "Try checking by omega...@.";
        begin
          try
            let b = OmegaInterface.is_valid_forall_exists xs [x] cond p in
            Debug.printf "check_exists: %b@." b;
            Debug.exec (fun _ -> ignore @@ read_line());
            b
          with OmegaInterface.Unknown ->
               Debug.printf "check_exists: OmegaInterface.Unknown@.";
               if Flag.Method.exists_unknown_false
               then false
               else raise Fpat.SMTProver.Unknown
        end
    | Fpat.SMTProver.Unknown when !Flag.NonTermination.use_omega ->
        Debug.printf "check_exists: Fpat.SMTProver.Unknown@.";
        if Flag.Method.exists_unknown_false
        then false
        else raise Fpat.SMTProver.Unknown
