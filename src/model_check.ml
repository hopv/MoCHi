open Util
open Mochi_util
open CEGAR_syntax
open CEGAR_type
open CEGAR_util

include Model_check_common

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type mc =
  | TRecS
  | HorSat
  | HorSat2
  | HorSatP
  [@@deriving show]

let current_mc : mc option ref = ref None
let mc_safety = ref (module MC_dummy : MC_safety_interface)
let mc_nontermination = ref (module MC_dummy : MC_nontermination_interface)
let mc_fair_nontermination = ref (module MC_dummy : MC_fair_nontermination_interface)

let available mc =
  let path =
    let open Flag.ModelCheck in
    match mc with
    | TRecS -> !trecs
    | HorSat -> !horsat
    | HorSat2 -> !horsat2
    | HorSatP -> !horsatp
  in
  path <> None

let use mc =
  if not (available mc) then failwith "%s is not available" (show_mc mc);
  current_mc := Some mc;
  match mc with
  | TRecS ->
      mc_safety := (module TrecsInterface : MC_safety_interface)
  | HorSat ->
      mc_safety := (module HorSatInterface : MC_safety_interface);
      mc_nontermination := (module HorSatInterface : MC_nontermination_interface)
  | HorSat2 ->
      mc_safety := (module HorSat2Interface : MC_safety_interface);
      mc_nontermination := (module HorSat2Interface : MC_nontermination_interface)
  | HorSatP ->
      mc_fair_nontermination := (module HorSatPInterface : MC_fair_nontermination_interface)

let init () =
  if available HorSat2 then
    use HorSat2
  else if available HorSat then
    use HorSat
  else
    use TRecS

let capitalize_var = String.capitalize
let uncapitalize_var = String.uncapitalize
let uncapitalize_env env = List.map (Pair.map_fst uncapitalize_var) env

let capitalize {env; defs; main; info} =
  let env' = List.map (Pair.map_fst capitalize_var) env in
  let sbst1 = subst_map @@ List.map (fun (f,_) -> f, Var (capitalize_var f)) env in
  let aux {fn=f; args=xs; cond; body} =
    let xs' = List.map uncapitalize_var xs in
    let sbst2 = subst_map @@ List.map2 (fun x x' -> x, Var x') xs xs' in
    {fn = capitalize_var f;
     args = xs';
     cond = sbst1 @@ sbst2 cond;
     body = sbst1 @@ sbst2 body}
  in
  let defs' = List.map aux defs in
  let main' = capitalize_var main in
  {env=env'; defs=defs'; main=main'; info}

let elim_non_det ({defs;main;info} as prog) =
  let env = get_ext_fun_env prog in
  let check f {fn=g} = f = g in
  let mem f defs = List.exists (check f) defs in
  let rec elim_non_det_def = function
    | [] -> []
    | {fn=f; args=xs; cond=t1; body=t2}::defs when mem f defs ->
        let f' = rename_id f in
        let defs1,defs2 = List.partition (check f) defs in
        let defs1' = List.map (fun def -> {def with fn = rename_id def.fn}) defs1 in
        let t =
          let args = List.map (fun x -> Var x) xs in
          let app f = make_app (Var f) args in
          List.fold_left (fun t {fn=g} -> make_br (app g) t) (app f') defs1'
        in
        {fn=f; args=xs; cond=Const True; body=t}
        :: {fn=f'; args=xs; cond=t1; body=t2}
        :: defs1'
        @ elim_non_det_def defs2
    | def::defs -> def :: elim_non_det_def defs
  in
  Typing.infer {env; defs=elim_non_det_def defs; main; info}

let make_bottom {env;defs;main;info} =
  let bottoms = ref [] in
  let make_bottom n =
    let x = "Bottom" ^ string_of_int n in
    bottoms := (x,n)::!bottoms;
    Var x
  in
  let aux_def {fn=f; args=xs; cond; body=t2} =
    let f_typ = List.assoc f env in
    let env' = get_arg_env f_typ xs @@@ env in
    let rec aux_term t typ =
      match t,typ with
      | Const Bottom, typ -> make_bottom (get_arg_num typ)
      | Const c, _ -> Const c
      | Var x, _ -> Var x
      | App(App(App(Const If, t1), t2), t3), typ ->
          let t1' = aux_term t1 (TBase(TBool,fun _ -> [])) in
          let aux_term' t typ =
            try
              aux_term t typ
            with TypeBottom -> make_bottom 0
          in
          let t2' = aux_term' t2 typ in
          let t3' = aux_term' t3 typ in
          App(App(App(Const If, t1'), t2'), t3')
      | App(Const (Label n), t), typ -> App(Const (Label n), aux_term t typ)
      | App(t1,t2), _ ->
          let typ = get_typ env' t1 in
          let typ' =
            match typ with
            | TFun(typ,_) -> typ
            | _ -> assert false
          in
          App(aux_term t1 typ, aux_term t2 typ')
      | Let _, _ -> assert false
      | Fun _, _ -> assert false
    in
    let app_typ x = function
      | TFun(_,typ2) -> typ2 (Var x)
      | _ -> assert false
    in
    let typ = List.fold_right app_typ xs f_typ in
    let t2' = aux_term t2 typ in
    {fn=f; args=xs; cond; body=t2'}
  in
  let bot0 = make_bottom 0 in
  let defs' = List.map aux_def defs in
  let bottom_defs =
    let make (x,n) = {fn=x; args=List.init n @@ Fun.const "x"; cond=Const True; body=bot0} in
    List.map make (List.unique !bottoms)
  in
  {env; defs=bottom_defs@@@defs'; main; info}


let rec eta_expand_term env = function
  | Const c -> Const c
  | Var x -> Var x
  | App(App(App(Const If, Const (Rand(TBool,_))), t2), t3) ->
      let typ = get_typ env t2 in
      let xs = Array.to_list (Array.init (arg_num typ) (fun _ -> new_id "x")) in
      let aux t = List.fold_left (fun t x -> App(t, Var x)) (eta_expand_term env t) xs in
      let t = make_if (Const (Rand(TBool,None))) (aux t2) (aux t3) in
        List.fold_right (fun x t -> Fun(x,None,t)) xs t
  | App(t1, t2) -> App(eta_expand_term env t1, eta_expand_term env t2)
  | Fun _ -> assert false
  | Let _ -> assert false


let eta_expand_def env ({fn=f; args=xs; body=t2} as def) =
  let d = arg_num (List.assoc f env) - List.length xs in
  let ys = Array.to_list (Array.init d (fun _ -> new_id "x")) in
  let t2' = eta_expand_term (get_arg_env (List.assoc f env) xs @@@ env) t2 in
  let body = List.fold_left (fun t x -> App(t, Var x)) t2' ys in
  {def with args=xs@ys; body}

let eta_expand prog =
  {prog with defs = List.map (eta_expand_def prog.env) prog.defs}
  |> CEGAR_lift.lift2

let trans_ce ce =
  let aux (s,_) =
    match s with
    | "unit" -> []
    | "br" -> []
    | s when s.[0] = 'l' -> [int_of_string @@ String.slice ~first:1 s]
    | s when String.starts_with s "event_" -> []
    | _ -> assert false
  in
  List.flatten_map aux ce


let true_var = "True"
let false_var = "False"
let rec church_encode_term = function
  | Const True -> Var true_var
  | Const False -> Var false_var
  | Const If -> assert false
  | Const c -> Const c
  | Var x -> Var x
  | App(App(App(Const If, Const (Rand(TBool,_))), t2), t3) ->
      let t2' = church_encode_term t2 in
      let t3' = church_encode_term t3 in
      make_app (Const If) [Const (Rand(TBool,None)); t2'; t3']
  | App(App(App(Const If, Var b), t2), t3) ->
      let t2' = church_encode_term t2 in
      let t3' = church_encode_term t3 in
      make_app (Var b) [t2'; t3']
  | App(t1, t2) -> App(church_encode_term t1, church_encode_term t2)
  | Let _ -> assert false
  | Fun _ -> assert false
let church_encode {defs;main;info} =
  let args = ["x"; "y"] in
  let cond = Const True in
  let true_def = {fn=true_var; args; cond=Const True; body=Var "x"} in
  let false_def = {fn=false_var; args; cond; body=Var "y"} in
  let defs' = List.map (map_body_def church_encode_term) defs @ [true_def; false_def] in
  let prog = {env=[];defs=defs';main;info} in
  if false then Format.fprintf !Flag.Print.target "CHURCH ENCODE:\n%a@." CEGAR_print.prog prog;
  Typing.infer prog


let rec full_app f n = function
  | Const _ -> true
  | Var x when f = x -> false
  | Var _ -> true
  | App _ as t ->
      let t1,ts = decomp_app t in
      let b1 = if t1 = Var f then n = List.length ts else true in
      let b2 = List.for_all (full_app f n) ts in
      b1 && b2
  | Let _ -> assert false
  | Fun _ -> assert false

let should_reduce {fn=f; cond} env defs =
  let n = arg_num (List.assoc f env) in
  cond = Const True &&
  List.count (fun {fn} -> f = fn) defs = 1 &&
  List.length (List.rev_flatten_map (fun {body} -> List.filter ((=) f) (get_fv body)) defs) = 1 &&
  List.for_all (fun def -> full_app f n def.body) defs

let rec get_head_count f = function
  | Const _ -> 0
  | Var _ -> 0
  | App _ as t ->
      let t1,ts = decomp_app t in
      let n = List.fold_left (fun n t -> n + get_head_count f t) 0 ts in
        if t1 = Var f
        then 1 + n
        else n
  | Let _ -> assert false
  | Fun _ -> assert false

let rec beta_reduce_term flag ({fn=f; args=xs; body=t2} as def) = function
  | Const c -> Const c
  | Var x -> Var x
  | App _ as t ->
      let t1,ts = decomp_app t in
      let ts' = List.map (beta_reduce_term flag def) ts in
      if t1 = Var f then
        if List.for_all (function Const _ | Var _ -> true | App _ -> false | _ -> assert false) ts'
        then List.fold_right2 subst xs ts' t2
        else (flag := true; make_app t1 ts')
      else
        make_app t1 ts'
  | Let _ -> assert false
  | Fun _ -> assert false

let beta_reduce_term flag ({fn=f} as def) t =
  let n = get_head_count f t in
  if n = 1
  then beta_reduce_term flag def t
  else (if n >= 2 then flag := true; t)

let beta_reduce_aux {env;defs;main;info} =
  let rec aux defs1 = function
      [] -> defs1
    | def::defs2 when should_reduce def env (defs1@@@def::defs2) ->
        let flag = ref false in
        let reduce_def def' = {def' with body = beta_reduce_term flag def def'.body} in
        let defs1' = List.map reduce_def defs1 in
        let defs2' = List.map reduce_def defs2 in
          if !flag
          then aux (defs1'@[def]) defs2'
          else aux defs1' defs2'
    | def::defs2 -> aux (defs1@[def]) defs2
  in
  {env; defs = aux [] defs; main; info}

let rec beta_reduce prog =
  let prog' = beta_reduce_aux prog in
    if prog.defs = prog'.defs
    then prog
    else beta_reduce prog'

let pr s t =
  Dbg.printf "##[ModelCheck] %s:@.%a@.@." s CEGAR_print.prog_typ t;
  ignore @@ Typing.infer t

let preprocess prog =
  Format.eprintf "WARNING: model checking for non-CPS programs is unmaintained.@.";
  prog
  |@> pr "INPUT"
  |> CEGAR_CPS.trans -$- true
  |@> pr "CPS"
  |> eta_expand
  |@> pr "eta_expand"
  |> elim_non_det
  |@> pr "elim_non_det"
  |> make_bottom
  |@> pr "make_bottom"
  |> pop_main
  |@> pr "pop_main"
  |> capitalize
  |@> pr "capitalize"
  |> Typing.infer
  |&Flag.ModelCheck.useless_elim&> Useless_elim.elim
  |&Flag.ModelCheck.beta_reduce&> beta_reduce
  |& !Flag.ModelCheck.church_encode&> church_encode
  |@> pr "church_encode"

let preprocess_cps prog =
  prog
  |@> pr "INPUT"
  |> eta_expand
  |@> pr "eta_expand"
  |> elim_non_det
  |@> pr "elim_non_det"
  |> put_arg_into_if
  |@> pr "put_arg_into_if"
  |> make_bottom
  |@> pr "make_bottom"
  |> pop_main
  |@> pr "pop_main"
  |> capitalize
  |@> pr "capitalize"
  |> Typing.infer
  |&Flag.ModelCheck.useless_elim&> Useless_elim.elim
  |&Flag.ModelCheck.beta_reduce&> beta_reduce
  |& !Flag.ModelCheck.church_encode&> church_encode
  |@> pr "church_encode"

let check abst prog spec =
  let module MC_safety = (val (!mc_safety) : MC_safety_interface) in
  let module MC_nontermination = (val (!mc_nontermination) : MC_nontermination_interface) in
  let module MC_fair_nontermination = (val (!mc_fair_nontermination) : MC_fair_nontermination_interface) in
  Verbose.printf ~color:Green "(%d-2)[%.3f] Checking HORS ... @?" !Flag.Log.cegar_loop !!Time.get;
  set_status @@ Flag.Log.Other (Format.sprintf "(%d-2) Model checking" !Flag.Log.cegar_loop);
  let abst' =
    if List.mem ACPS prog.info.attr
    then preprocess_cps abst
    else preprocess abst
  in
  let result =
    match spec with
    | Safety ->
        let spec = MC_safety.make_spec_safety (max_label abst) in
        let r =
          match MC_safety.check_safety (abst',spec) with
          | SSafe env -> SSafe (uncapitalize_env env)
          | SUnsafe ce -> SUnsafe ce
        in
        RSafety r
    | NonTermination ->
       let labels = List.map make_randint_label @@ List.filter_map (decomp_randint_name -| fst) prog.env in
       let spec = MC_nontermination.make_spec_nontermination labels in
        let r =
          match MC_nontermination.check_nontermination (abst',spec) with
          | NTSafe env -> NTSafe (uncapitalize_env env)
          | NTUnsafe ce -> NTUnsafe ce
        in
        RNonTermination r
    | FairNonTermination fairness ->
        Verbose.printf "@\nFAIRNESS: %a@." Fair_termination_util.print_fairness fairness;
        let randint_labels = List.map make_randint_label @@ List.filter_map (decomp_randint_name -| fst) prog.env in
        let events = List.map (fun s -> "event_" ^ s) @@ col_events prog in
        let labels = events @ randint_labels in
        let spec = MC_fair_nontermination.make_spec_fair_nontermination labels fairness  in
        let r =
          match MC_fair_nontermination.check_fair_nontermination (abst',spec) with
          | FNTSafe env -> FNTSafe (uncapitalize_env env)
          | FNTUnsafe rules -> FNTUnsafe rules
        in
        RFairNonTermination r
  in
  Verbose.printf ~color:Green "DONE!@.@.";
  result
let check abst prog spec =
  Time.measure_and_add Flag.Log.Time.mc (check abst prog) spec
