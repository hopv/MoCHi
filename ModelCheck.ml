open Util
open Mochi_util
open CEGAR_syntax
open CEGAR_type
open CEGAR_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type filename = string
type node = UnitNode | BrNode | LineNode of int | EventNode of string
type counterexample =
  | CESafety of TrecsInterface.counterexample
  | CENonTerm of HorSatInterface.counterexample_apt
  | CEFairNonTerm of HORS_syntax.rules

type result = Safe of (var * Inter_type.t) list | Unsafe of counterexample

type mc_spec =
  | SpecTRecS of TrecsInterface.spec
  | SpecHorSat of HorSatInterface.spec

type spec =
  | Fairness of Fair_termination_type.fairness
  | Other

let make_file_spec () =
  [0, "unit", [];
   0, "event_newr", [1];
   1, "event_read", [1];
   1, "event_close", [4];
   0, "event_neww", [2];
   2, "event_write", [2];
   2, "event_close", [4];
   2, "event_newr", [3];
   1, "event_neww", [3];
   3, "unit", [];
   3, "event_read", [3];
   3, "event_write", [3];
   3, "event_close", [3];
   4, "unit", [];]




let capitalize_var = String.capitalize
let uncapitalize_var = String.uncapitalize
let uncapitalize_env env = List.map (Pair.map_fst uncapitalize_var) env

let capitalize {env;defs;main;info} =
  let env' = List.map (Pair.map_fst capitalize_var) env in
  let sbst1 = subst_map @@ List.map (fun (f,_) -> f, Var (capitalize_var f)) env in
  let aux (f,xs,t1,e,t2) =
    let xs' = List.map uncapitalize_var xs in
    let sbst2 = subst_map @@ List.map2 (fun x x' -> x, Var x') xs xs' in
    capitalize_var f,
    xs',
    sbst1 @@ sbst2 t1,
    e,
    sbst1 @@ sbst2 t2
  in
  let defs' = List.map aux defs in
  let main' = capitalize_var main in
  {env=env'; defs=defs'; main=main'; info}


let elim_non_det ({defs;main;info} as prog) =
  let env = get_ext_fun_env prog in
  let check f (g,_,_,_,_) = f = g in
  let mem f defs = List.exists (check f) defs in
  let rec elim_non_det_def = function
    | [] -> []
    | (f,xs,t1,e,t2)::defs when mem f defs ->
        let f' = rename_id f in
        let defs1,defs2 = List.partition (check f) defs in
        let defs1' = List.map (fun (f,xs,t1,e,t2) -> rename_id f,xs,t1,e,t2) defs1 in
        let t =
          let args = List.map (fun x -> Var x) xs in
          let app f = make_app (Var f) args in
          List.fold_left (fun t (g,_,_,_,_) -> make_br (app g) t) (app f') defs1'
        in
        (f,xs,Const True,[],t)::(f',xs,t1,e,t2)::defs1' @ elim_non_det_def defs2
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
  let aux_def (f,xs,t1,e,t2) =
    let f_typ = List.assoc f env in
    let env' = get_arg_env f_typ xs @@@ env in
    let rec aux_term t typ =
      match t,typ with
      | Const Bottom, typ -> make_bottom (get_arg_num typ)
      | Const c, _ -> Const c
      | Var x, _ -> Var x
      | App(App(App(Const If, t1), t2), t3), typ ->
          let t1' = aux_term t1 (TBase(TBool,fun _ -> [])) in
          let t2' =
            try
              aux_term t2 typ
            with TypeBottom -> make_bottom 0
          in
          let t3' =
            try
              aux_term t3 typ
            with TypeBottom -> make_bottom 0
          in
          App(App(App(Const If, t1'), t2'), t3')
      | App(Const (Label n), t), typ -> App(Const (Label n), aux_term t typ)
      | App(t1,t2), _ ->
          let typ = get_typ env' t1 in
          let typ' =
            match typ with
              TFun(typ,_) -> typ
            | _ -> assert false
          in
          App(aux_term t1 typ, aux_term t2 typ')
      | Let _, _ -> assert false
      | Fun _, _ -> assert false
    in
    let app_typ x = function
        TFun(_,typ2) -> typ2 (Var x)
      | _ -> assert false
    in
    let typ = List.fold_right app_typ xs f_typ in
    let t2' = aux_term t2 typ in
    f, xs, t1, e, t2'
  in
  let bot0 = make_bottom 0 in
  let make (x,n) = x, List.init n @@ Fun.const "x", Const True, [], bot0 in
  let defs' = List.map aux_def defs in
  let bottom_defs = List.map make (List.unique !bottoms) in
  {env; defs=bottom_defs@@@defs'; main; info}


let rec eta_expand_term env = function
    Const c -> Const c
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


let eta_expand_def env ((f,xs,t1,e,t2):fun_def) =
  let d = arg_num (List.assoc f env) - List.length xs in
  let ys = Array.to_list (Array.init d (fun _ -> new_id "x")) in
  let t2' = eta_expand_term (get_arg_env (List.assoc f env) xs @@@ env) t2 in
  let t2'' = List.fold_left (fun t x -> App(t, Var x)) t2' ys in
    f, xs@ys, t1, e, t2''

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
let church_encode {env;defs;main;info} =
  let true_def = true_var, ["x"; "y"], Const True, [], Var "x" in
  let false_def = false_var, ["x"; "y"], Const True, [], Var "y" in
  let defs' = List.map (map_body_def church_encode_term) defs @ [true_def; false_def] in
  let prog = {env=[];defs=defs';main;info} in
  if false then Format.printf "CHURCH ENCODE:\n%a@." CEGAR_print.prog prog;
  Typing.infer prog


let rec full_app f n = function
  | Const _ -> true
  | Var x when f = x -> false
  | Var x -> true
  | App _ as t ->
      let t1,ts = decomp_app t in
      let b1 = if t1 = Var f then n = List.length ts else true in
      let b2 = List.for_all (full_app f n) ts in
      b1 && b2
  | Let _ -> assert false
  | Fun _ -> assert false

let should_reduce (f,xs,t1,es,t2) env defs =
  let n = arg_num (List.assoc f env) in
    t1 = Const True && es = [] &&
    List.length (List.filter (fun (g,_,_,_,_) -> f=g) defs) = 1 &&
    List.length (List.rev_flatten_map (fun (_,_,_,_,t) -> List.filter ((=) f) (get_fv t)) defs) = 1 &&
    List.for_all (fun (_,_,_,_,t2) -> full_app f n t2) defs

let rec get_head_count f = function
  | Const _ -> 0
  | Var x -> 0
  | App _ as t ->
      let t1,ts = decomp_app t in
      let n = List.fold_left (fun n t -> n + get_head_count f t) 0 ts in
        if t1 = Var f
        then 1 + n
        else n
  | Let _ -> assert false
  | Fun _ -> assert false

let rec beta_reduce_term flag (f,xs,t1,es,t2) = function
  | Const c -> Const c
  | Var x -> Var x
  | App _ as t ->
      let t1,ts = decomp_app t in
      let ts' = List.map (beta_reduce_term flag (f,xs,t1,es,t2)) ts in
        if t1 = Var f
        then
          if List.for_all (function Const _ | Var _ -> true | App _ -> false | _ -> assert false) ts'
          then List.fold_right2 subst xs ts' t2
          else (flag := true; make_app t1 ts')
        else make_app t1 ts'
  | Let _ -> assert false
  | Fun _ -> assert false

let beta_reduce_term flag ((f,_,_,_,_) as def) t =
  let n = get_head_count f t in
    if n = 1
    then beta_reduce_term flag def t
    else (if n >= 2 then flag := true; t)

let beta_reduce_aux {env;defs;main;info} =
  let rec aux defs1 = function
      [] -> defs1
    | ((f,_,_,_,_) as def)::defs2 when should_reduce def env (defs1@@@def::defs2) ->
        let flag = ref false in
        let reduce_def (f',xs',t1',es',t2') = f', xs', t1', es', beta_reduce_term flag def t2' in
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
  Debug.printf "##[ModelCheck] %s:@.%a@.@." s CEGAR_print.prog_typ t;
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
  if !Flag.Print.progress
  then Color.printf Color.Green "(%d-2)[%.3f] Checking HORS ... @?" !Flag.Log.cegar_loop !!Time.get;
  set_status @@ Flag.Log.Other (Format.sprintf "(%d-2) Model checking" !Flag.Log.cegar_loop);
  let abst' =
    if List.mem ACPS prog.info.attr
    then preprocess_cps abst
    else preprocess abst
  in
  let result =
    match !Flag.ModelCheck.mc, !Flag.Method.mode with
    | Flag.ModelCheck.TRecS, _ ->
        let spec = TrecsInterface.make_spec @@ List.length prog.defs in
        begin
          match TrecsInterface.check (abst',spec) with
          | TrecsInterface.Safe env -> Safe (uncapitalize_env env)
          | TrecsInterface.Unsafe ce -> Unsafe (CESafety ce)
        end
    | Flag.ModelCheck.HorSat, Flag.Method.NonTermination ->
       let labels = List.map make_randint_label @@ List.filter_map (decomp_randint_name -| fst) prog.env in
       let spec = HorSatInterface.make_spec_nonterm labels in
        begin
          match HorSatInterface.check_apt (abst',spec) with
          | HorSatInterface.Safe env -> Safe (uncapitalize_env env)
          | HorSatInterface.UnsafeAPT ce -> Unsafe (CENonTerm ce)
          | HorSatInterface.Unsafe _ -> assert false
        end
    | Flag.ModelCheck.HorSat2, Flag.Method.NonTermination ->
       let labels = List.map make_randint_label @@ List.filter_map (decomp_randint_name -| fst) prog.env in
       let spec = HorSat2Interface.make_spec_nonterm labels in
        begin
          match HorSat2Interface.check_apt (abst',spec) with
          | HorSat2Interface.Safe env -> Safe (uncapitalize_env env)
          | HorSat2Interface.UnsafeAPT ce -> Unsafe (CENonTerm ce)
          | HorSat2Interface.Unsafe _ -> assert false
        end
    | Flag.ModelCheck.HorSat, _ ->
        let spec = HorSatInterface.make_spec @@ List.length prog.defs in
        begin
          match HorSatInterface.check (abst',spec) with
          | HorSatInterface.Safe env -> Safe (uncapitalize_env env)
          | HorSatInterface.Unsafe ce -> Unsafe (CESafety ce)
          | HorSatInterface.UnsafeAPT _ -> assert false
        end
    | Flag.ModelCheck.HorSat2, _ ->
        let spec = HorSat2Interface.make_spec @@ List.length prog.defs in
        begin
          match HorSat2Interface.check (abst',spec) with
          | HorSat2Interface.Safe env -> Safe (uncapitalize_env env)
          | HorSat2Interface.Unsafe ce -> Unsafe (CESafety ce)
          | HorSat2Interface.UnsafeAPT _ -> assert false
        end
    | Flag.ModelCheck.HorSatP, Flag.Method.FairNonTermination ->
       let fairness =
         match spec with
         | Fairness x -> x
         | Other -> assert false in
       Verbose.printf "\nFAIRNESS: %a@." Fair_termination_util.print_fairness fairness;
       let randint_labels = List.map make_randint_label @@ List.filter_map (decomp_randint_name -| fst) prog.env in
       let events = List.map (fun s -> "event_" ^ s) @@ gather_events prog.defs in
       let labels = events @ randint_labels in
       let spec = HorSatPInterface.make_fair_nonterm_spec labels fairness  in
        begin
          match HorSatPInterface.check (abst',spec) with
          | HorSatPInterface.Satisfied -> Safe []
          | HorSatPInterface.Unsatisfied ->
             let fname = Filename.change_extension !!Flag.Input.main "error_hors" in
             let rules = HorSatPInterface.read_HORS_file fname in
             Unsafe (CEFairNonTerm rules)
        end
    | Flag.ModelCheck.HorSatP, _ ->
       assert false
  in
  if !Flag.Print.progress then Color.printf Color.Green "DONE!@.@.";
  result
let check abst prog spec =
  Time.measure_and_add Flag.Log.Time.mc (check abst prog) spec
