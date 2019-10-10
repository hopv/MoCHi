open Util
open Mochi_util
open CEGAR_syntax
open CEGAR_type
open CEGAR_util

module MC = ModelCheck

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type result =
  | Safe of (var * CEGAR_ref_type.t) list
  | Unsafe of int list * MC.counterexample
  | Unknown of string

let pre () =
  ()

let post () =
  incr Flag.Log.cegar_loop;
  Fpat.Global.cegar_iterations := !Flag.Log.cegar_loop

let print_non_CPS_abst abst prog =
  if !Flag.Mode.just_print_non_CPS_abst then
    let result =
      try
        Some (MC.check abst prog MC.Other)
      with _ -> None
    in
    let s =
      match result with
      | None -> "Unknown"
      | Some (MC.Safe _) -> "Safe"
      | Some (MC.Unsafe _) -> "Unsafe"
    in
    Format.eprintf "@.ABST:@.%a@." CEGAR_print.prog abst;
    Format.eprintf "RESULT: %s@." s;
    exit 0

let improve_precision () =
  match () with
  | _ when not !Flag.PredAbst.use_filter ->
      Verbose.printf "Filter option enabled.@.";
      Verbose.printf "Restart CEGAR-loop.@.";
      Flag.PredAbst.use_filter := true
  | _ when not !Flag.PredAbst.never_use_neg_pred && not !Fpat.PredAbst.use_neg_pred ->
      Verbose.printf "Negative-predicate option enabled.@.";
      Verbose.printf "Restart CEGAR-loop.@.";
      Fpat.PredAbst.use_neg_pred := true
  | _ when !Fpat.PredAbst.wp_max_num < Flag.PredAbst.wp_max_max ->
      incr Fpat.PredAbst.wp_max_num;
      CEGAR_abst.incr_wp_max := true;
      Verbose.printf "Set wp_max_num to %d.@." !Fpat.PredAbst.wp_max_num;
      Verbose.printf "Restart CEGAR-loop.@.";
  | _ ->
      raise NoProgress

let rec loop preprocessed prog0 is_cp ces =
  pre ();
  let prog =
    if !Flag.Method.relative_complete
    then
      let env,defs,main = FpatInterface.instantiate_param prog0 in
      {env; defs; main; info=init_info}
    else prog0
  in
  let pr =
    if !Flag.PredAbst.expand_non_rec
    then CEGAR_util.print_prog_typ' prog.info.inlined
    else CEGAR_print.prog_typ
  in
  Verbose.printf "Program with abstraction types (CEGAR-cycle %d)::@.%a@." !Flag.Log.cegar_loop pr prog;
  if !Flag.Print.abst_typ
  then Format.printf "Abstraction types (CEGAR-cycle %d)::@.%a@." !Flag.Log.cegar_loop CEGAR_print.env prog.env;
  let labeled,preprocessed,abst = CEGAR_abst.abstract prog.info.inlined prog preprocessed in
  print_non_CPS_abst abst prog;
  let spec =
    match prog.info.CEGAR_syntax.fairness with
    | Some x -> MC.Fairness x
    | None -> MC.Other in
  let result = MC.check abst prog spec in
  match result, !Flag.Method.mode with
  | MC.Safe env, _ ->
      if !!Flag.Debug.print_ref_typ then
        begin
          Format.printf "Intersection types:@.";
          List.iter (fun (f,typ) -> Format.printf "  %s: %a@." f Inter_type.print typ) env;
          Format.printf "@."
        end;
      let env' =
        let aux (x,ityp) =
          try
            Some (x, Type_trans.ref_of_inter (List.assoc x prog.env) ityp)
          with Not_found -> None
        in
        if !Flag.Print.certificate && Flag.ModelCheck.(!mc <> TRecS) then
          match Ref.tmp_set Flag.ModelCheck.mc Flag.ModelCheck.TRecS (fun () -> MC.check abst prog spec) with
          | MC.Safe env -> List.filter_map aux env
          | _ -> assert false
        else
          List.filter_map aux env
      in
      if !!Flag.Debug.print_ref_typ then
        begin
          Format.printf "Refinement types:@.";
          List.iter (fun (f,typ) -> Format.printf "  %s: %a@." f CEGAR_ref_type.print typ) env';
          Format.printf "@."
        end;
      post ();
      prog, Safe env'
  | MC.Unsafe (MC.CENonTerm ce_tree), Flag.Method.NonTermination ->
      let prog' = CEGAR_non_term.cegar prog0 labeled is_cp ce_tree prog in
      post ();
      loop preprocessed prog' is_cp ((MC.CENonTerm ce_tree)::ces)
  | MC.Unsafe (MC.CEFairNonTerm ce_rules), Flag.Method.FairNonTermination ->
      begin
        let prog' = CEGAR_fair_non_term.cegar prog0 labeled is_cp ce_rules prog in
        post ();
        Fpat.PredAbst.use_neg_pred := true;
        let same_counterexample =
          match ces with
          | [] -> false
          | MC.CEFairNonTerm ce_pre :: _ -> ce_pre = ce_rules (*TODO*)
          | _ -> assert false
        in
        if same_counterexample then
          try
            improve_precision ();
            loop preprocessed prog is_cp ces
          with NoProgress ->
            post ();
            raise NoProgress
        else
          loop preprocessed prog' is_cp ((MC.CEFairNonTerm ce_rules)::ces)
      end
  | MC.Unsafe ce, _ ->
      let ce_orig =
        match ce with
        | MC.CESafety ce -> ce
        | _ -> assert false
      in
      if !Flag.Print.eval_abst then CEGAR_trans.eval_abst_cbn prog labeled abst ce_orig;
      let ce' = CEGAR_trans.trans_ce labeled prog ce_orig None in
      let same_counterexample =
        match ces with
        | [] -> false
        | MC.CESafety ce_pre :: _ -> ce' = CEGAR_trans.trans_ce labeled prog ce_pre None
        | _ -> assert false
      in
      if !Flag.Print.progress then Feasibility.print_ce_reduction ce' prog;
      if same_counterexample then
        try
          improve_precision ();
          loop preprocessed prog is_cp ces
        with NoProgress ->
          post ();
          raise NoProgress
      else
        begin
          match Feasibility.check ce' prog, !Flag.Method.mode with
          | Feasibility.Feasible sol, Flag.Method.Termination ->
              (* termination analysis *)
              Refine.refine_rank_fun ce' [] prog0;
              assert false
          | Feasibility.Feasible sol, Flag.Method.FairTermination ->
              Refine.refine_rank_fun ce' [] prog0;
              assert false
          | Feasibility.Feasible sol, _ ->
              prog, Unsafe(sol, ce)
          | Feasibility.FeasibleNonTerm _, _ ->
              assert false
          | Feasibility.Infeasible prefix, _ ->
              let ces' = ce::ces in
              let inlined_functions = inlined_functions prog0 in
              let aux ce =
                match ce with
                | MC.CESafety ce' -> CEGAR_trans.trans_ce labeled prog ce' None
                | _ -> assert false
              in
              let _,prog' =
                let ces'' = List.map aux ces' in
                let ext_ces = List.map (Fun.const []) ces'' in
                Refine.refine inlined_functions is_cp prefix ces'' ext_ces prog0
              in
              Verbose.printf "Prefix of spurious counterexample::@.%a@.@." CEGAR_print.ce prefix;
              post ();
              loop preprocessed prog' is_cp ces'
        end


let run prog =
  if !!Debug.check then ignore @@ Typing.infer prog;
  let prog =
    match !Flag.Method.mode with
    | Flag.Method.NonTermination
    | Flag.Method.FairNonTermination -> CEGAR_trans.add_fail_to_end prog
    | _ -> prog
  in
  make_ID_map prog;
  let info =
    if !Flag.PredAbst.expand_non_rec then
      {prog.info with non_rec = get_non_rec CEGAR_abst_CPS.beta_reduce_term @@ snd @@ CEGAR_abst_util.add_label prog}
    else
      prog.info
  in
  try
    let is_cp = FpatInterface.is_cp prog in
    try
      snd @@ loop None {prog with info} is_cp []
    with Fpat.RefTypInfer.FailedToRefineTypes when !Flag.PrettyPrinter.web ->
      FpatInterface.parse_arg "-hccs it";
      snd @@ loop None {prog with info} is_cp []
  with NoProgress | CEGAR_abst.NotRefined ->
    post ();
    raise NoProgress
