open Util
open Mochi_util
open CEGAR_syntax
open CEGAR_type
open CEGAR_util

module MC = Model_check

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

let rec loop ?preprocessed prog0 is_cp ces =
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
    then CEGAR_util.print_prog_typ'
    else CEGAR_print.prog_typ
  in
  Verbose.printf "Program with abstraction types (CEGAR-cycle %d)::@.%a@." !Flag.Log.cegar_loop pr prog;
  if !Flag.Print.abst_typ
  then Format.fprintf !Flag.Print.target "Abstraction types (CEGAR-cycle %d)::@.%a@." !Flag.Log.cegar_loop CEGAR_print.env prog.env;
  let labeled,preprocessed,abst = CEGAR_abst.abstract prog.info.inlined ?preprocessed prog in
  let spec =
    match !Flag.mode, prog.info.CEGAR_syntax.fairness with
    | FairNonTermination, Some x -> MC.FairNonTermination x
    | FairNonTermination, None -> assert false
    | NonTermination, _ -> NonTermination
    | _ -> Safety
  in
  match MC.check abst prog spec with
  | RSafety (SSafe env)
  | RNonTermination (NTSafe env)
  | RFairNonTermination (FNTSafe env) ->
      if !!Flag.Debug.print_ref_typ then
        begin
          Format.fprintf !Flag.Print.target "Intersection types:@.";
          List.iter (fun (f,typ) -> Format.fprintf !Flag.Print.target "  %s: %a@." f Inter_type.print typ) env;
          Format.fprintf !Flag.Print.target "@."
        end;
      let env' =
        let aux (x,ityp) =
          try
            Some (x, Type_trans.ref_of_inter (List.assoc x prog.env) ityp)
          with Not_found -> None
        in
        if !Flag.Print.certificate && !Flag.mode <> NonTermination && !Flag.mode <> FairNonTermination then
          match MC.use TRecS; MC.check abst prog spec with
          | RSafety (SSafe env) -> List.filter_map aux env
          | _ -> assert false
        else
          List.filter_map aux env
      in
      if !!Flag.Debug.print_ref_typ then
        begin
          Format.fprintf !Flag.Print.target "Refinement types:@.";
          List.iter (fun (f,typ) -> Format.fprintf !Flag.Print.target "  %s: %a@." f CEGAR_ref_type.print typ) env';
          Format.fprintf !Flag.Print.target "@."
        end;
      post ();
      prog, Safe env'
  | RNonTermination (NTUnsafe ce_tree) ->
      let prog' = CEGAR_non_term.cegar prog0 labeled is_cp ce_tree prog in
      post ();
      loop ~preprocessed prog' is_cp ((MC.CENonTerm ce_tree)::ces)
  | RFairNonTermination (FNTUnsafe ce_rules) ->
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
            loop ~preprocessed prog is_cp ces
          with NoProgress ->
            post ();
            raise NoProgress
        else
          loop ~preprocessed prog' is_cp ((MC.CEFairNonTerm ce_rules)::ces)
      end
  | RSafety (SUnsafe ce) ->
      let ce_orig = ce in
      if !Flag.Print.eval_abst then CEGAR_trans.eval_abst_cbn prog labeled abst ce_orig;
      let ce' = CEGAR_trans.trans_ce labeled prog ce_orig None in
      let same_counterexample =
        if !Flag.Debug.input_cex then
          false
        else
          match ces with
          | [] -> false
          | MC.CESafety ce_pre :: _ -> ce' = CEGAR_trans.trans_ce labeled prog ce_pre None
          | _ -> assert false
      in
      if !Flag.Print.progress then Feasibility.print_ce_reduction ce' prog;
      if same_counterexample then
        try
          improve_precision ();
          loop ~preprocessed prog is_cp ces
        with NoProgress ->
          post ();
          raise NoProgress
      else
        match Feasibility.check ce' prog, !Flag.mode with
        | Feasibility.Feasible _sol, Flag.Termination ->
            (* termination analysis *)
            Refine.refine_rank_fun ce' [] prog0;
            assert false
        | Feasibility.Feasible _sol, Flag.FairTermination ->
            Refine.refine_rank_fun ce' [] prog0;
            assert false
        | Feasibility.Feasible sol, _ ->
            prog, Unsafe(sol, CESafety ce)
        | Feasibility.FeasibleNonTerm _, _ ->
            assert false
        | Feasibility.Infeasible prefix, _ ->
            let ces' = MC.CESafety ce::ces in
            let inlined_functions = inlined_functions prog0 in
            let aux ce =
              match ce with
              | MC.CESafety ce' -> CEGAR_trans.trans_ce labeled prog ce' None
              | _ -> assert false
            in
            let _,prog' =
              let ces'' =
                if !Flag.Debug.input_cex then
                  [ce']
                else
                  List.map aux ces'
              in
              let ext_ces = List.map (Fun.const []) ces'' in
              Refine.refine inlined_functions is_cp prefix ces'' ext_ces prog0
            in
            Verbose.printf "Prefix of spurious counterexample::@.%a@.@." CEGAR_print.ce prefix;
            post ();
            loop ~preprocessed prog' is_cp ces'


let run prog =
  if !!Debug.check then ignore @@ Typing.infer prog;
  let prog =
    match !Flag.mode with
    | Flag.NonTermination
    | Flag.FairNonTermination -> CEGAR_trans.add_fail_to_end prog
    | _ -> prog
  in
  make_ID_map prog;
  let info =
    if !Flag.PredAbst.expand_non_rec then
      let non_rec =
        CEGAR_abst_util.add_label prog
        |> snd
        |> get_non_rec CEGAR_abst_CPS.beta_reduce_term
      in
      {prog.info with non_rec}
    else
      prog.info
  in
  try
    let is_cp = FpatInterface.is_cp prog in
    let run () = snd @@ loop {prog with info} is_cp [] in
    try
      run ()
    with Fpat.RefTypInfer.FailedToRefineTypes when !Flag.PrettyPrinter.web ->
      FpatInterface.parse_arg "-hccs it";
      run ()
  with NoProgress | CEGAR_abst.NotRefined ->
    post ();
    raise NoProgress
