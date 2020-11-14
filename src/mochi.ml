open Util
open Mochi_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let print_info_default () =
  if !Flag.Termination.add_closure_exparam && Flag.Log.(!result = Terminating) then
    Format.printf "exparam inserted program:@. %a@." Print.(term_custom {!config_default with unused=true}) !ExtraParamInfer.origWithExparam;
  if Flag.(!mode = Termination) && Flag.Log.(!result = Terminating) then
    begin
      List.iter
        (fun (f_name, (cycles, pred)) ->
         Format.printf "ranking function(%s)[inference cycle: %d]: %a\n" f_name cycles BRA_types.pr_ranking_function pred;
         if !Flag.Termination.add_closure_exparam then
           let str_exparam = ExtraParamInfer.to_string_CoeffInfos pred.BRA_types.coeffsMap in
           if str_exparam <> "" then Format.printf "exparam(%s):\n%s\n" f_name str_exparam)
        !Termination_loop.lrf
    end;
  if Flag.(!mode = FairTermination) then
    Format.printf "cycles: %d@." !Flag.FairTermination.loop_count;
  Format.printf "CEGAR-cycles: %d@." !Flag.Log.cegar_loop;
  Format.printf "total: %.3f sec@." !!Time.get;
  (*  Format.printf "  pre: %.3f sec@." !Flag.Log.Time.preprocess;*)
  Format.printf "  abst: %.3f sec@." !Flag.Log.Time.abstraction;
  Format.printf "  mc: %.3f sec@." !Flag.Log.Time.mc;
  if Flag.Experiment.HORS_quickcheck.(!use <> None) then
    Format.printf "    hors_quickcheck: %.3f sec@." !Flag.Log.Time.hors_quickcheck;
  Format.printf "  refine: %.3f sec@." !Flag.Log.Time.cegar;
  if !Flag.Method.relative_complete then
    Format.printf "    exparam: %.3f sec@." !Flag.Log.Time.parameter_inference;
  Format.pp_print_flush Format.std_formatter ()

let output_json () =
  let filename = Filename.change_extension !!Flag.Input.main "json" in
  let assoc =
    ["filename", `String !!Flag.Input.main;
     "result", `String (Flag.Log.string_of_result false);
     "cycles", `Int !Flag.Log.cegar_loop;
     "total", `Float !!Time.get;
     (*     "pre", `Float !Flag.Log.Time.preprocess;*)
     "abst", `Float !Flag.Log.Time.abstraction;
     "mc", `Float !Flag.Log.Time.mc;
     "refine", `Float !Flag.Log.Time.cegar]
    @
      (if Flag.(!mode = Termination) then
         let json_of_lrf (f_name, (cycles, pred)) =
           let rank_fun = Format.asprintf "%a" BRA_types.pr_ranking_function pred in
           f_name, `Assoc ["function", `String rank_fun; "inferCycles", `Int cycles]
         in
         ["ranking", `Assoc (List.map json_of_lrf !Termination_loop.lrf)]
       else
         [])
    @
      (if Flag.Experiment.HORS_quickcheck.(!use <> None) then
         ["hors_quickcheck", `Float !Flag.Log.Time.hors_quickcheck;
          "cex_length", `String (List.to_string ~delimiter:"," string_of_int !Flag.Experiment.HORS_quickcheck.cex_length_history)]
       else
         [])
    @
      (if !Flag.Method.relative_complete then
         ["exparam", `Float !Flag.Log.Time.parameter_inference]
       else
         [])
    @
      (if !Flag.Method.modular then
         ["#typeChecker", `Int !Modular.num_tycheck;
          "typeChecker", `Float !Modular.time_check;
          "typeSynthesizer", `Float !Modular.time_synthesize]
       else
         [])
  in
  JSON.to_file filename (`Assoc assoc)

let print_info_modular () =
  Format.printf "#typeChecker: %d@." !Modular.num_tycheck;
  Format.printf "total: %.3f sec@." !!Time.get;
  Format.printf "  typeChecker: %.3f sec@." !Modular.time_check;
  Format.printf "  typeSynthesizer: %.3f sec@." !Modular.time_synthesize

let print_info () =
  output_json ();
  if !Flag.Print.result then
    if !Flag.Method.modular then
      print_info_modular ()
    else
      print_info_default ()

let main_input_cegar filename =
  let open CEGAR_syntax in
  IO.CPS.open_in filename (fun cin ->
    let lb = Lexing.from_channel cin in
    lb.Lexing.lex_curr_p <-
      {Lexing.pos_fname = Filename.basename filename;
       Lexing.pos_lnum = 1;
       Lexing.pos_cnum = 0;
       Lexing.pos_bol = 0};
    let prog = CEGAR_parser.prog CEGAR_lexer.token lb in
    let prog' = Typing.infer {prog with env=[]} in
    let env = List.filter_out (fun (f,_) -> List.mem_assoc f prog.env) prog'.env @ prog.env in
    Main_loop.run_cegar {prog with env})

let main_termination parsed =
  let parsed = BRA_transform.lambda_lift (BRA_transform.remove_unit_wraping parsed) in
  let _ = Verbose.printf "lambda-lifted::@. @[%a@.@." Print.term parsed in
  let parsed = BRA_transform.regularization parsed in
  let _ = Verbose.printf "regularized::@. @[%a@.@." Print.term parsed in
  let parsed = if !Flag.Termination.add_closure_depth then ExtraClsDepth.addExtraClsDepth parsed else parsed in
  let _ = if !Flag.Termination.add_closure_depth then Verbose.printf "closure depth inserted::@. @[%a@.@." Print.term parsed in
  let parsed = if !Flag.Termination.add_closure_exparam then ExtraParamInfer.addTemplate parsed else parsed in
  let _ = if !Flag.Termination.add_closure_exparam then Verbose.printf "closure exparam inserted::@. @[%a@.@." Print.term parsed in
  let holed_list = BRA_transform.to_holed_programs parsed in
  let coeffs = List.filter Id.is_coefficient @@ Term_util.get_fv parsed in
  let result =
    try
      List.for_all
        (fun holed ->
         let init_predicate_info =
           { BRA_types.variables = List.map BRA_transform.extract_id (BRA_state.get_argvars holed.BRA_types.state holed.BRA_types.verified)
           ; BRA_types.coeffsMap = if !Flag.Termination.add_closure_exparam then List.map (Pair.add_right @@ Fun.const 0) coeffs else []
           ; BRA_types.prev_variables = List.map BRA_transform.extract_id (BRA_state.get_prev_statevars holed.BRA_types.state holed.BRA_types.verified)
           ; BRA_types.coefficients = []
           ; BRA_types.errorPaths = []
           ; BRA_types.errorPathsWithExparam = [] } in
         let predicate_que = Queue.create () in
         let _ = Queue.add (fun _ -> init_predicate_info) predicate_que in
         Termination_loop.reset_cycle ();
         Termination_loop.run predicate_que holed) holed_list
    with
    | Fpat.PolyConstrSolver.NoSolution
    | Termination_loop.FailedToFindLLRF -> false
  in
  if result then
    begin
      set_status Flag.Log.Terminating;
      if !Flag.Print.result then Format.printf "Terminating!@."
    end
  else
   begin
      set_status @@ Flag.Log.Unknown "";
     if !Flag.Print.result then Format.printf "Unknown...@."
   end;
  result

let main_fair_termination spec parsed =
  let result = Fair_termination.run spec parsed in
  if result
  then Format.printf "Fair terminating!@.@."
  else Format.printf "Unknown...@.@.";
  result

let output_randint_refinement_log input_string =
  let cout =
    let input =
      let dirname = Filename.dirname !!Flag.Input.main in
      let basename = Filename.basename !!Flag.Input.main in
      dirname ^ "/refinement/" ^ Filename.change_extension basename "refinement"
    in
    open_out_gen [Open_wronly; Open_trunc; Open_text; Open_creat] 0o644 input
  in
  output_string cout ("[INPUT]:\n" ^ input_string ^ "\n");
  close_out cout

let main_quick_check t =
  t
  |> Preprocess.(run_on_term (before CPS !!all))
  |> Quick_check.repeat_forever

let main_trans t =
  let pps_all = !!Preprocess.all in
  let print_as_ml pps =
       Preprocess.run_on_term pps
    |- Trans.remove_unambiguous_id
    |- Trans.replace_typ_result_with_unit
    |- Trans.rename_for_ocaml
    |- Format.printf "%a@." Print.as_ocaml_typ
  in
  begin
    match !Flag.Trans.destination with
    | Flag.Trans.Before_CPS -> print_as_ml Preprocess.(before CPS pps_all) t
    | Flag.Trans.CPS -> print_as_ml Preprocess.(before_and Remove_pair pps_all) t
    | Flag.Trans.CHC ->
        Flag.PredAbst.shift_pred := true;
        let t' =
          t
          |> Preprocess.(run_on_term (before_and CPS pps_all))
          |> Trans.alpha_rename ~whole:true
        in
        let ty = Ref_type.of_simple t'.Syntax.typ in
        let env = Ref_type.Env.empty in
        try
          Ref_type_check.print stdout env t' ty
        with e when !Flag.Debug.debug_module = [] ->
          Format.eprintf "%s@." (Printexc.to_string e);
          Format.printf ")@.(get-proof)@."; (* for hoice *)
          exit 1
  end;
  exit 0

let make_temp_file () =
  let dir = "/tmp/mochi" in
  let template = Format.asprintf "%s/%a_XXXXXXXX.ml" dir Time.print_simple !!Unix.time in
  (try Unix.mkdir dir 0o755 with Unix.Unix_error(Unix.EEXIST, _, _) -> ());
  Unix.CPS.open_process_in ("mktemp " ^ template) input_line
  |@> Verbose.printf "Temporary file \"%s\" is created@.@."

let copy_input_file file =
  let temp_file = !!make_temp_file in
  IO.copy_file ~src:file ~dest:temp_file;
  temp_file

let save_input_to_file filenames =
  match filenames with
  | []
  | ["-"] ->
      let filename = if !Flag.use_temp then !!make_temp_file else "stdin.ml" in
      Flag.Input.filenames := [filename];
      IO.output_file ~filename ~text:(IO.input_all stdin)
  | _ ->
      if !Flag.use_temp then
        filenames
        |> List.map copy_input_file
        |> Ref.set Flag.Input.filenames

(* called before parsing options *)
let fpat_init1 () =
  Fpat.FPATConfig.set_default ()

(* called after parsing options *)
let fpat_init2 () =
  let open Fpat in
  Global.target_filename := !!Flag.Input.main;
  SMTProver.cvc3_command := !Flag.External.cvc3;
  SMTProver.initialize ()

let check_env () =
  begin
    match !Flag.ModelCheck.mc with
    | Flag.ModelCheck.TRecS -> if not Mconfig.trecs_available then fatal "TRecS not found"
    | Flag.ModelCheck.HorSat -> if not Mconfig.horsat_available then fatal "HorSat not found"
    | Flag.ModelCheck.HorSat2 -> if not Mconfig.horsat2_available then fatal "HorSat2 not found"
    | Flag.ModelCheck.HorSatP -> if not Mconfig.horsatp_available then fatal "HorSatP not found"
  end;
  begin
    if !Flag.Refine.use_rec_chc_solver then
      match !Flag.Refine.solver with
      | Flag.Refine.Hoice -> if not Mconfig.hoice_available then fatal "HoICE not found"
      | Flag.Refine.Z3
      | Flag.Refine.Z3_spacer -> if not Mconfig.z3_available then fatal "Z3 binary not found"
  end;
  begin
    if Flag.Experiment.HORS_quickcheck.(!use <> None) then
      if not Mconfig.hors_quickcheck_available then fatal "hors_quickcheck not found"
  end

let string_of_exception = function
  | e when Fpat.FPATConfig.is_fpat_exception e ->
     Fpat.FPATConfig.string_of_fpat_exception e
  | Syntaxerr.Error _err -> "Syntaxerr.Error"
  | Typecore.Error(_loc,_env,_err) -> "Typecore.Error"
  | Typemod.Error(_loc,_env,_err) -> "Typemod.Error"
  | Env.Error _e -> "Env.Error"
  | Typetexp.Error(_loc,_env,_err) -> "Typetexp.Error"
  | Lexer.Error(_err, _loc) -> "Lexer.Error"
  | CEGAR_syntax.NoProgress -> "CEGAR_syntax.NoProgress"
  | Fatal _s -> "Fatal"
  | TimeOut
  | Fpat.Timer.Timeout
  | Assert_failure("timer.ml", _, _) -> "TimeOut"
  | Killed -> "Killed"
  | e -> Printexc.to_string e

let print_error e =
  match e with
  | Fpat.RefTypInfer.FailedToRefineTypes ->
      Format.eprintf "Verification failed:@.";
      Format.eprintf "  MoCHi could not refute an infeasible error path@.";
      Format.eprintf "  due to the incompleteness of the refinement type system@."
  | e when Fpat.FPATConfig.is_fpat_exception e ->
      Format.eprintf "FPAT: %a@." Fpat.FPATConfig.pr_exception e
  | Syntaxerr.Error _
  | Typecore.Error _
  | Typemod.Error _
  | Env.Error _
  | Typetexp.Error _
  | Lexer.Error _ as e ->
      Parser_wrapper.report_error e
  | CEGAR_syntax.NoProgress ->
      Format.eprintf "Unknown. (CEGAR not progress) @."
  | CEGAR_abst.NotRefined ->
      Format.eprintf "Verification failed (new error path not found)@."
  | Fatal s ->
      Format.eprintf "Fatal error: %s@." s
  | Unsupported s ->
      Format.eprintf "Unsupported: %s@." s
  | Sys_error s ->
      Format.eprintf "%s@." s
  | TimeOut
  | Fpat.Timer.Timeout
  | Assert_failure("timer.ml", _, _) -> (* for Fpat *)
      Format.eprintf "Verification failed (time out)@."
  | e when !Flag.Debug.debug_module = [] ->
      Format.eprintf "Exception: %s@." @@ Printexc.to_string e
  | _ -> raise e

let init_before_parse_arg () =
  fpat_init1 ()

let init_after_parse_arg () =
  if Flag.ModelCheck.(!mc <> TRecS) then
    Flag.ModelCheck.church_encode := true;
  fpat_init2 ();
  Fpat.Global.timeout_z3 := 60 * 60 * 1000;
  ignore @@ Unix.alarm !Flag.Limit.time;
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise TimeOut));
  Color.init ();
  check_env ();
  set_status @@ Flag.Log.Other "Start";
  IO.empty_file @@ Filename.change_extension !!Flag.Input.main "json"

let check_bin filename =
  let open Main_loop_util in
  let {args;preprocessed} = Marshal.from_file_exn !!Flag.Input.main in
  Cmd.parse_arg_list true args;
  Flag.Input.filenames := [filename];
  let s,r =
    match Main_loop.((check preprocessed).result) with
    | CEGAR.Safe _ -> Flag.Log.Safe, true
    | CEGAR.Unsafe _ -> Flag.Log.Unsafe, false
    | CEGAR.Unknown s -> Flag.Log.Unknown s, false
    | exception e -> Flag.Log.Error (string_of_exception e), false
  in
  set_status s;
  r

let debug_preprocess filename =
  let debug = Marshal.from_file_exn filename in
  let open Preprocess in
  Cmd.parse_arg_list true debug.debug_args;
  Verbose.printf "problem: %a@." Problem.print' debug.debug_problem;
  let pp = !!Preprocess.all in
  try
    let tr = Preprocess.(assoc debug.debug_label pp) in
    ignore Preprocess.(trans_and_print tr debug.debug_problem);
    true
  with _ -> false


let wrap_input_for_fair_termination () =
  if List.length !Flag.Input.filenames > 1 then unsupported "Multiple files for fair-termination checking";
  let filename = Filename.change_extension !!Flag.Input.main "ft.ml" in
  let text =
    !!Flag.Input.main
    |> IO.input_file
    |> Fair_termination_util.add_event
  in
  IO.output_file ~filename ~text;
  Flag.Input.filenames := [filename]

let verify orig spec t =
  if !Flag.Method.modular then
    Modular.main orig spec t
  else
    let problem =
      let assertion = Spec.get_assertion spec t in
      if assertion = [] then
        if spec.Spec.assertion <> [] then
          fatal "Unused assertions in spec."
        else
          Problem.safety ~spec t
      else
        let spec = {spec with assertion = []} in
        Problem.ref_type_check ~spec t assertion
    in
    Main_loop.run ~orig problem

let main () =
  if !!Flag.Input.is_bin then
    check_bin !!Flag.Input.main
  else if !!Flag.Input.is_debug then
    debug_preprocess !!Flag.Input.main
  else if !!Flag.Input.is_cegar then
    main_input_cegar !!Flag.Input.main
  else
    let () =
      if Flag.(List.mem !mode [FairTermination;FairNonTermination]) then
        wrap_input_for_fair_termination ()
    in
    let origs,parsed = Parser_wrapper.parse_files !Flag.Input.filenames in
    if !Flag.Print.exit_after_parsing then exit 0;
    let orig = List.hd origs in
    if false then Verbose.printf "%a:@. @[%a@.@." Color.s_red "parsed" Print.term_typ parsed;
    let spec = Spec.read Spec_parser.spec Spec_lexer.token in
    match !Flag.mode with
    | Flag.Trans -> main_trans parsed
    | Flag.Quick_check -> main_quick_check parsed
    | Flag.Verify_ref_typ -> Verify_ref_typ.main orig spec parsed
    | Flag.Termination -> main_termination parsed
    | Flag.FairTermination -> main_fair_termination spec parsed
    | Flag.Verify_module -> Verify_module.main (verify orig spec) parsed
    | _ -> verify orig spec parsed

let () =
  if !Sys.interactive then ()
  else
    try
      init_before_parse_arg ();
      Cmd.parse_arg ();
      if not !!is_only_result then Cmd.print_env true false;
      save_input_to_file !Flag.Input.filenames;
      init_after_parse_arg ();
      if main () then decr Flag.Log.cegar_loop;
      Fpat.SMTProver.finalize ();
      print_info ()
    with
    | e when not !!Debug.check ->
        set_status @@ Flag.Log.Error (string_of_exception e);
        Format.print_flush ();
        flush_all ();
        output_json ();
        Main_loop.print_result_delimiter ();
        print_error e;
        exit 1
