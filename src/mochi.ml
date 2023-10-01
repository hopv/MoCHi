open Util
open Mochi_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let print_info_default () =
  if !Flag.Termination.add_closure_exparam && Flag.Log.(!result = Terminating) then
    Format.fprintf !Flag.Print.target "exparam inserted program:@. %a@." Print.(term_custom {!config_default with unused=true}) !ExtraParamInfer.origWithExparam;
  if Flag.(!mode = Termination) && Flag.Log.(!result = Terminating) then
    begin
      List.iter
        (fun (f_name, (cycles, pred)) ->
         Format.fprintf !Flag.Print.target "ranking function(%s)[inference cycle: %d]: %a\n" f_name cycles BRA_types.pr_ranking_function pred;
         if !Flag.Termination.add_closure_exparam then
           let str_exparam = ExtraParamInfer.to_string_CoeffInfos pred.BRA_types.coeffsMap in
           if str_exparam <> "" then Format.fprintf !Flag.Print.target "exparam(%s):\n%s\n" f_name str_exparam)
        !Termination_loop.lrf
    end;
  if Flag.(!mode = FairTermination) then
    Format.fprintf !Flag.Print.target "cycles: %d@." !Flag.FairTermination.loop_count;
  Format.fprintf !Flag.Print.target "CEGAR-cycles: %d@." !Flag.Log.cegar_loop;
  Format.fprintf !Flag.Print.target "total: %.3f sec@." !!Time.get;
  (*  Format.fprintf !Flag.Print.target "  pre: %.3f sec@." !Flag.Log.Time.preprocess;*)
  Format.fprintf !Flag.Print.target "  abst: %.3f sec@." !Flag.Log.Time.abstraction;
  Format.fprintf !Flag.Print.target "  mc: %.3f sec@." !Flag.Log.Time.mc;
  if Flag.Experiment.HORS_quickcheck.(!use <> None) then
    Format.fprintf !Flag.Print.target "    hors_quickcheck: %.3f sec@." !Flag.Log.Time.hors_quickcheck;
  Format.fprintf !Flag.Print.target "  refine: %.3f sec@." !Flag.Log.Time.cegar;
  if !Flag.Method.relative_complete then
    Format.fprintf !Flag.Print.target "    exparam: %.3f sec@." !Flag.Log.Time.parameter_inference;
  Format.pp_print_flush Format.std_formatter ()

let output_json () =
  let assoc =
    ["filename", `String !!Flag.IO.main;
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
         let open Modular in
         ["#typeChecker", `Int !num_tycheck;
          "typeChecker", `Float !time_check;
          "typeSynthesizer", `Float !time_synthesize]
       else
         [])
    @
      (if !Flag.Method.sub then
         let open Flag.Experiment.Slice in
         ["alpha", `Float !alpha;
          "max_hop", `Int !max_hop;
          "before_slice", `Float !Flag.Log.Time.before_slice]
       else
         [])
  in
  JSON.to_file !!Flag.IO.result (`Assoc assoc)

let print_info_modular () =
  Format.fprintf !Flag.Print.target "#typeChecker: %d@." !Modular.num_tycheck;
  Format.fprintf !Flag.Print.target "total: %.3f sec@." !!Time.get;
  Format.fprintf !Flag.Print.target "  typeChecker: %.3f sec@." !Modular.time_check;
  Format.fprintf !Flag.Print.target "  typeSynthesizer: %.3f sec@." !Modular.time_synthesize

let print_info () =
  output_json ();
  if !Flag.Print.result then
    if !Flag.Method.modular then
      print_info_modular ()
    else
      print_info_default ()

let main_input_cegar filename =
  let open CEGAR_syntax in
  let@ cin = IO.CPS.open_in filename in
  let lb = Lexing.from_channel cin in
  lb.Lexing.lex_curr_p <-
    {Lexing.pos_fname = Filename.basename filename;
     Lexing.pos_lnum = 1;
     Lexing.pos_cnum = 0;
     Lexing.pos_bol = 0};
  let prog = CEGAR_parser.prog CEGAR_lexer.token lb in
  let prog' = Typing.infer {prog with env=[]} in
  let env = List.filter_out (fun (f,_) -> List.mem_assoc f prog.env) prog'.env @ prog.env in
  Main_loop.run_cegar {prog with env}

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
  let coeffs = List.filter Id.is_coefficient @@ Syntax.get_fv parsed in
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
      if !Flag.Print.result then Format.fprintf !Flag.Print.target "Terminating!@."
    end
  else
   begin
      set_status @@ Flag.Log.Unknown "";
     if !Flag.Print.result then Format.fprintf !Flag.Print.target "Unknown...@."
   end;
  result

let main_fair_termination spec parsed =
  let result = Fair_termination.run spec parsed in
  if result
  then Format.fprintf !Flag.Print.target "Fair terminating!@.@."
  else Format.fprintf !Flag.Print.target "Unknown...@.@.";
  result

let output_randint_refinement_log input_string =
  let cout =
    let input =
      let dirname = Filename.dirname !!Flag.IO.temp in
      let basename = Filename.basename !!Flag.IO.temp in
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
    |- Format.fprintf !Flag.Print.target "%a@." Print.as_ocaml_typ
  in
  begin
    match !Flag.Trans.destination with
    | Flag.Trans.Before_CPS -> print_as_ml Preprocess.(before CPS pps_all) t
    | Flag.Trans.CPS -> print_as_ml Preprocess.(before_and Remove_pair pps_all) t
    | Flag.Trans.CHC ->
        let t' =
          t
          |> Preprocess.(run_on_term (before Encode_list pps_all))
          |> Trans.alpha_rename ~whole:true
        in
        let ty = Ref_type.of_simple t'.Syntax.typ in
        let env = Ref_type.Env.empty in
        try
          Ref_type_check.print stdout env t' ty
        with e when !Flag.Debug.debug_module = [] ->
          Format.eprintf "%s@." (Printexc.to_string e);
          Format.fprintf !Flag.Print.target ")@.(get-proof)@."; (* for hoice *)
          exit 1
  end;
  exit 0

let make_temp_file () =
  let dir = "/tmp/mochi" in
  let template = Format.asprintf "%s/%a_XXXXXXXX.ml" dir Time.print_simple !!Unix.time in
  (try Unix.mkdir dir 0o755 with Unix.Unix_error(Unix.EEXIST, _, _) -> ());
  Unix.CPS.open_process_in ("mktemp " ^ template) input_line
  |@> Verbose.printf {|Temporary file "%s" is created@.@.|}

let copy_input_file file =
  let temp_file = !!make_temp_file in
  IO.copy_file ~src:file ~dest:temp_file;
  temp_file

let save_input_to_file filenames =
  match filenames with
  | []
  | ["-"] ->
      let filename = if !Flag.use_temp then !!make_temp_file else "stdin.ml" in
      Flag.IO.filenames := [filename];
      IO.output_file ~filename ~text:(IO.input_all stdin)
  | _ ->
      if !Flag.use_temp then
        filenames
        |> List.map copy_input_file
        |> Ref.set Flag.IO.filenames

(* called before parsing options *)
let fpat_init1 () =
  Fpat.FPATConfig.set_default ()

(* called after parsing options *)
let fpat_init2 () =
  let open Fpat in
  Global.target_filename := !!Flag.IO.main;
  BatOption.may (fun cmd -> SMTProver.cvc3_command := cmd) !Flag.External.cvc3;
  SMTProver.initialize ()

let check_env () =
  begin
    if !Flag.Refine.use_rec_chc_solver then
      match !Flag.Refine.solver with
      | Flag.Refine.Hoice -> if Mconfig.hoice = None then failwith "HoICE not found"
      | Flag.Refine.Z3
      | Flag.Refine.Z3_spacer -> if Mconfig.z3 = None then failwith "Z3 binary not found"
  end;
  if Flag.Experiment.HORS_quickcheck.(!use <> None) then
    if Mconfig.hors_quickcheck = None then failwith "hors_quickcheck not found"

let string_of_exception = function
  | e when Fpat.FPATConfig.is_fpat_exception e -> Fpat.FPATConfig.string_of_fpat_exception e
  | Syntaxerr.Error _err -> "Syntaxerr.Error"
  | Typecore.Error(_loc,_env,_err) -> "Typecore.Error"
  | Typemod.Error(_loc,_env,_err) -> "Typemod.Error"
  | Env.Error _e -> "Env.Error"
  | Typetexp.Error(_loc,_env,_err) -> "Typetexp.Error"
  | Lexer.Error(_err, _loc) -> "Lexer.Error"
  | CEGAR_syntax.NoProgress -> "CEGAR_syntax.NoProgress"
  | Failure _s -> "Failure"
  | TimeOut
  | Fpat.Timer.Timeout
  | Assert_failure("timer.ml", _, _) -> "TimeOut"
  | Killed -> "Killed"
  | e -> Printexc.to_string e

let print_error e =
  match Parser_wrapper.report_error e with
  | () -> ()
  | exception _ ->
      match e with
      | Fpat.RefTypInfer.FailedToRefineTypes ->
          Format.eprintf "Verification failed:@.";
          Format.eprintf "  MoCHi could not refute an infeasible error path@.";
          Format.eprintf "  due to the incompleteness of the refinement type system@."
      | e when Fpat.FPATConfig.is_fpat_exception e ->
          Format.eprintf "FPAT: %a@." Fpat.FPATConfig.pr_exception e
      | CEGAR_syntax.NoProgress ->
          Format.eprintf "Unknown. (CEGAR not progress) @."
      | CEGAR_abst.NotRefined ->
          Format.eprintf "Verification failed (new error path not found)@."
      | Failure s ->
          Format.eprintf "Failure: %s@." s
      | Unsupported s ->
          Format.eprintf "Unsupported: %s@." s
      | Killed ->
          Format.eprintf "Killed@."
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
  Model_check.init ();
  fpat_init1 ()

let init_after_parse_arg () =
  if !Model_check.current_mc <> Some TRecS then
    Flag.ModelCheck.church_encode := true;
  fpat_init2 ();
  Fpat.Global.timeout_z3 := 60 * 60 * 1000;
  ignore @@ Unix.alarm !Flag.Limit.time;
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise TimeOut));
  check_env ();
  set_status @@ Flag.Log.Other "Start";
  IO.empty_file @@ !!Flag.IO.result

let check_bin filename =
  let open Main_loop_util in
  let {args;preprocessed} = Marshal.from_file_exn !!Flag.IO.main in
  Cmd.parse_arg_list true args;
  Flag.IO.filenames := [filename];
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
  if List.length !Flag.IO.filenames > 1 then unsupported "Multiple files for fair-termination checking";
  let filename = Filename.change_extension !!Flag.IO.temp "ft.ml" in
  let text =
    !!Flag.IO.main
    |> IO.input_file
    |> Fair_termination_util.add_event
  in
  IO.output_file ~filename ~text;
  Flag.IO.filenames := [filename]

let verify orig spec {Parser_wrapper.ext_typ; ext_exc; ext_mod_typ} t =
  if !Flag.Method.modular then
    Modular.main ext_typ ext_exc ext_mod_typ orig spec t
  else
    let problem =
      if !Flag.Preprocess.restart_preprocess then
        None
      else
        let assertion = Spec.get_assertion spec t in
        if assertion = [] then
          if spec.Spec.assertion <> [] then
            failwith "Unused assertions in spec."
          else
            Some (Problem.safety ~spec ~ext_typ ~ext_exc ~ext_mod_typ t)
        else
          let spec = {spec with assertion = []} in
          Some (Problem.ref_type_check ~spec ~ext_typ ~ext_exc ~ext_mod_typ t assertion)
    in
    Main_loop.run ~orig problem

let main_input_chc filename =
  Flag.Refine.use_rec_chc_solver := false;
  Flag.Method.slice := false;
  filename
  |> Smtlib_wrapper.read
  |> Chc2prog.trans
  |> verify [] Spec.init {ext_typ=[]; ext_exc=[]; ext_mod_typ=[]}

let main () =
  if !!Flag.IO.is_bin then
    check_bin !!Flag.IO.main
  else if !!Flag.IO.is_debug then
    debug_preprocess !!Flag.IO.main
  else if !!Flag.IO.is_cegar then
    main_input_cegar !!Flag.IO.main
  else if !!Flag.IO.is_smt2 || !Flag.Method.chc then
    main_input_chc !!Flag.IO.main
  else
    let () =
      if Flag.(List.mem !mode [FairTermination;FairNonTermination]) then
        wrap_input_for_fair_termination ()
    in
    let p = Parser_wrapper.parse_files !Flag.IO.filenames in
    if !Flag.Print.exit_after_parsing then exit 0;
    let orig = List.hd p.origs in
    if false then Verbose.printf "%a:@. @[%a@.@." Color.s_red "parsed" Print.term_typ p.parsed;
    let spec = Spec.read Spec_parser.spec Spec_lexer.token in
    match !Flag.mode with
    | Flag.Trans -> main_trans p.parsed
    | Flag.Quick_check -> main_quick_check p.parsed
    | Flag.Verify_ref_typ -> Verify_ref_typ.main orig spec p.parsed
    | Flag.Termination -> main_termination p.parsed
    | Flag.FairTermination -> main_fair_termination spec p.parsed
    | Flag.Verify_module -> Verify_module.main (verify orig spec p.exts) p.parsed
    | _ when !Flag.Debug.minimize ->
        let verify = verify orig spec p.exts in
        let conf = Minimizer.run verify p.parsed in
        let error = Minimizer.get_error verify conf.target in
        Format.fprintf !Flag.Print.target "Minimized:@.%a@." Print.as_ocaml conf.target;
        Format.fprintf !Flag.Print.target "Error: %s@." error;
        exit 0
    | _ -> verify orig spec p.exts p.parsed

let () =
  if !Sys.interactive then ()
  else
    try
      init_before_parse_arg ();
      Cmd.parse_arg ();
      if not !!is_only_result then Cmd.print_env ~cmd:true ~json:false;
      save_input_to_file !Flag.IO.filenames;
      init_after_parse_arg ();
      if main () then decr Flag.Log.cegar_loop;
      Fpat.SMTProver.finalize ();
      print_info ()
    with
    | e when not (List.mem "b=1" @@ !!Sys.runtime_parameters_list) && !Flag.IO.filenames <> [] ->
        set_status @@ Flag.Log.Error (string_of_exception e);
        Format.print_flush ();
        flush_all ();
        output_json ();
        Main_loop.print_result_delimiter ();
        print_error e;
        exit 1
