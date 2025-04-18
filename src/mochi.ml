open Util
open Mochi_util

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

let print_info_default () =
  if !Flag.Termination.add_closure_exparam && Flag.Log.(!result = Terminating) then
    Format.fprintf !Flag.Print.target "exparam inserted program:@. %a@."
      Print.(term_custom { !config_default with unused = true })
      !ExtraParamInfer.origWithExparam;
  if Flag.(!mode = Termination) && Flag.Log.(!result = Terminating) then
    List.iter
      (fun (f_name, (cycles, pred)) ->
        Format.fprintf !Flag.Print.target "ranking function(%s)[inference cycle: %d]: %a\n" f_name
          cycles BRA_types.pr_ranking_function pred;
        if !Flag.Termination.add_closure_exparam then
          let str_exparam = ExtraParamInfer.to_string_CoeffInfos pred.BRA_types.coeffsMap in
          if str_exparam <> "" then
            Format.fprintf !Flag.Print.target "exparam(%s):\n%s\n" f_name str_exparam)
      !Termination_loop.lrf;
  if Flag.(!mode = FairTermination) then
    Format.fprintf !Flag.Print.target "cycles: %d@." !Flag.FairTermination.loop_count;
  Format.fprintf !Flag.Print.target "CEGAR-cycles: %d@." !Flag.Log.cegar_loop;
  Format.fprintf !Flag.Print.target "total: %.3f sec@." !!Time.get;
  (*  Format.fprintf !Flag.Print.target "  pre: %.3f sec@." !Flag.Log.Time.preprocess;*)
  Format.fprintf !Flag.Print.target "  abst: %.3f sec@." !Flag.Log.Time.abstraction;
  Format.fprintf !Flag.Print.target "  mc: %.3f sec@." !Flag.Log.Time.mc;
  if Flag.Experiment.HORS_quickcheck.(!use <> None) then
    Format.fprintf !Flag.Print.target "    hors_quickcheck: %.3f sec@."
      !Flag.Log.Time.hors_quickcheck;
  Format.fprintf !Flag.Print.target "  refine: %.3f sec@." !Flag.Log.Time.cegar;
  if !Flag.Method.relative_complete then
    Format.fprintf !Flag.Print.target "    exparam: %.3f sec@." !Flag.Log.Time.parameter_inference;
  Format.pp_print_flush Format.std_formatter ()

let json_of_result init =
  let if_ b xs = if b then xs () else [] in
  let info =
    [
      [
        ("filename", `String !!Flag.IO.main);
        ("command", `List (List.map (fun s -> `String s) !Flag.Log.args));
        ("start_at", `Float (!!Unix.time -. !!Sys.time));
      ];
      if_ (not init) (fun () ->
          [
            ("result", `String (Flag.Log.string_of_result false));
            ("cycles", `Int !Flag.Log.cegar_loop);
            ("total", `Float !!Time.get);
            (*     "pre", `Float !Flag.Log.Time.preprocess;*)
            ("abst", `Float !Flag.Log.Time.abstraction);
            ("mc", `Float !Flag.Log.Time.mc);
            ("refine", `Float !Flag.Log.Time.cegar);
          ]);
      if_
        Flag.(!mode = Termination)
        (fun () ->
          let json_of_lrf (f_name, (cycles, pred)) =
            let rank_fun = Format.asprintf "%a" BRA_types.pr_ranking_function pred in
            (f_name, `Assoc [ ("function", `String rank_fun); ("inferCycles", `Int cycles) ])
          in
          [ ("ranking", `Assoc (List.map json_of_lrf !Termination_loop.lrf)) ]);
      if_
        Flag.Experiment.HORS_quickcheck.(!use <> None)
        (fun () ->
          [
            ("hors_quickcheck", `Float !Flag.Log.Time.hors_quickcheck);
            ( "cex_length",
              `String
                (List.to_string ~delimiter:"," string_of_int
                   !Flag.Experiment.HORS_quickcheck.cex_length_history) );
          ]);
      if_ !Flag.Method.relative_complete (fun () ->
          [ ("exparam", `Float !Flag.Log.Time.parameter_inference) ]);
      if_ !Flag.Method.modular (fun () ->
          let open Modular in
          [
            ("#typeChecker", `Int !num_tycheck);
            ("typeChecker", `Float !time_check);
            ("typeSynthesizer", `Float !time_synthesize);
          ]);
      if_ !Flag.Method.sub (fun () ->
          let open Flag.Experiment.Slice in
          [
            ("alpha", `Float !alpha);
            ("max_hop", `Int !max_hop);
            ("before_slice", `Float !Flag.Log.Time.before_slice);
          ]);
    ]
  in
  `Assoc (List.flatten info)

let output_json_to_file b = JSON.to_file !Flag.Log.json_file (json_of_result b)

let print_json () =
  if !Flag.Print.json then
    Format.fprintf !Flag.Print.target "%a@." (JSON.pretty_print ~std:true) (json_of_result false);
  if !Flag.Log.json_file <> "" then output_json_to_file false

let print_info_modular () =
  Format.fprintf !Flag.Print.target "#typeChecker: %d@." !Modular.num_tycheck;
  Format.fprintf !Flag.Print.target "total: %.3f sec@." !!Time.get;
  Format.fprintf !Flag.Print.target "  typeChecker: %.3f sec@." !Modular.time_check;
  Format.fprintf !Flag.Print.target "  typeSynthesizer: %.3f sec@." !Modular.time_synthesize

let print_info () =
  print_json ();
  if !Flag.Print.result then
    if !Flag.Method.modular then print_info_modular () else print_info_default ()

let main_input_cegar filename =
  let open CEGAR_syntax in
  let@ cin = IO.CPS.open_in filename in
  let lb = Lexing.from_channel cin in
  lb.Lexing.lex_curr_p <-
    {
      Lexing.pos_fname = Filename.basename filename;
      Lexing.pos_lnum = 1;
      Lexing.pos_cnum = 0;
      Lexing.pos_bol = 0;
    };
  let prog = CEGAR_parser.prog CEGAR_lexer.token lb in
  let prog' = Typing.infer { prog with env = [] } in
  let env = List.filter_out (fun (f, _) -> List.mem_assoc f prog.env) prog'.env @ prog.env in
  Main_loop.run_cegar { prog with env }

let main_termination parsed =
  let parsed = BRA_transform.lambda_lift (BRA_transform.remove_unit_wraping parsed) in
  let _ = Verbose.printf "lambda-lifted::@. @[%a@.@." Print.term parsed in
  let parsed = BRA_transform.regularization parsed in
  let _ = Verbose.printf "regularized::@. @[%a@.@." Print.term parsed in
  let parsed =
    if !Flag.Termination.add_closure_depth then ExtraClsDepth.addExtraClsDepth parsed else parsed
  in
  let _ =
    if !Flag.Termination.add_closure_depth then
      Verbose.printf "closure depth inserted::@. @[%a@.@." Print.term parsed
  in
  let parsed =
    if !Flag.Termination.add_closure_exparam then ExtraParamInfer.addTemplate parsed else parsed
  in
  let _ =
    if !Flag.Termination.add_closure_exparam then
      Verbose.printf "closure exparam inserted::@. @[%a@.@." Print.term parsed
  in
  let holed_list = BRA_transform.to_holed_programs parsed in
  let coeffs = List.filter Id.is_coefficient @@ Syntax.get_fv parsed in
  let result =
    try
      List.for_all
        (fun holed ->
          let init_predicate_info =
            {
              BRA_types.variables =
                List.map BRA_transform.extract_id
                  (BRA_state.get_argvars holed.BRA_types.state holed.BRA_types.verified);
              BRA_types.coeffsMap =
                (if !Flag.Termination.add_closure_exparam then
                   List.map (Pair.add_right @@ Fun.const 0) coeffs
                 else []);
              BRA_types.prev_variables =
                List.map BRA_transform.extract_id
                  (BRA_state.get_prev_statevars holed.BRA_types.state holed.BRA_types.verified);
              BRA_types.coefficients = [];
              BRA_types.errorPaths = [];
              BRA_types.errorPathsWithExparam = [];
            }
          in
          let predicate_que = Queue.create () in
          let _ = Queue.add (fun _ -> init_predicate_info) predicate_que in
          Termination_loop.reset_cycle ();
          Termination_loop.run predicate_que holed)
        holed_list
    with Fpat.PolyConstrSolver.NoSolution | Termination_loop.FailedToFindLLRF -> false
  in
  if result then (
    set_status Flag.Log.Terminating;
    if !Flag.Print.result then Format.fprintf !Flag.Print.target "Terminating!@.")
  else (
    set_status @@ Flag.Log.Unknown "";
    if !Flag.Print.result then Format.fprintf !Flag.Print.target "Unknown...@.");
  result

let main_fair_termination spec parsed =
  let result = Fair_termination.run spec parsed in
  if result then Format.fprintf !Flag.Print.target "Fair terminating!@.@."
  else Format.fprintf !Flag.Print.target "Unknown...@.@.";
  result

let output_randint_refinement_log input_string =
  let cout =
    let input =
      let dirname = !!Temp.S.dir in
      let basename = !!Flag.IO.main in
      dirname ^ "/refinement/" ^ Filename.change_extension basename "refinement"
    in
    open_out_gen [ Open_wronly; Open_trunc; Open_text; Open_creat ] 0o644 input
  in
  output_string cout ("[INPUT]:\n" ^ input_string ^ "\n");
  close_out cout

let main_quick_check t =
  t
  |> Preprocess.(run_on_term (Preprocess_common.before CPS !!Preprocess.all))
  |> Quick_check.repeat_forever

let main_trans { Parser_wrapper.parsed = t; ext_mod_typ } =
  Flag.PrettyPrinter.color := false;
  let print_as_ml pps =
    Preprocess.run_on_term pps
    |- Trans.remove_unambiguous_id
    |- Trans.replace_typ_result_with_unit
    |- Trans.rename_for_ocaml
    |- Format.fprintf !Flag.Print.target "%a@." Print.as_ocaml_typ
  in
  (match !Flag.Trans.destination with
  | Before_CPS -> print_as_ml (Preprocess_common.before CPS !!Preprocess.all) t
  | CPS -> print_as_ml (Preprocess_common.before_and Remove_pair !!Preprocess.all) t
  | CHC -> (
      let pps = Preprocess_common.before Encode_list !!Preprocess.all in
      let t' = t |> Preprocess.run_on_term pps |> Trans.alpha_rename ~whole:true in
      let ty = Ref_type.of_simple t'.Syntax.typ in
      let env = Ref_type.Env.empty in
      try Ref_type_check.print stdout env t' ty
      with e when !Flag.Debug.debug_module = [] ->
        Format.eprintf "%s@." (Printexc.to_string e);
        Format.fprintf !Flag.Print.target ")@.(get-proof)@." (* for hoice *);
        exit 1)
  | HFLz ->
      let pps = !!Preprocess.all in
      Problem.safety ~ext_mod_typ t
      |> Preprocess.run_problem pps
      |> Preprocess.get_problem_of
      |> Problem.map (Trans.map_var (Id.map_name String.sign_to_letters))
      |> Main_loop.cegar_of_problem []
      |> Triple.fst
      |> CEGAR.update_non_rec_info
      |> CEGAR_trans.expand_non_rec
      |> CEGAR_trans.bool_to_int
      |> CEGAR_trans.lift_for_hfl
      |> HFLz.hes_of_prog
      |> Format.printf "%a" HFLz.Print.hes);
  exit 0

let save_input_to_file filenames =
  match filenames with
  | [] | [ "-" ] ->
      let filename = Temp.S.file "stdin.ml" in
      Flag.IO.filenames := [ filename ];
      IO.output_file ~filename ~text:(IO.input_all stdin)
  | _ -> ()

(* called before parsing options *)
let fpat_init1 () = Fpat.FPATConfig.set_default ()

(* called after parsing options *)
let fpat_init2 () =
  let open Fpat in
  Global.target_filename := !!Flag.IO.main;
  BatOption.may (fun cmd -> SMTProver.cvc3_command := cmd) !Flag.External.cvc3;
  SMTProver.initialize ()

let string_of_exception = function
  | e when Fpat.FPATConfig.is_fpat_exception e -> Fpat.FPATConfig.string_of_fpat_exception e
  | Syntaxerr.Error _err -> "Syntaxerr.Error"
  | Typecore.Error (_loc, _env, _err) -> "Typecore.Error"
  | Typemod.Error (_loc, _env, _err) -> "Typemod.Error"
  | Env.Error _e -> "Env.Error"
  | Typetexp.Error (_loc, _env, _err) -> "Typetexp.Error"
  | Lexer.Error (_err, _loc) -> "Lexer.Error"
  | CEGAR_syntax.NoProgress -> "CEGAR_syntax.NoProgress"
  | Failure _s -> "Failure"
  | TimeOut | Fpat.Timer.Timeout | Assert_failure ("timer.ml", _, _) -> "TimeOut"
  | Killed -> "Killed"
  | e -> Printexc.to_string e

let print_error e =
  match Parser_wrapper.report_error e with
  | () -> ()
  | exception _ -> (
      match e with
      | Fpat.RefTypInfer.FailedToRefineTypes ->
          Format.eprintf "Verification failed:@.";
          Format.eprintf "  MoCHi could not refute an infeasible error path@.";
          Format.eprintf "  due to the incompleteness of the refinement type system@."
      | e when Fpat.FPATConfig.is_fpat_exception e ->
          Format.eprintf "FPAT: %a@." Fpat.FPATConfig.pr_exception e
      | CEGAR_syntax.NoProgress -> Format.eprintf "Unknown. (CEGAR not progress) @."
      | CEGAR_abst.NotRefined -> Format.eprintf "Verification failed (new error path not found)@."
      | Failure s -> Format.eprintf "Failure: %s@." s
      | Unsupported s -> Format.eprintf "Unsupported: %s@." s
      | Killed -> Format.eprintf "Killed@."
      | Sys_error s -> Format.eprintf "%s@." s
      | TimeOut | Fpat.Timer.Timeout | Assert_failure ("timer.ml", _, _) ->
          (* for Fpat *)
          Format.eprintf "Verification failed (time out)@."
      | e when !Flag.Debug.debug_module = [] || not !!Dbg.check ->
          Format.eprintf "Exception: %s@." @@ Printexc.to_string e
      | _ -> raise e)

let init_before_parse_arg () =
  find_binaries ();
  Model_check.init ();
  fpat_init1 ()

let init_after_parse_arg () =
  if !Model_check.current_mc <> Some TRecS then Flag.ModelCheck.church_encode := true;
  fpat_init2 ();
  Fpat.Global.timeout_z3 := 60 * 60 * 1000;
  ignore @@ Unix.alarm !Flag.Limit.time;
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise TimeOut));
  check_env ();
  set_status @@ Flag.Log.Other "Start";
  if !Flag.Log.json_file <> "" then output_json_to_file true

let wrap_input_for_fair_termination () =
  if List.length !Flag.IO.filenames > 1 then
    unsupported "Multiple files for fair-termination checking";
  let filename = Temp.S.ext "ft.ml" in
  let text = !!Flag.IO.main |> IO.input_file |> Fair_termination_util.add_event in
  IO.output_file ~filename ~text;
  Flag.IO.filenames := [ filename ]

let verify orig (spec : Spec.t) ext_mod_typ t =
  if !Flag.Method.modular then Modular.main ext_mod_typ orig spec t
  else
    let problem =
      let assertion = Spec.get_assertion spec t in
      if assertion = [] then
        if spec.assertion <> [] then failwith "Unused assertions in spec."
        else Problem.safety ~spec ~ext_mod_typ t
      else
        let spec = { spec with assertion = [] } in
        Problem.ref_type_check ~spec ~ext_mod_typ t assertion
    in
    Main_loop.run ~orig problem

let main_input_chc filename =
  Flag.Refine.use_rec_chc_solver := false;
  Flag.Method.slice := false;
  filename |> Smtlib_wrapper.read |> Chc2prog.trans |> verify [] Spec.init []

let main_bin filename =
  assert (!Flag.Parallel.child <> "");
  filename
  |> Marshal.from_file_exn
  |> CEGAR.run
  |> Marshal.to_file ~flag:[ Closures ] !Flag.Parallel.child;
  exit 0

let main () =
  if !!Flag.IO.is_bin then main_bin !!Flag.IO.main
  else if !!Flag.IO.is_cegar then main_input_cegar !!Flag.IO.main
  else if !!Flag.IO.is_smt2 || !Flag.Method.chc then main_input_chc !!Flag.IO.main
  else
    let () =
      if Flag.(List.mem !mode [ FairTermination; FairNonTermination ]) then
        wrap_input_for_fair_termination ()
    in
    let spec = Spec.read (Spec_parser.spec Spec_lexer.token) in
    let env = Parser_wrapper.make_env ~target_locs:!Flag.Method.targets ~spec () in
    let p = Parser_wrapper.parse_files ~env !Flag.IO.filenames in
    if !Flag.Print.exit_after_parsing then exit 0;
    let orig = List.hd p.origs in
    if false then Verbose.printf "%a:@. @[%a@.@." Color.s_red "parsed" Print.term_typ p.parsed;
    match !Flag.mode with
    (* TODO: use p.ext_mod_typ *)
    | Flag.Trans -> main_trans p
    | Flag.Quick_check -> main_quick_check p.parsed
    | Flag.Verify_ref_typ -> Verify_ref_typ.main orig spec p.parsed
    | Flag.Termination -> main_termination p.parsed
    | Flag.FairTermination -> main_fair_termination spec p.parsed
    | Flag.Verify_module -> Verify_module.main (verify orig spec p.ext_mod_typ) p.parsed
    | _ when !Flag.Debug.minimize ->
        let verify = verify orig spec p.ext_mod_typ in
        let conf = Minimizer.run verify p.parsed in
        let error = Minimizer.get_error verify conf.target in
        Format.fprintf !Flag.Print.target "Minimized:@.%a@." Print.as_ocaml conf.target;
        Format.fprintf !Flag.Print.target "Error: %s@." error;
        exit 0
    | _ -> verify orig spec p.ext_mod_typ p.parsed

let has_debug_param () =
  match !!Sys.runtime_parameters_list |> List.assoc_opt "b" with
  | None | Some "0" -> false
  | _ -> true

let save_intermediate_files () =
  let dest = Filename.change_extension !!Flag.IO.main "out" in
  let post = if Sys.file_exists dest then "/*" else "" in
  let cmd = Format.sprintf "cp -r %s%s %s" !!Temp.S.dir post dest in
  ignore @@ Sys.command cmd

let () =
  if !Sys.interactive then ()
  else
    try
      init_before_parse_arg ();
      Cmd.parse_arg ();
      if !Flag.IO.save_files then (
        ignore !!Temp.dir;
        at_exit save_intermediate_files);
      if not !!is_only_result then Format.printf "%t@." (Cmd.print_env ~cmd:true ~json:false);
      save_input_to_file !Flag.IO.filenames;
      init_after_parse_arg ();
      if main () then decr Flag.Log.cegar_loop;
      Fpat.SMTProver.finalize ();
      print_info ()
    with e when not !!Dbg.check ->
      if !Flag.IO.filenames <> [] then set_status @@ Flag.Log.Error (string_of_exception e);
      print_json ();
      Main_loop.print_result_delimiter ();
      print_error e;
      exit 1
