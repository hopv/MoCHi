open Util
open Mochi_util

let print_env cmd json =
  let mochi = Revision.mochi in
  let z3_lib =
    let a,b,c,d = Z3native.get_version () in
    Format.sprintf "%d.%d.%d.%d" a b c d
  in
  let z3_bin = if Mconfig.z3_available then Some (String.trim @@ Unix.CPS.open_process_in (Mconfig.z3 ^ " -version") IO.input_all) else None in
  let trecs = TrecsInterface.version () in
  let horsat = HorSatInterface.version () in
  let horsat2 = HorSat2Interface.version () in
  let horsatp = HorSatPInterface.version () in
  let hoice = if Mconfig.hoice_available then Some (List.nth (String.split_blanc @@ Unix.CPS.open_process_in (Mconfig.hoice ^ " -V") IO.input_all) 1) else None in
  if json then
    try
      Option.iter (Format.printf "{Build:%S," -| fst) mochi;
      Format.printf "\"Z3 library\":%S," z3_lib;
      Option.iter (Format.printf "\"Z3 binary\":%S,") z3_bin;
      Option.iter (Format.printf "TRecS:%S,") trecs;
      Option.iter (Format.printf "HorSat:%S,") horsat;
      Option.iter (Format.printf "HorSat2:%S,") horsat2;
      Option.iter (Format.printf "HorSatP:%S,") horsatp;
      Option.iter (Format.printf "HoIce:%S,") hoice;
      Format.printf "OCaml:%S}" Sys.ocaml_version;
    with Option.No_value -> exit 1
  else
    begin
      Color.printf Color.Green "MoCHi: Model Checker for Higher-Order Problems@.";
      Option.iter (fun (r,t) -> Format.printf "  Build: %s (%s)@." r t) mochi;
      Format.printf "  Z3 library version: %s@." z3_lib;
      Option.iter (Format.printf "  Z3 binary: %s@.") z3_bin;
      Option.iter (Format.printf "  TRecS version: %s@.") trecs;
      Option.iter (Format.printf "  HorSat version: %s@.") horsat;
      Option.iter (Format.printf "  HorSat2 version: %s@.") horsat2;
      Option.iter (Format.printf "  HorSatP version: %s@.") horsatp;
      Option.iter (Format.printf "  HoIce version: %s@.") hoice;
      Format.printf "  OCaml version: %s@." Sys.ocaml_version;
      if cmd then
        !Flag.Log.args
        |> List.map (fun s -> if String.contains s ' ' then Format.sprintf "'%s'" s else s)
        |> Format.printf "  Command: %a@.@." (print_list Format.pp_print_string " ")
    end

let just_run_other_command cmd =
  if !Flag.Input.filenames = [] then
    (Format.eprintf "Option \"-just-run\" must follow input file@."; exit 1);
  let filename = List.hd !Flag.Input.filenames in
  let total,r = Time.measure (fun () -> Sys.command @@ snd @@ String.replace ~str:cmd ~sub:"%i" ~by:filename) in
  let result = if r = 0 then "Safe" else "Error" in
  Format.printf "{filename:%S, result:%S, total:%f}@." filename result total;
  exit r

let usage =
  "MoCHi: Model Checker for Higher-Order Problems\n\n" ^
    "Usage: " ^ Sys.executable_name ^ " [options] file\noptions are:"
let rec arg_spec for_completion =
  let align_spec specs =
    let add_desc (desc,spec) =
      let sep = String.of_char Arg.separator in
      if String.exists sep desc then unsupported "add_desc";
      let _,s = String.replace ~sub:sep ~by:" " ~str:desc in
      if for_completion then
        spec
      else
        ("", Arg.Unit ignore, s)::spec
    in
    specs
    |> List.flatten_map add_desc
    |> Arg.align
  in
  let general =
    "General options",
    ["-I", Arg.String Parser_wrapper.add_load_path,
     "<dir>  Add <dir> to the list of include directories";
     "-margin", Arg.Int Format.set_margin, "<n>  Set pretty printing margin";
     "-only-result", Arg.Unit set_only_result, " Show only result";
     "-color", Arg.Set Flag.PrettyPrinter.color, " Turn on syntax highlighting";
     "-color-always", Arg.Set Flag.PrettyPrinter.color_always, " Turn on syntax highlighting even if stdout does not refer to a terminal";
     "-ignore-conf", Arg.Set Flag.Mode.ignore_conf, " Ignore option.conf";
     "-v", Arg.Unit (fun () -> print_env false false; exit 0), " Print the version shortly";
     "-env", Arg.Unit (fun () -> print_env false true; exit 0), " Print the version and the environment as JSON";
     "-version", Arg.Unit (fun () -> print_env false false; exit 0), " Print the version";
     "-limit", Arg.Set_int Flag.Limit.time, " Set time limit (seconds)";
     "-par-limit", Arg.Set_int Flag.Parallel.time, " Set time limit for parallel execution (seconds)";
     "-pp", Arg.String (fun pp -> Flag.pp := Some pp), " Set preprocessor command";
     "-web", Arg.Set Flag.PrettyPrinter.web, " Web mode";
     "-rand-self-init", Arg.Unit Random.self_init, " Initialize the random seed";
     "-use-temp", Arg.Set Flag.use_temp, " Use temporary files for intermediate/log files";
     "-trans",
       Arg.String Flag.(fun s -> Method.(mode := Trans);
                                 Trans.set_trans s;
                                 set_only_result ()),
       Format.asprintf "<dest>  Translate the input to <dest> which must be one of the following:\n%s"
         !!Flag.Trans.string_of_destinations;
     "-p", Arg.Set_int Flag.Parallel.num, "<n>  Numbers of jobs to run simultaneously";
     "-s", Arg.Unit set_silent, " Do not print any information"]
  in
  let debug =
    "Debug options",
    ["-debug", Arg.String Flag.Debug.set_debug_modules, "<modules>  Set debug flag of modules (comma-separated)";
     "-stop-after", Arg.Set_string Flag.Debug.stop_after, "<label>"]
  in
  let experiment =
    "Options for experiments",
    ["-just-run", Arg.String just_run_other_command, " (just for experiments, %i is replaced with the filename)";
     "-hors-quickcheck-short", Arg.Unit Flag.(fun () -> Experiment.HORS_quickcheck.(use := Some Shortest)), " Use shortest counterexample generated by hors_quickcheck";
     "-hors-quickcheck-long", Arg.Unit Flag.(fun () -> Experiment.HORS_quickcheck.(use := Some Longest)), " Use longest counterexample generated by hors_quickcheck";
     "-hors-quickcheck-low", Arg.Unit Flag.(fun () -> Experiment.HORS_quickcheck.(use := Some LowestCoverage)), " Use lowest coverage counterexample generated by hors_quickcheck";
     "-hors-quickcheck-high", Arg.Unit Flag.(fun () -> Experiment.HORS_quickcheck.(use := Some HighestCoverage)), " Use highest coverage counterexample generated by hors_quickcheck"]
  in
  let abstraction =
    "Options for abstraction",
    ["-ignore-exn-arg", Arg.Unit Flag.(fun () -> Method.ignore_exn_arg := true), " Ignore exception arguments";
     "-abst-literal", Arg.Int Flag.(fun n -> Encode.abst_literal := n), " Abstract literals";
     "-abst-list-eq", Arg.Unit Flag.(fun () -> Encode.abst_list_eq := true), " Abstract list equalities";
     "-ignore-non-termination", Arg.Unit Flag.(fun () -> Method.ignore_non_termination := true), " Ignore non-termination"]
  in
  let completion =
    "Options for completion",
    ["-option-list", Arg.Unit print_option_and_exit, " Print list of options";
     "-debug-list", Arg.Unit (fun () -> List.iter (Format.printf "%s@.") !Flag.Debug.debuggable_modules; exit 0), " Print list of debug options";
     "-trans-list", Arg.Unit (fun () -> List.iter (Format.printf "%s@.") @@ List.map fst Flag.Trans.destinations; exit 0), " Print list of -trans destinations"]
  in
  let printing =
    "Options for printing",
    ["-print-abst-types", Arg.Set Flag.Print.abst_typ, " Print abstraction types when the program is safe";
     "-print-non-CPS-abst", Arg.Unit Flag.(fun () -> Mode.just_print_non_CPS_abst := true; Flag.Mode.trans_to_CPS := false), " Print non-CPS abstracted program (and exit)";
     "-print-as-ocaml", Arg.Unit Print.set_as_ocaml, " Print terms in OCaml syntax";
     "-print-progress", Arg.Set Flag.Print.progress, " Print progress (use after -modular/-imodular)";
     "-print-unused-arg", Arg.Unit Print.set_unused, " Print unused arguments";
     "-print-cert", Arg.Set Flag.Print.certificate, " Print certificates even if the model checker does not support certificates (need TRecS)";
     "-print-depth", Arg.Int Print.set_depth, " Print depth of terms";
     "-print-assert-location", Arg.Set Flag.Print.assert_loc, " Print the locations of assertions (used for -target)"]
  in
  let preprocessing =
    "Options for preprocessing",
    ["-fail-as-excep", Arg.Set Flag.Method.fail_as_exception, " Treat fail as an exception";
     "-replace-const", Arg.Set Flag.Method.replace_const, " Replace unchanging variables with constants";
     "-no-exparam", Arg.Set Flag.Method.no_exparam, " Do not add extra parameters";
     "-use-exparam", Arg.Clear Flag.Method.no_exparam, " Add extra parameters when CEGAR fails";
     "-list-option", Arg.Set Flag.Encode.encode_list_opt, " Encode list using options not pairs";
     "-disable-preprocess", Arg.Clear Flag.Mode.init_trans, " Disable encoding of recursive data structures, CPS transformation, etc.";
     "-lift-fv", Arg.Set Flag.Method.lift_fv_only, " Lift variables which occur in a body";
     "-cps-naive", Arg.Set Flag.Method.cps_simpl, " Use naive CPS transformation";
     "-ins-param-funarg", Arg.Set Flag.Method.insert_param_funarg, " Insert an extra param for functions with function arguments";
     "-tupling", Arg.Unit Flag.Method.(fun () -> tupling := not !tupling), " Toggle tupling";
     "-elim-same-arg", Arg.Set Flag.Method.elim_same_arg, " Eliminate same arguments";
     "-base-to-int", Arg.Set Flag.Encode.base_to_int, " Replace primitive base types with int";
     "-data-to-int", Arg.Set Flag.Encode.data_to_int, " Replace data types with int";
     "-bool-to-int", Arg.Set Flag.Encode.bool_to_int, " Encode booleans into integers";
     "-encode-before-make-ext-fun", Arg.Set Flag.Method.encode_before_make_ext_fun, " Encode before make external functions";
     "-make-ext-fun-before-encode", Arg.Clear Flag.Method.encode_before_make_ext_fun, " Make external functions before encode";
     "-no-slice", Arg.Clear Flag.Method.slice, " Do not slice";
     "-recdata",
       Arg.Int (fun n ->
           let open Flag.Encode.RecData in
           let d,a =
             match n with
             | 1 -> Tuple, Nothing
             | 2 -> Tuple, Top
             | 3 -> Variant, Nothing
             | 4 -> Variant, Top
             | 5 -> Variant, Unit_top
             | _ -> raise (Arg.Bad "Unknown option for -recdata")
           in
           dest := d;
           additional := a),
       Format.asprintf "<n>  Encoding of recursive data types. Examples for int-labeled binary trees: \n%s" @@
         String.join "\n" @@ List.map (fun (n,s) -> Format.sprintf "%d: %s" n s)
                               [1, "int list -> (bool * ()) * (bool * (int))";
                                2, "ty * (int list -> ty) where ty = (bool * ()) * (bool * (int))";
                                3, "int list -> Leaf | Node of int";
                                4, "ty * (int list -> ty) whene ty = Leaf | Node of int";
                                5, "unit * ty * (int list -> ty) whene ty = Leaf | Node of int"]]
  in
  let verification =
     "Options for verification",
     ["-modular",
       Arg.Unit Flag.(fun () ->
                      Method.modular := true;
                      Print.modular_progress := !Flag.Print.progress;
                      Print.progress := false;
                      Modular.infer_ind := false),
       " Modular verification";
     "-imodular",
       Arg.Unit Flag.(fun () ->
                      Method.modular := true;
                      Print.modular_progress := !Flag.Print.progress;
                      Print.progress := false;
                      Modular.infer_ind := true),
       " Modular verification (inductive mode)";
     "-verify-ref-typ", Arg.Set Flag.Method.verify_ref_typ, " Verify functions have given refinement types";
     "-spec", Arg.Set_string Flag.Input.spec, "<filename>  use <filename> as a specification";
     "-use-spec", Arg.Set Flag.Method.use_spec, " use XYZ.spec for verifying XYZ.ml if exists\n(This option is ignored if -spec is used)";
     "-disable-comment-spec", Arg.Clear Flag.Method.comment_spec, " disable {SPEC} on comments";
     "-module-verification", Arg.Set Flag.Mode.module_mode, " Check input as library";
     "-quickcheck", Arg.Set Flag.Method.quick_check, " Disprove safety via QuickCheck (other method options will be ignored)";
     "-only-specified", Arg.Set Flag.Method.only_specified, " Verify only specified targets";
     "-target", Arg.String (fun s -> Flag.Method.target := s; Flag.Method.only_specified := true),
       "<location>  Verify only assertions matched with <location> (use -print-assert-location)";
     "-sub", Arg.Set Flag.Method.sub, " Verify sub-programs"]
  in
  let modular =
     "Options for Modular Verification",
     ["-check-simple", Arg.Set Flag.Modular.check_simple, " Use simple refinement checking"]
  in
  let cegar =
    "Options for CEGAR",
    ["-split-assert", Arg.Set Flag.Method.split_assert, " Reduce to verification of multiple programs\n(each program has only one assertion)";
     "-disable-predicate-accumulation", Arg.Set Flag.Refine.disable_predicate_accumulation, " Disable predicate accumulation"]
  in
  let relative_complete =
    "Options for relatively complete verification",
    ["-relative-complete", Arg.Set Flag.Method.relative_complete, " Enable relatively complete verification from the begining"]
  in
  let predicate_abstraction =
    "Options for predicate abstraction",
    ["-abs-remove-false", Arg.Set Flag.PredAbst.remove_false, " Do not use unsatisfiable predicates in abstraction";
     "-no-enr", Arg.Unit Flag.PredAbst.(fun () -> expand_non_rec := false; expand_non_rec_init := false), " Do not expand non-recursive functions";
     "-enr", Arg.Unit Flag.PredAbst.(fun () -> expand_non_rec := true; expand_non_rec_init := false),
             " Expand non-recursive functions except those in the original program";
     "-abs-filter", Arg.Set Flag.PredAbst.use_filter, " Turn on the abstraction-filter option";
     "-neg-pred-off", Arg.Set Flag.PredAbst.never_use_neg_pred, " Never use negative predicates for abstraction";
     "-decomp-pred", Arg.Set Flag.PredAbst.decomp_pred, " Decompose abstraction predicates (e.g., [P1 && P2] ==> [P1, P2])";
     "-decomp-eq-pred", Arg.Set Flag.PredAbst.decomp_eq_pred, " Decompose abstraction predicates on equalities (e.g., [t1 = t2] ==> [t1 <= t2, t1 >= t2])";
     "-no-shift-pred", Arg.Clear Flag.PredAbst.shift_pred, " Set predicates true for safe function arguments";
     "-shift-pred", Arg.Set Flag.PredAbst.shift_pred, " Set predicates true for safe function arguments";
     "-non-cartesian", Arg.Clear Flag.PredAbst.cartesian, " Do non-cartesian abstraction"]
  in
  let homc =
    "Options for model checking",
    ["-rename-hors", Arg.Set Flag.ModelCheck.rename_hors, " Set different name to each hors file";
     "-ea", Arg.Set Flag.Print.eval_abst, " Print evaluation of abstacted program";
     "-bool-church", Arg.Set Flag.ModelCheck.church_encode, " Use church-encoding for model checking";
     "-trecs", Arg.Unit Flag.(fun () -> ModelCheck.(mc := TRecS)), " Use TRecS as the model checker";
     "-horsat", Arg.Unit Flag.(fun () -> ModelCheck.(mc := HorSat)), " Use HorSat as the model checker";
     "-horsat2", Arg.Unit Flag.(fun () -> ModelCheck.(mc := HorSat2)), " Use HorSat2 as the model checker";
     "-trecs-bin", Arg.Set_string Flag.ModelCheck.trecs,
                   Format.sprintf "<cmd>  Change trecs command to <cmd> (default: \"%s\")" !Flag.ModelCheck.trecs;
     "-horsat-bin", Arg.Set_string Flag.ModelCheck.horsat,
                    Format.sprintf "<cmd>  Change horsat command to <cmd> (default: \"%s\")" !Flag.ModelCheck.horsat;
     "-horsat2-bin", Arg.Set_string Flag.ModelCheck.horsat2,
                    Format.sprintf "<cmd>  Change horsat2 command to <cmd> (default: \"%s\")" !Flag.ModelCheck.horsat2;
     "-horsatp-bin", Arg.Set_string Flag.ModelCheck.horsatp,
                     Format.sprintf "<cmd>  Change horsatp command to <cmd> (default: \"%s\")" !Flag.ModelCheck.horsatp]
  in
  let predicate_discovery =
    "Options for predicate discovery",
    ["-fpat", Arg.String FpatInterface.parse_arg, "<option>  Pass <option> to FPAT";
     "-bool-init-empty", Arg.Set Flag.PredAbst.bool_init_empty,
       " Use an empty set as the initial sets of predicates for booleans";
     "-bool-init-self", Arg.Clear Flag.PredAbst.bool_init_empty,
       " Use predicates of themselves as the initial sets of predicates for booleans";
     "-mp", Arg.Set Flag.Refine.use_multiple_paths, " Use multiple infeasible error paths for predicate discovery";
     "-no-simplification", Arg.Set Flag.PredAbst.no_simplification, " Do not simplify abstracted programs";
     "-no-rec-chc", Arg.Clear Flag.Refine.use_rec_chc_solver, " Do not use recursive CHC solver";
     "-rec-chc", Arg.Set Flag.Refine.use_rec_chc_solver, " Use recursive CHC solver";
     "-rec-chc-limit", Arg.Set_int Flag.Refine.solver_timelimit, " Set time limit for recursive CHC solver (seconds)";
     "-rec-chc-app-id", Arg.Set Flag.Method.occurence_param, " Add extra parameter for application ID";
     "-hoice", Arg.Unit Flag.(fun () -> Refine.(solver := Hoice)), " Use HoICE as the recursive horn-clause solver";
     "-hoice-bin", Arg.Set_string Flag.Refine.hoice,
                   Format.sprintf "<cmd>  Change hoice command to <cmd> (default: \"%s\")" !Flag.Refine.hoice;
     "-z3", Arg.Unit Flag.(fun () -> Refine.(solver := Z3)), " Use Z3 as the recursive horn-clause solver";
     "-z3-bin", Arg.Set_string Flag.Refine.z3,
                Format.sprintf "<cmd>  Change z3 command to <cmd> (default: \"%s\")" !Flag.Refine.z3;
     "-z3-spacer", Arg.Unit Flag.(fun () -> Refine.(solver := Z3_spacer)), " Use Z3 (Spacer) as the recursive horn-clause solver";
     "-z3-spacer-bin", Arg.Set_string Flag.Refine.z3_spacer,
                   Format.sprintf "<cmd>  Change z3-spacer command to <cmd> (default: \"%s\")" !Flag.Refine.z3_spacer]
  in
  let smt =
    "Options for SMT solver",
    ["-cvc3-bin", Arg.Set_string Flag.External.cvc3,
                  Format.sprintf "<cmd>  Change cvc3 command to <cmd> (default: \"%s\")" !Flag.External.cvc3]
  in
  let fair_termination =
    "Options for fair termination mode",
    ["-fair-termination", Arg.Unit Flag.(fun () -> Method.mode := Flag.Method.FairTermination), " Check fair termination";
     "-expand-set-flag", Arg.Set Flag.FairTermination.expand_set_flag, ""]
  in
  let termination =
    "Options for termination mode",
    ["-termination-disj",
       Arg.Unit Flag.(fun _ ->
                      Method.mode := Method.Termination;
                      Termination.disjunctive := true),
       " Check termination by finding disjunctive well-founded relation";
     "-termination",
       Arg.Unit Flag.(fun _ -> Method.(mode := Termination)),
       " Check termination";
     "-termination-sep",
       Arg.Unit Flag.(fun _ ->
                      Method.mode := Method.Termination;
                      Termination.separate_pred := true),
       " Check termination with separating {decrease, boundedness} verification";
     "-termination-split-callsite",
       Arg.Unit Flag.(fun _ ->
                      Method.mode := Method.Termination;
                      Termination.split_callsite := true),
       " Check termination for each callsite of functions";
     "-add-cd",
       Arg.Set Flag.Termination.add_closure_depth,
       " Insert extra parameters for representing depth of closures";
     "-infer-ranking-exparam",
       Arg.Set Flag.Termination.add_closure_exparam,
       " Infer extra ranking parameters for closures for termination verification";
     "-non-termination",
       Arg.Unit Flag.(fun _ ->
                      Method.mode := Method.NonTermination;
                      ModelCheck.church_encode := true;
                      ModelCheck.mc := ModelCheck.HorSat),
       " Check non-termination"]
  in
  let non_termination =
    "Options for non-termination mode",
     ["-merge-paths",
       Arg.Set Flag.NonTermination.merge_paths_of_same_branch,
       " Merge predicates of paths that have same if-branch information";
     "-refinement-log",
       Arg.Set Flag.NonTermination.randint_refinement_log,
       " Write refinement types into log file (./refinement/[input file].refinement)";
     "-no-use-omega",
       Arg.Clear Flag.NonTermination.use_omega,
       " Do not use omega solver for under-approximation";
     "-use-omega-first",
       Arg.Set Flag.NonTermination.use_omega_first,
       " Preferentially use omega solver for under-approximation\n(if failed, we then check with z3)"]
  in
  let fair_non_termination =
    "Options for fair non-termination mode",
    ["-fair-non-termination",
       Arg.Unit Flag.(fun _ ->
                      Method.mode := Method.FairNonTermination;
                      ModelCheck.church_encode := true;
                      ModelCheck.mc := ModelCheck.HorSatP),
       " Check fair-non-termination";
     "-expand-ce-iter-init",
       Arg.Set_int Flag.FairNonTermination.expand_ce_iter_init,
       " Set the initial interaction count of counterexample expansion";
     "-expand-ce-count",
       Arg.Set_int Flag.FairNonTermination.expand_ce_iter_init,
       " Same as -expand-ce-iter-init";
     "", Arg.Unit ignore, "Other_options"]
  in
  align_spec
    [general;
     debug;
     experiment;
     abstraction;
     completion;
     printing;
     preprocessing;
     verification;
     modular;
     cegar;
     relative_complete;
     predicate_abstraction;
     homc;
     predicate_discovery;
     smt;
     fair_termination;
     termination;
     non_termination;
     fair_non_termination]

and print_option_and_exit () =
  arg_spec true
  |> Arg.filter_out_desc
  |> List.map Triple.fst
  |> List.iter @@ Format.printf "%s@.";
  exit 0
let arg_spec = arg_spec false

let set_file name =
  let name' =
    match !Flag.pp with
    | None -> name
    | Some pp ->
        let name' = Filename.change_extension name "pml" in
        ignore @@ Sys.command @@ Format.sprintf "%s %s -o '%s'" pp name name';
        name'
  in
  Flag.Input.(filenames := name' :: !filenames)

let parse_arg_list has_head args =
  Arg.current := 0;
  try
    let args' = if has_head then args else Sys.argv.(0) :: args in
    Arg.parse_argv (Array.of_list args') arg_spec set_file usage
  with
  | Arg.Bad s
  | Arg.Help s -> Format.eprintf "%s@." s; exit 1
  | End_of_file -> ()

let read_option_conf () =
  try
    let args = IO.CPS.open_in "option.conf" (input_line |- String.split_blanc) in
    parse_arg_list false args;
    Flag.Log.args := !Flag.Log.args @ args
  with
  | End_of_file -> ()
  | Sys_error _ -> ()

let parse_arg () =
  Arg.parse arg_spec set_file usage;
  Flag.Log.args := Array.to_list Sys.argv;
  if not !Flag.Mode.ignore_conf then read_option_conf ()
