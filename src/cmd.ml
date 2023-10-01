open Util
open Mochi_util

let print_env ~cmd ~json =
  let mochi = Revision.mochi in
  let z3_lib = Z3.Version.full_version in
  let z3_bin = Option.map (fun z3 -> String.trim @@ Unix.CPS.open_process_in (z3 ^ " -version") IO.input_all) Mconfig.z3 in
  let trecs = TrecsInterface.version () in
  let horsat = HorSatInterface.version () in
  let horsat2 = HorSat2Interface.version () in
  let horsatp = HorSatPInterface.version () in
  let hoice = Option.map (fun hoice -> List.nth (String.split_blanc @@ Unix.CPS.open_process_in (hoice ^ " -V") IO.input_all) 1) Mconfig.hoice in
  let pr fm = Format.fprintf !Flag.Print.target fm in
  if json then
    let of_option s x = Option.fold ~none:[] ~some:(fun ver -> [s, `String ver]) x in
    let assoc =
      of_option "Build" mochi @
      ["Z3 library", `String z3_lib] @
      of_option "Z3 binary" z3_bin @
      of_option "TRecS" trecs @
      of_option "HorSat" horsat @
      of_option "HorSat2" horsat2 @
      of_option "HorSatP" horsatp @
      of_option "HoIce" hoice @
      ["OCaml", `String Sys.ocaml_version]
    in
    `Assoc assoc
    |> JSON.to_string
    |> pr "%s"
  else
    begin
      Color.fprintf !Flag.Print.target Green "MoCHi: Model Checker for Higher-Order Programs@.";
      Option.iter (pr "  Build: %s@.") mochi;
      pr "  Z3 library version: %s@." z3_lib;
      Option.iter (pr "  Z3 binary: %s@.") z3_bin;
      Option.iter (pr "  TRecS version: %s@.") trecs;
      Option.iter (pr "  HorSat version: %s@.") horsat;
      Option.iter (pr "  HorSat2 version: %s@.") horsat2;
      Option.iter (pr "  HorSatP version: %s@.") horsatp;
      Option.iter (pr "  HoIce version: %s@.") hoice;
      pr "  OCaml version: %s@." Sys.ocaml_version;
      if cmd then
        !Flag.Log.args
        |> List.map (fun s -> if String.contains s ' ' then Format.sprintf "'%s'" s else s)
        |> String.join " "
        |> pr "  Command: %s@.@."
    end

let just_run_other_command cmd =
  if !Flag.IO.filenames = [] then
    (Format.eprintf {|Option "-just-run" must follow input file@.|}; exit 1);
  let filename = List.hd !Flag.IO.filenames in
  let total,r = Time.measure (fun () -> Sys.command @@ snd @@ String.replace ~str:cmd ~sub:"%i" ~by:filename) in
  let result = if r = 0 then "Safe" else "Error" in
  `Assoc ["filename", `String filename; "result", `String result; "total", `Float total]
  |> JSON.to_string
  |> Format.fprintf !Flag.Print.target "%s@.";
  exit r

let align_spec specs =
  specs
  |> List.flatten_map (fun (desc,spec) -> ("", Arg.Unit ignore, desc)::spec)
  |> Arg.align

let set_bin name r =
  let default = Option.map_default (Format.sprintf {| (default: "%s"|}) "" !r in
  Format.sprintf "-%s-bin" name,
  Arg.String (fun s -> r := Some s),
  Format.sprintf {|<cmd>  Change %s command to <cmd>%s|} name default

let rec spec_general =
  "General options",
  ["-I", Arg.String Parser_wrapper.add_load_path,
   "<dir>  Add <dir> to the list of include directories";
   "-margin", Arg.Int Format.set_margin, "<n>  Set pretty printing margin";
   "-only-result", Arg.Unit set_only_result, " Show only result";
   "-color", Arg.Set Flag.PrettyPrinter.color, " Turn on syntax highlighting";
   "-no-color", Arg.Clear Flag.PrettyPrinter.color, " Turn off syntax highlighting";
   "-color-always", Arg.Set Flag.PrettyPrinter.color_always, " Turn on syntax highlighting even if stdout does not refer to a terminal";
   "-ignore-conf", Arg.Unit Flag.IO.(fun () -> if !conf_file = conf_file_default then conf_file := ""), " Ignore option.conf";
   "-ignore-inc", Arg.Set Flag.IO.ignore_inc, " Ignore *.inc";
   "-ignore-inc", Arg.Set Flag.IO.ignore_lib, " Ignore *.lib";
   "-config", Arg.Set_string Flag.IO.conf_file, "<filename>  Use <filename> as config file";
   "-v", Arg.Unit (fun () -> print_env ~cmd:false ~json:false; exit 0), " Print the versions";
   "-env", Arg.Unit (fun () -> print_env ~cmd:false ~json:true; exit 0), " Print the version and the environment as JSON";
   "-version", Arg.Unit (fun () -> print_env ~cmd:false ~json:false; exit 0), " Same as -v";
   "-limit", Arg.Set_int Flag.Limit.time, " Set time limit (seconds)";
   "-limit-sub", Arg.Set_int Flag.Limit.time_subproblem, " Set time limit for each sub-problem (seconds)";
   "-limit-par", Arg.Set_int Flag.Parallel.time, " Set time limit for parallel execution (seconds)";
   "-pp", Arg.String (fun pp -> Flag.pp := Some pp), " Set preprocessor command";
   "-web", Arg.Set Flag.PrettyPrinter.web, " Web mode";
   "-rand-self-init", Arg.Unit Random.self_init, " Initialize the random seed";
   "-use-temp", Arg.Set Flag.use_temp, " Use temporary files for intermediate/log files";
   "-trans",
     Arg.String Flag.(fun s -> mode := Trans;
                               Trans.set_trans s;
                               set_only_result ()),
     Format.asprintf "<dest>  Translate the input to <dest> which must be one of the following:\n%s"
       !!Flag.Trans.string_of_destinations;
   "-chc", Arg.Set Flag.Method.chc, " CHC solving mode";
   "-p", Arg.Set_int Flag.Parallel.num, "<n>  Numbers of jobs to run simultaneously";
   "-s", Arg.Unit set_silent, " Do not print information to stdout except in some printing options "]

and spec_debug =
  "Debug options",
  ["-debug", Arg.String Flag.Debug.set_debug_modules, "<modules>  Set debug flag of modules (comma-separated)";
   "-stop-after", Arg.Set_string Flag.Preprocess.stop_after, "<label>";
   "-check-after", Arg.String Flag.Preprocess.(fun s -> check_flag := false; check_after := s), "<label>";
   "-input-cex", Arg.Set Flag.Debug.input_cex, " Input counterexamples by hands";
   "-minimize", Arg.Set Flag.Debug.minimize, "<error>  Minimize erroneous input"]

and spec_experiment =
  let module Q = Flag.Experiment.HORS_quickcheck in
  "Options for experiments",
  ["-just-run", Arg.String just_run_other_command, " (just for experiments, %i is replaced with the filename)";
   "-hors-quickcheck-short", Arg.Unit Q.(fun () -> use := Some Shortest), " Use shortest counterexample generated by hors_quickcheck";
   "-hors-quickcheck-long", Arg.Unit Q.(fun () -> use := Some Longest), " Use longest counterexample generated by hors_quickcheck";
   "-hors-quickcheck-low", Arg.Unit Q.(fun () -> use := Some LowestCoverage), " Use lowest coverage counterexample generated by hors_quickcheck";
   "-hors-quickcheck-high", Arg.Unit Q.(fun () -> use := Some HighestCoverage), " Use highest coverage counterexample generated by hors_quickcheck";
   "-spawn", Arg.Set Flag.Experiment.spawn, " Spawn new process for each sub-problems"]

and spec_abstraction =
  let module A = Flag.Abstract in
  "Options for abstraction",
  ["-ignore-exn-arg", Arg.Set A.ignore_exn_arg, " Ignore exception arguments";
   "-ignore-data-arg", Arg.Set A.ignore_data_arg, " Ignore constructor arguments";
   "-abst-literal", Arg.Set_int A.literal, " Abstract literals";
   "-abst-list-eq", Arg.Set A.list_eq, " Abstract list equalities";
   "-no-abst-list-eq", Arg.Clear A.list_eq, " Do not abstract list equalities";
   "-ignore-non-termination", Arg.Set Flag.Method.ignore_non_termination, " Ignore non-termination";
   "-abst-exn", Arg.Set A.exn_to_bool, " Abstract exceptions to Booleans"]

and spec_completion =
  "Options for completion",
  ["-option-list", Arg.Unit print_option_and_exit, " Print list of options";
   "-debug-list", Arg.Unit (fun () -> List.iter (Format.fprintf !Flag.Print.target "%s@.") !Flag.Debug.debuggable_modules; exit 0), " Print list of debug options";
   "-prep-list",
     Arg.Unit (fun () ->
         let pr_prep (_,(descr,_)) = Format.fprintf !Flag.Print.target "%s@." descr in
         List.iter pr_prep !!Preprocess.all;
         exit 0),
     " Print list of preprocess";
   "-trans-list", Arg.Unit (fun () -> List.iter (Format.fprintf !Flag.Print.target "%s@.") @@ List.map fst Flag.Trans.destinations; exit 0), " Print list of -trans destinations"]

and spec_printing =
  let module P = Flag.Print in
  "Options for printing",
  ["-o", Arg.String set_print_target, "<logfile>  Log all messages to logfile";
   "-print-abst-types", Arg.Set P.abst_typ, " Print abstraction types when the program is safe";
   "-print-as-ocaml", Arg.Unit Print.set_as_ocaml, " Print terms in OCaml syntax";
   "-print-progress", Arg.Set P.progress, " Print progress (use after -modular/-imodular)";
   "-print-unused-arg", Arg.Unit Print.set_unused, " Print unused arguments";
   "-print-cert", Arg.Set P.certificate, " Print certificates even if the model checker does not support certificates (need TRecS)";
   "-print-depth", Arg.Int Print.set_depth, "<n>  Limit the printing of terms/types to a maximal depth of n";
   "-print-length", Arg.Int Print.set_length, "<n>  Limit the printing of sequence of term/types to a maximal length of n";
   "-print-assert-location", Arg.Unit (fun () -> P.assert_loc := true; P.exit_after_parsing := true), " Print the locations of assertions (used for -target)";
   "-print-id-location", Arg.String (fun s -> P.id_loc := s; P.exit_after_parsing := true), {|<var>  Print the locations of <var> (used for "external" in spec)|};
   "-print-signature", Arg.Set P.signature, " Print module signatures";
   "-print-variable-id", Arg.Set P.var_id, " Print varible ids always";
   "-print-exception", Arg.Unit (fun () -> P.exn := true; P.exit_after_parsing := true), " (for experiments)"]

and spec_preprocessing =
  "Options for preprocessing",
  ["-fail-as-excep", Arg.Set Flag.Method.fail_as_exception, " Treat fail as an exception";
   "-replace-const", Arg.Set Flag.Method.replace_const, " Replace unchanging variables with constants";
   "-no-exparam", Arg.Set Flag.Method.no_exparam, " Do not add extra parameters";
   "-use-exparam", Arg.Clear Flag.Method.no_exparam, " Add extra parameters when CEGAR fails";
   "-list-option", Arg.Set Flag.Encode.encode_list_opt, " Encode list using options not pairs";
   "-disable-preprocess", Arg.Clear Flag.Method.init_trans, " Disable encoding of recursive data structures, CPS transformation, etc.";
   "-lift-fv", Arg.Set Flag.Method.lift_fv_only, " Lift variables which occur in a body";
   "-cps-naive", Arg.Set Flag.Method.cps_simpl, " Use naive CPS transformation";
   "-ins-param-funarg", Arg.Set Flag.Method.insert_param_funarg, " Insert an extra param for functions with function arguments";
   "-tupling", Arg.Unit Flag.Method.(fun () -> tupling := not !tupling), " Toggle tupling";
   "-elim-same-arg", Arg.Set Flag.Method.elim_same_arg, " Eliminate same arguments";
   "-base-to-int", Arg.Set Flag.Abstract.base_to_int, " Replace primitive base types with int";
   "-list-to-int", Arg.Set Flag.Abstract.list_to_int, " Replace lists with int";
   "-data-to-int", Arg.Set Flag.Abstract.data_to_int, " Replace data types with int";
   "-data-to-int-but-exn", Arg.Set Flag.Abstract.data_to_int_but_exn, " Replace data types with int except exceptions";
   "-bool-to-int", Arg.Set Flag.Encode.bool_to_int, " Encode booleans into integers";
   "-exn-to-bool", Arg.Set Flag.Abstract.exn_to_bool, " Replace exceptions with int";
   "-encode-before-make-ext-fun", Arg.Set Flag.Method.encode_before_make_ext_fun, " Encode before make external functions";
   "-make-ext-fun-before-encode", Arg.Clear Flag.Method.encode_before_make_ext_fun, " Make external functions before encode (BUGGY)";
   "-no-slice", Arg.Clear Flag.Method.slice, " Do not slice";
   "-slice-exp", Arg.Set_int Flag.Method.slice_i, " (just for debug)";
   "-slice-target", Arg.Set_string Flag.Method.slice_target, " (just for debug)";
   "-reduce-memory", Arg.Set Flag.Preprocess.reduce_memory, " Reduce memory usage in preprocess. This disables some features.";
   "-save-preprocess", Arg.Set Flag.Preprocess.save_preprocess, " Save each step of preprocess to restart (DOES NOT WORK)";
   "-restart", Arg.Set Flag.Preprocess.restart_preprocess, " Restart from preprocess (DOES NOT WORK)";
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
                              5, "unit * ty * (int list -> ty) whene ty = Leaf | Node of int"];
   "-use-elim-may-div", Arg.Set Flag.Method.use_elim_may_div, " Eliminate unused let-bindings that may diverge"]

and spec_verification =
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
                    Modular.infer_ind := true;
                    PredAbst.shift_pred := false),
     " Modular verification (inductive mode)";
   "-verify-ref-typ", Arg.Unit (fun () -> Flag.(mode := Verify_ref_typ)), " Verify whether functions have given refinement types";
   "-spec", Arg.Set_string Flag.IO.spec, "<filename>  use <filename> as a specification";
   "-use-spec", Arg.Set Flag.Method.use_spec, " use XYZ.spec for verifying XYZ.ml if exists\n(This option is ignored if -spec is used)";
   "-disable-comment-spec", Arg.Clear Flag.Method.comment_spec, " disable {SPEC} on comments";
   "-ignore-comment-spec", Arg.Clear Flag.Method.comment_spec, " same as -disable-comment-spec";
   "-module-verification", Arg.Unit (fun () -> Flag.(mode := Verify_module)), " Check input as library";
   "-quickcheck", Arg.Unit (fun () -> Flag.(mode := Quick_check)), " Disprove safety via QuickCheck (other method options will be ignored)";
   "-only-specified", Arg.Set Flag.Method.only_specified, " Verify only specified targets";
   "-target", Arg.String (fun s -> Flag.Method.(targets := s::!targets); Flag.Method.only_specified := true),
     "<location>  Verify only assertions matched with <location> (Use -print-assert-location)";
   "-target-exn", Arg.String (fun s -> Flag.Method.(target_exn := s::!target_exn); Flag.Method.only_specified := true),
     "<exception>  Verify only uncaght-exception <exception>";
   "-sub", Arg.Set Flag.Method.sub, " Verify sub-programs";
   "-verify-ref-interface", Arg.Set Flag.Method.verify_ref_interface, " Verify refinement type interface";
   "-set-theory",
     Arg.Unit (fun () -> Flag.Method.use_set_theory := true;
                         Flag.Refine.use_rec_chc_solver := false;
                         FpatInterface.parse_arg "-set-theory"),
     " (Use after -fpat option)"]

and spec_modular =
   "Options for Modular Verification",
   ["-check-simple", Arg.Set Flag.Modular.check_simple, " Use simple refinement checking"]

and spec_cegar =
  "Options for CEGAR",
  ["-split-assert", Arg.Set Flag.Method.split_assert, " Reduce to verification of multiple programs\n(each program has only one assertion)";
   "-disable-predicate-accumulation", Arg.Set Flag.Refine.disable_predicate_accumulation, " Disable predicate accumulation"]

and spec_relative_complete =
  "Options for relatively complete verification",
  ["-relative-complete", Arg.Set Flag.Method.relative_complete, " Enable relatively complete verification from the begining"]

and spec_predicate_abstraction =
  let module P = Flag.PredAbst in
  "Options for predicate abstraction",
  ["-abs-remove-false", Arg.Set P.remove_false, " Do not use unsatisfiable predicates in abstraction";
   "-no-enr", Arg.Unit P.(fun () -> expand_non_rec := false; expand_non_rec_init := false), " Do not expand non-recursive functions";
   "-enr", Arg.Unit P.(fun () -> expand_non_rec := true; expand_non_rec_init := false),
           " Expand non-recursive functions except those in the original program";
   "-abs-filter", Arg.Set P.use_filter, " Turn on the abstraction-filter option";
   "-neg-pred-off", Arg.Set P.never_use_neg_pred, " Never use negative predicates for abstraction";
   "-decomp-pred", Arg.Set P.decomp_pred, " Decompose abstraction predicates (e.g., [P1 && P2] ==> [P1, P2])";
   "-decomp-eq-pred", Arg.Set P.decomp_eq_pred, " Decompose abstraction predicates on equalities (e.g., [t1 = t2] ==> [t1 <= t2, t1 >= t2])";
   "-no-shift-pred", Arg.Clear P.shift_pred, " Disable -shift-pred";
   "-shift-pred", Arg.Set P.shift_pred, " Set predicates true for safe function arguments";
   "-non-cartesian", Arg.Clear P.cartesian, " Do non-cartesian abstraction"]

and spec_homc =
  let module M = Flag.ModelCheck in
  "Options for model checking",
  ["-rename-hors", Arg.Set M.rename_hors, " Set different name to each hors file";
   "-ea", Arg.Set Flag.Print.eval_abst, " Print evaluation of abstacted program";
   "-bool-church", Arg.Set M.church_encode, " Use church-encoding for model checking";
   "-trecs", Arg.Unit (fun () -> Model_check.use TRecS), " Use TRecS as the model checker";
   "-horsat", Arg.Unit (fun () -> Model_check.use HorSat), " Use HorSat as the model checker";
   "-horsat2", Arg.Unit (fun () -> Model_check.use HorSat2), " Use HorSat2 as the model checker";
   set_bin "trecs" M.trecs;
   set_bin "horast" M.horsat;
   set_bin "horsat2" M.horsat2;
   set_bin "horsatp" M.horsatp]

and spec_predicate_discovery =
  let module R = Flag.Refine in
  "Options for predicate discovery",
  ["-fpat", Arg.String FpatInterface.parse_arg, "<option>  Pass <option> to FPAT";
   "-bool-init-empty", Arg.Set Flag.PredAbst.bool_init_empty,
     " Use an empty set as the initial sets of predicates for booleans";
   "-bool-init-self", Arg.Clear Flag.PredAbst.bool_init_empty,
     " Use predicates of themselves as the initial sets of predicates for booleans";
   "-mp", Arg.Set R.use_multiple_paths, " Use multiple infeasible error paths for predicate discovery";
   "-no-simplification", Arg.Set Flag.PredAbst.no_simplification, " Do not simplify abstracted programs";
   "-no-rec-chc", Arg.Clear R.use_rec_chc_solver, " Do not use recursive CHC solver";
   "-rec-chc", Arg.Set R.use_rec_chc_solver, " Use recursive CHC solver";
   "-rec-chc-limit", Arg.Set_int R.solver_timelimit, " Set time limit for recursive CHC solver (seconds)";
   "-rec-chc-app-id", Arg.Set Flag.Method.occurence_param, " Add extra parameter for application ID";
   "-hoice", Arg.Unit R.(fun () -> solver := Hoice), " Use HoICE as the recursive horn-clause solver";
   set_bin "hoice" R.hoice;
   "-z3", Arg.Unit (fun () -> R.(solver := Z3)), " Use Z3 as the recursive horn-clause solver";
   set_bin "z3" R.z3;
   "-z3-spacer", Arg.Unit R.(fun () -> solver := Z3_spacer), " Use Z3 (Spacer) as the recursive horn-clause solver";
   set_bin "z3" R.z3_spacer]

and spec_smt =
  "Options for SMT solver",
  [set_bin "cvc3" Flag.External.cvc3]

and spec_fair_termination =
  "Options for fair termination mode",
  ["-fair-termination", Arg.Unit Flag.(fun () -> mode := FairTermination), " Check fair termination";
   "-expand-set-flag", Arg.Set Flag.FairTermination.expand_set_flag, ""]

and spec_termination =
  let module T = Flag.Termination in
  "Options for termination mode",
  ["-termination-disj",
     Arg.Unit Flag.(fun _ ->
                    mode := Termination;
                    T.disjunctive := true),
     " Check termination by finding disjunctive well-founded relation";
   "-termination",
     Arg.Unit Flag.(fun _ -> mode := Termination),
     " Check termination";
   "-termination-sep",
     Arg.Unit Flag.(fun _ ->
                    mode := Termination;
                    T.separate_pred := true),
     " Check termination with separating {decrease, boundedness} verification";
   "-termination-split-callsite",
     Arg.Unit Flag.(fun _ ->
                    mode := Termination;
                    T.split_callsite := true),
     " Check termination for each callsite of functions";
   "-add-cd",
     Arg.Set T.add_closure_depth,
     " Insert extra parameters for representing depth of closures";
   "-infer-ranking-exparam",
     Arg.Set T.add_closure_exparam,
     " Infer extra ranking parameters for closures for termination verification";
   "-non-termination",
     Arg.Unit (fun _ ->
               Flag.mode := NonTermination;
               Model_check.use HorSat),
     " Check non-termination"]

and spec_non_termination =
  let module N = Flag.NonTermination in
  "Options for non-termination mode",
   ["-merge-paths",
     Arg.Set N.merge_paths_of_same_branch,
     " Merge predicates of paths that have same if-branch information";
   "-refinement-log",
     Arg.Set N.randint_refinement_log,
     " Write refinement types into log file (./refinement/[input file].refinement)";
   "-no-use-omega",
     Arg.Clear N.use_omega,
     " Do not use omega solver for under-approximation";
   "-use-omega-first",
     Arg.Set N.use_omega_first,
     " Preferentially use omega solver for under-approximation\n(if failed, we then check with z3)"]

and spec_fair_non_termination =
  "Options for fair non-termination mode",
  ["-fair-non-termination",
     Arg.Unit (fun _ ->
               Flag.mode := FairNonTermination;
               Model_check.(use HorSat2)),
     " Check fair-non-termination";
   "-expand-ce-iter-init",
     Arg.Set_int Flag.FairNonTermination.expand_ce_iter_init,
     " Set the initial interaction count of counterexample expansion";
   "-expand-ce-count",
     Arg.Set_int Flag.FairNonTermination.expand_ce_iter_init,
     " Same as -expand-ce-iter-init"]

and usage =
  "MoCHi: Model Checker for Higher-Order Problems\n\n" ^
    "Usage: " ^ Sys.executable_name ^ " [options] file\noptions are:"

and arg_spec () =
  align_spec
    [spec_general;
     spec_debug;
     spec_experiment;
     spec_abstraction;
     spec_completion;
     spec_printing;
     spec_preprocessing;
     spec_verification;
     spec_modular;
     spec_cegar;
     spec_relative_complete;
     spec_predicate_abstraction;
     spec_homc;
     spec_predicate_discovery;
     spec_smt;
     spec_fair_termination;
     spec_termination;
     spec_non_termination;
     spec_fair_non_termination;
     "Other options", []]

and print_option_and_exit () =
  !!arg_spec
  |> List.map Triple.fst
  |> List.filter (fun s -> s <> "" && s.[0] = '-')
  |> List.iter @@ Format.fprintf !Flag.Print.target "%s@.";
  exit 0

let set_file name =
  let ext = Filename.extension name in
  match ext with
  | "" | ".ml" ->
      if ext = "" then warning "Treat %s as an implementation file" name;
      let name' =
        match !Flag.pp with
        | None -> name
        | Some pp ->
            let name' = Filename.change_extension name "pml" in
            ignore @@ Sys.command @@ Format.sprintf "%s %s -o '%s'" pp name name';
            name'
      in
      Flag.IO.(filenames := name' :: !filenames)
  | ".bin" | ".cegar" | ".debug" | ".smt2" ->
      if !Flag.IO.filenames <> [] then unsupported "Multiple files for *%s (only the last file is used)" ext;
      Flag.IO.(filenames := [name])
  | _ -> unsupported "File with extension %s" ext


let parse_arg_list has_head args =
  Arg.current := 0;
  try
    let args' = if has_head then args else Sys.argv.(0) :: args in
    Arg.parse_argv (Array.of_list args') !!arg_spec set_file usage
  with
  | Arg.Bad s
  | Arg.Help s -> Format.eprintf "%s@." s; exit 1
  | End_of_file -> ()
let parse_arg_list' has_head args =
    parse_arg_list has_head args;
    Flag.Log.args := !Flag.Log.args @ args

let read_option_conf filename =
  try
    let read cin =
      cin
      |> IO.input_all
      |> String.split_on_char '\n'
      |> List.filter_out (String.starts_with -$- "#")
      |> String.join " "
      |> String.split_blanc
    in
    let args = IO.CPS.open_in filename read in
    parse_arg_list' false args
  with
  | End_of_file -> ()
  | Sys_error _ -> ()

let add_includes () =
  let inc = Filename.change_extension !!Flag.IO.main "inc" in
  if Sys.file_exists inc then
    let s = IO.input_file inc in
    if String.exists_stdlib (List.mem -$- ['\\'; '\"'; '\'']) s then
      unsupported "%s" __FUNCTION__;
    let args =
      s
      |> String.replace_chars (fun c -> if Char.is_whitespace c then " " else String.of_char c)
      |> String.split_on_char ' '
      |> List.remove_all -$- ""
      |> List.flatten_map (fun dir -> ["-I"; dir])
    in
    parse_arg_list' false args

let add_lib_dir () =
  let lib = Filename.change_extension !!Flag.IO.main "lib" in
  if Sys.file_exists lib && Sys.is_directory lib then
    let args = ["-I"; lib] in
    parse_arg_list' false args

let parse_arg () =
  Arg.parse !!arg_spec set_file usage;
  Flag.Log.args := Array.to_list Sys.argv;
  if !Flag.IO.conf_file <> "" then read_option_conf !Flag.IO.conf_file;
  if not !Flag.IO.ignore_inc && !Flag.IO.filenames <> [] then add_includes ();
  if not !Flag.IO.ignore_lib && !Flag.IO.filenames <> [] then add_lib_dir ()
