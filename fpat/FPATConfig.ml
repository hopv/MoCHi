open Util
open Combinator

(** FPAT Configuration *)

let _ =
  HCCSSolver.ext_of_string :=
    (function
      (* PPDP 2009 *)
      | "it" -> BwIPHCCSSolver.solve
      (* PEPM 2013 *)
      | "git" -> GenHCCSSolver.solve (CHGenInterpProver.interpolate false)
      | "gch" -> GenHCCSSolver.solve (CHGenInterpProver.interpolate true)
      (* others *)
      | "lb" -> FwHCCSSolver.solve_simp
      | "pdr" -> HCCSSolver.solve_pdr
      | "dual" -> HCCSSolver.solve_duality
      | _ -> raise Not_found)


let usage =
  (*"FPAT: A Framework for Program Analysis and Transformation\n\n" ^*)
  "Usage: "
  ^ Sys.executable_name
  ^ " <options> <files>\noptions are:"
let tabs = "\t\t\t\t"
let arg_spec =
  ["-silent", Arg.Set Global.silent, " Enable silent mode";
   "-bench", Arg.Set Global.bench_mode, " Enable benchmark mode";
   "-timeout", Arg.Int (fun n -> Global.timeout := n), "<n> Set timeout (sec)";
   (* debugging *)
   "-debug", Arg.Set Global.debug, " Enable debug mode";
   "-debug-regexp", Arg.String (fun str -> Global.debug := true;
                                 Logger.filter_regexp := Str.regexp str),
     "<regexp> Enable debug mode (only log calls that match <regexp> and their ancestor calls)";
   "-debug-regexp-exact", Arg.String (fun str -> Global.debug := true;
                                       Logger.filter_exact := true;
                                       Logger.filter_regexp := Str.regexp str),
     "<regexp> Enable debug mode (only log calls that match <regexp>)";
   "-debug-call-id", Arg.Int (fun n -> Global.debug := true;
                               Logger.filter_call_id := n),
     "<n> Enable debug mode (only log calls that match call_id <n> and their ancestor calls)";
   "-debug-call-id-exact", Arg.Int (fun n -> Global.debug := true;
                                     Logger.filter_exact := true;
                                     Logger.filter_call_id := n),
     "<n> Enable debug mode (only log calls that match call_id <n>)";
   "-debug-level", Arg.Int (fun n -> Global.debug_level := n),
     "<n> Set debug level";
   "-profile", Arg.Unit (fun () -> Global.debug := true;
                          Logger.filter_kinds := [Logger.Trace]),
     " Enable profiling mode";
   "-print-log", Arg.Set Global.print_log,
     " Print log messages to the standard output";
   "-disable-print-callstack-exception",
     Arg.Clear Logger.print_call_stack_on_exception,
     " Disable printing the call stack when an exception is occurred";
   (* options for program verification *)
   (* HCCS solvers *)
   "-hccs", Arg.String (fun str ->
       try HCCSSolver.of_string_dyn str |> HCCSSolver.link_dyn
       with Not_found -> raise (Arg.Bad "invalid argument for -hccs")),
     "<n> Use an HCCS solver based on\n"
     (* FLOPS 2008 *)
     ^ tabs ^ "qe: top-down iterative quantifier elimination\n"
     (* PPDP 2009 *)
     ^ tabs ^ "it: top-down iterative interpolation\n"
     (* PEPM 2013 *)
     ^ tabs ^ "git: generalized interpolation\n"
     ^ tabs ^ "gch: generalized interpolation using convex hull\n"
     (* others *)
     ^ tabs ^ "lb: bottom-up iterative propagation\n"
     ^ tabs ^ "uoa: unwinding + iterative under/over approximation\n"
     ^ tabs ^ "pdr: PDR on Z3 (muZ)\n"
     ^ tabs ^ "dual: duality on Z3 (muZ)";
   (* options for HCCS solvers *)
   "-l2r", Arg.Set BwIPHCCSSolver.solve_body_left_to_right,
     " Incrementally solve the body of each HCCS from left to right (it)";
   "-disable-interp-simp", Arg.Clear InterpProver.interp_simplify,
     " Disable simplification of interpolants and HCCS solutions (it)";
   "-fol-bw", Arg.Set FwHCCSSolver.fol_backward,
     " use backward transformation of HCCSs to FOL formulas (lb)";
   "-numconj", Arg.Set_int Template.num_conj,
     " The number of conjuncts (tb)";
   "-numdisj", Arg.Set_int Template.num_disj,
     " The number of disjuncts (tb)";
   "-lin-template", Arg.Set Template.linear_farkas,
     " Enable linear constraint solving (tb)";
   "-disable-ray", Arg.Set Polyhedron.disable_ray,
     " Disable ray counterexample sampling (expsb)";
   "-enable-pol", Arg.Set Polyhedron.enable_pol,
     " Enable polytope counterexample sampling instead of point (expsb)";
   "-disable-conj", Arg.Set HornClause.disable_conj,
     " Disable conj (expsb)";
   (* HCCS simplification *)
   "-res-inc", Arg.Set HCCS.resolve_inc, " resolve HCCSs incrementally";
   "-disable-pred-share1", Arg.Set PvaCube.disable_pred_sharing1,
     " an option for HCCS simplification?";
   "-enable-pred-share2", Arg.Set PvaCube.enable_pred_sharing2,
     " an option for HCCS simplification?";
   "-disable-elim-lt-gt", Arg.Set CunAtom.disable_elim_lt_gt,
     " Disable elimination of LessThan and GreaterThan for QFLIA";
   (* interpolating provers *)
   "-interp", Arg.String ((function
       | "csisat" -> InterpProver.interpolate_csisat_dyn
       | "csisatgen" -> InterpProver.interpolate_csisat_gen_dyn
       | "z3" -> InterpProver.interpolate_z3_dyn
       | _ -> raise (Arg.Bad "invalid argument for -interp"))
      >> InterpProver.link_dyn),
     "<n> Use an interpolating prover based on\n"
     ^ tabs ^ "csisat: CSIsat\n"
     ^ tabs ^ "csisatgen: CSIsat + generalization heuristics\n"
     ^ tabs ^ "z3: Z3\n"
     ^ tabs ^ "tb: templated-based synthesis\n"
     ^ tabs ^ "expsb: extremal point sampling\n"
     ^ tabs ^ "psb: point sampling";
   (* options for interpolating provers *)
   "-degree", Arg.Int (fun d -> InterpProver.degree := d; Template.degree := d),
     " Set the degree of interpolants";
   (* SMT solvers *)
   "-smt", Arg.String (function
       | "z3" -> SMTProver.init_z3 ()
       | "cvc3" -> SMTProver.init_cvc3 ()
       | _ -> raise (Arg.Bad "invalid argument for -smt")),
     "<n> Specify an SMT solver\n"
     ^ tabs ^ "z3: Z3\n"
     ^ tabs ^ "cvc3: CVC3";
   (* options for SMT solvers *)
   "-print-z3", Arg.Set SMTProver.print_z3, " Print Z3 input";
   "-timeout-z3", Arg.Int (fun n -> Global.timeout_z3 := n * 1000),
     "<n> Set timeout for Z3 (sec) (default: 60 sec)";
   (* polynomial constraint solvers *)
   "-pc", Arg.String (function
       | "z3" -> PolyConstrSolver.ext_solve := PolyConstrSolver.solve_z3
       | "cvc3" -> PolyConstrSolver.ext_solve := PolyConstrSolver.solve_cvc3
       (* use PolyConstrSolver.gen_coeff_constr ~pos:true ~linear:true *)
       | _ -> raise (Arg.Bad "invalid argument for -template")),
     "<n> Specify a polynomial constraint solver\n"
     ^ tabs ^ "z3: Z3\n"
     ^ tabs ^ "cvc3: CVC3\n"
     ^ tabs ^ "bb: bit-blasting\n"
     ^ tabs ^ "cad: QECAD";
   (* options for polynomial constraint solvers *)
   "-enable-lang-restrict", Arg.Set PolyConstrSolver.enable_lang_restrict,
     " Enable L-restriction";
   "-use-ineq", Arg.Set PolyConstrSolver.lang_restrict_use_inequality,
     " Use inequalities in L-restriction";
   "-tlr", Arg.Set_int PolyConstrSolver.lang_restrict_threshold,
     " Threshold of the absolute value of coefficients in L-restriction";
   (* options for forall-exists HCCS solvers *)
   (* options for exists-forall HCCS solvers *)
   "-lin-eahccs", Arg.Set EAHCCSSolver.linear_farkas,
     " Enable linear constraint solving for EHCCS solving";
   "-aec", Arg.Set EAHCCSSolver.accumulate_ext_constrs,
     " Accumulate the constraints in EAHCCS solving";
   "-no-cmask", Arg.Clear PolyConstrSolver.mask_coeffs,
     " Not to mask coefficients in EAHCCS solving";
   (* options for ranking function synthesis *)
   "-rank-widen", Arg.Set RankFunInfer.rank_widen,
     " Use widening for ranking function synthesis";
   "-lex", Arg.Int (fun n -> RankFun.num_rankfuns := n),
     " Number of ranking functions (deprecated)";
   "-llrf", Arg.Int (fun n -> RankFun.num_rankfuns := n),
   "<n> Use lexicographic linear ranking functions";
   (* refinement type inference *)
   "-disable-inlining", Arg.Set RefTypInfer.no_inlining,
     " Disable HCCS inlining";
   "-cpo", Arg.Set RefTypInfer.cut_points_only,
     " Find good predicates for cut-points";
   (* relatively-complete refinemenet type inference *)
   "-nex", Arg.Set_int RefTypInfer.number_of_extra_params,
     " Number of inserted extra parameters for each functional argument";
   "-cc", Arg.Set RefTypInfer.enable_coeff_const,
     " Enable constant terms of extra parameters";
   "-flag-coeff", Arg.Set RefTypInfer.flag_coeff,
     " an option for EAHCCS generation?";
   (* abstraction type inference *)
   "-split-eq", Arg.Set AbsType.split_equalities,
     " Split equalities";
   "-eap", Arg.Set AbsType.extract_atomic_predicates,
     " Extract atomic predicates";
   (* predicate abstraction *)
   "-use-cfp", Arg.Set PredAbst.use_cfp,
     " Use constraint fixpoint computation for predicate abstraction";
   "-wp-max", Arg.Set_int PredAbst.wp_max_num,
     "<n> The maximum dimension of hypercubes in predicate abstraction";
   "-neg-pred", Arg.Set PredAbst.use_neg_pred,
     " Use negative predicates for abstraction";
   "-no-opt", Arg.Clear PredAbst.incomplete_opt,
     " Disable an (incomplete) optimization of predicate abstraction";
  ]



let set_default () =
  (* default SMT solver *)
  SMTProver.init_z3 ();
  (* default polynomial constraint solver *)
  PolyConstrSolver.ext_solve := PolyConstrSolver.solve_z3;
  (* default interpolating prover *)
  InterpProver.link_dyn InterpProver.interpolate_csisat_dyn;
  (* default HCCS solver *)
  HCCSSolver.link_dyn BwIPHCCSSolver.solve;
  (* default unit, bool, and tuple HCCS encoders *)
  HCCSSolver.ext_solve_unit := UnitHCCSSolver.solve;
  HCCSSolver.ext_solve_bool := id
let set_default =
  (* this is not printed because !Global.debug is false *)
  Logger.log_block1 "FPATConfig.set_default" set_default

let is_fpat_exception = function
  | Global.NotImplemented _
  | Global.NoMatch _
  (*| SMTProver.Unsat*)
  | SMTProver.Unknown
  (*| InterpProver.NoInterpolant*)
  | InterpProver.Fail
  | InterpProver.Unknown
  (*| PolyConstrSolver.NoSolution*)
  | PolyConstrSolver.Unknown
  | RefTypInfer.FailedToRefineTypes
  | RefTypInfer.FailedToRefineInputTypes
  | RefTypInfer.FailedToRefineExtraParameters -> true
  | _ -> false

let pr_exception ppf = function
  | Global.NotImplemented msg -> Format.fprintf ppf "Not implemented: %s" msg
  | Global.NoMatch msg -> Format.fprintf ppf "Not matched: %s" msg
  | SMTProver.Unknown -> Format.fprintf ppf "Failure of SMT prover"
  | InterpProver.Fail ->
    Format.fprintf ppf
      "Failure of interpolating prover (integer domain not fully supported)"
  | InterpProver.Unknown ->
    Format.fprintf ppf "Failure of interpolating prover"
  | PolyConstrSolver.Unknown ->
    Format.fprintf ppf "Failure of polynomial constraint solver"
  | RefTypInfer.FailedToRefineTypes ->
    Format.fprintf ppf "Failure of abstraction type refinement"
  | RefTypInfer.FailedToRefineInputTypes ->
    Format.fprintf ppf
      "Failure of abstraction type refinement of external inputs"
  | RefTypInfer.FailedToRefineExtraParameters ->
    Format.fprintf ppf "Failure of parameter substitution refinement"
  | _ -> raise Not_found

let string_of_fpat_exception = Printer.string_of pr_exception
