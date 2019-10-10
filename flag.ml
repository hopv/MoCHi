open Util

module External = struct
  let omega = ref Mconfig.omega
  let cvc3 = ref Mconfig.cvc3
end

module Input = struct
  let filenames : string list ref = ref []
  let main () = List.hd !filenames
  let spec = ref ""
  let is_cegar () =
    match !filenames with
    | [filename] -> String.ends_with filename ".cegar"
    | _ -> false
end

let pp : string option ref = ref None

let use_temp = ref false

module TRecS = struct
  let param1 = ref 1000
  let param2 = ref 10
end

module Limit = struct
  let time = ref 0
end

module Parallel = struct
  let num = ref 0
  let time = ref 0
  let continue = ref true
end

module Method = struct
  type mode = Reachability | FileAccess | Termination | NonTermination | FairTermination | FairNonTermination | Trans
  let mode = ref Reachability
  let nondet = ref false (* eager evaluation for branch *)
  let use_nint = ref false
  let use_part_eval = true
  let check_sat = true
  let gen_int = true
  let split_free_var = ref false
  let filter_forward = ref true
  let use_unknown = ref false
  let lift_fv_only = ref false
  let relative_complete = ref false
  let never_use_relative_complete = ref true
  let no_exparam = ref true
  let cps_simpl = ref false
  let insert_param_funarg = ref false
  let split_assert = ref false
  let tupling = ref false
  let elim_redundant_arg = ref true
  let elim_same_arg = ref false
  let exists_unknown_false = true
  let replace_const = ref false
  let use_spec = ref false
  let comment_spec = ref true
  let modular = ref false
  let verify_ref_typ = ref false
  let ignore_non_termination = ref false
  let fail_as_exception = ref false
  let ignore_exn_arg = ref false
  let quick_check = ref false
  let abst_for_loop = ref true
  let encode_before_make_ext_fun = ref true
  let only_specified = ref false
  let occurence_param = ref false
  let slice = ref true
  let sub = ref false
  let target = ref ""
end

module Encode = struct
  let bool_to_int = ref false
  let base_to_int = ref true
  let data_to_int = ref false
  let complex_data_to_int = ref true
  let encode_list_opt = ref false
  let abst_list_eq = ref false
  let abst_literal = ref (-1)
  let used_abst : string list ref = ref []
  let use_abst s = if not @@ List.mem s !used_abst then used_abst := s :: !used_abst

  module RecData = struct
    type dest = Tuple | Variant
    let dest = ref Tuple
    type additional = Nothing | Top | Unit_top
    let additional = ref Top
    let share_predicate = ref true
  end
end

module Print = struct
  let source = true
  let cps = true
  let abst = true
  let abst_eager = true
  let typ = true
  let hors = false
  let trecs_output = false
  let trace = false
  let interpolant = true
  let progress = ref true
  let modular_progress = ref true
  let constraints = true
  let lower_bound = true
  let refine_log = true
  let eval_abst = ref false
  let fun_arg_typ = ref true
  let rd_constraints = ref true
  let abst_typ = ref false
  let only_if_id = ref false
  let result = ref true
  let certificate = ref false
  let assert_loc = ref false
end

module Log = struct
  module Time = struct
    let preprocess = ref 0.
    let abstraction = ref 0.
    let mc = ref 0.
    let cegar = ref 0.
    let interpolant = ref 0.
    let parameter_inference = ref 0.
    let hors_quickcheck = ref 0.
  end

  type status = Safe | Unsafe | Terminating | NonTerminating | Unknown of string | Error of string | Other of string
  let result = ref (Other "Init")
  let string_of_result head =
    let hd s = if head then "Done: " ^ s else s in
    match !result with
    | Safe -> hd "Safe"
    | Unsafe -> hd "Unsafe"
    | Terminating -> hd "Terminating"
    | NonTerminating -> hd "NonTerminating"
    | Unknown "" -> hd "Unknown"
    | Unknown s -> hd @@ Format.sprintf "Unknown (%s)" s
    | Error s -> if head then "Error: " ^ s else s
    | Other s -> s

  let cegar_loop = ref 1
  let args = ref [""] (* command-line options *)
end

module Trans = struct
  type destination = Before_CPS | CPS | CHC

  let destination = ref CPS

  let destinations =
    ["Before_CPS", (Before_CPS, "ML program before CPS transformation (ADT is encoded)");
     "CPS",        (CPS,        "ML program after CPS transformation");
     "CHC",        (CHC,        "CHC for refinement types")]

  let string_of_destinations () =
    List.fold_left (fun acc (s,(_,desc)) -> acc ^ Format.sprintf "%s: %s\n" s desc) "" destinations

  let set_trans s =
    Method.(mode := Trans);
    try
      let dest,_ = List.assoc s destinations in
      destination := dest
    with Not_found ->
      raise @@ Arg.Bad (Format.sprintf "Invalaid argument of -trans")
end

(** TODO merge with Method *)
module Mode = struct
  let ignore_conf = ref false
  let init_trans = ref true
  let just_print_non_CPS_abst = ref false
  let trans_to_CPS = ref true
  let module_mode = ref false
end

module PredAbst = struct
  let use_filter = ref false
  let never_use_neg_pred = ref false
  let wp_max_max = 8
  let remove_false = ref false (* remove false from pbs/pts in CEGAR_abst_util *)
  let assume = ref false (* use strongest post condition in if-term *)
  let assume_if = ref false (* whether replace if-term to branch or not (this flag is used only when !assume = true) *)
  let expand_non_rec = ref true
  let expand_non_rec_init = ref true
  let decomp_pred = ref false
  let decomp_eq_pred = ref false
  let no_simplification = ref false
  let cartesian = ref true
  let shift_pred = ref true
  let bool_init_empty = ref true
end

module Refine = struct
  let use_prefix_trace = false
  let merge_counterexample = ref false
  let use_multiple_paths = ref false
  let disable_predicate_accumulation = ref false
  let use_rec_chc_solver = ref true
  type solver = Hoice | Z3 | Z3_spacer
  let solver = ref Hoice
  let solver_timelimit = ref 5 (* seconds *)
  let hoice = ref Mconfig.hoice
  let z3 = ref Mconfig.z3
  let z3_spacer = ref (Mconfig.z3 ^ " fixedpoint.engine=spacer")
end

module ModelCheck = struct
  let trecs = ref Mconfig.trecs
  let horsat = ref Mconfig.horsat
  let horsat2 = ref Mconfig.horsat2
  let horsatp = ref Mconfig.horsatp

  type model_checker = TRecS | HorSat | HorSat2 | HorSatP
  let mc = ref (if Mconfig.horsat2_available then HorSat2 else if Mconfig.horsat_available then HorSat else TRecS)

  let church_encode = ref false
  let beta_reduce = false
  let useless_elim = false
  let rename_hors = ref false
end

module PrettyPrinter = struct
  let () = Format.set_margin 120
  let color = ref false
  let color_always = ref false
  let write_annot = ref true
  let web = ref false
end

module Termination = struct
  let disjunctive = ref false
  let separate_pred = ref false
  let split_callsite = ref false
  let add_closure_depth = ref false
  let add_closure_exparam = ref false
end

module NonTermination = struct
  let merge_paths_of_same_branch = ref false
  let randint_refinement_log = ref false
  let use_omega = ref true
  let use_omega_first = ref false
end

module FairTermination = struct
  let expand_set_flag = ref false
  let loop_count = ref 0
end

module FairNonTermination = struct
  let expand_ce_iter_init = ref 5
  let break_expansion_ref = ref false
end

module Modular = struct
  let use_ref_typ_gen_method_in_esop2017 = ref false
  let infer_ind = ref false
  let refine_init = ref false
  let use_neg_env = ref true
  let infer_merge = ref false
  let check_simple = ref false
end

module Experiment = struct
  module HORS_quickcheck = struct
    type use = Shortest | Longest | LowestCoverage | HighestCoverage
    let command = ref Mconfig.hors_quickcheck
    let use : use option ref = ref None
    let num = ref 5
    let cex_length_history : int list ref = ref []
  end
end

module Debug = struct
  let check_fun_arg_typ = false
  let check_typ = true
  let debuggable_modules : string list ref = ref []
  let debug_module : string list ref = ref []
  let abst = ref false
  let stop_after = ref ""

  let print_ref_typ () = List.mem "Ref_type" !debug_module
  let make_check s =
    debuggable_modules := s::!debuggable_modules;
    fun () -> List.mem s !debug_module
  let set_debug_modules mods =
    let modules = BatString.nsplit mods "," in
    let check m =
      if not @@ List.mem m !debuggable_modules then
        (Format.printf "Module \"%s\" is not registered for debug@." m;
         exit 1)
    in
    List.iter check modules;
    debug_module := modules @ !debug_module
end
