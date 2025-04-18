open Util

type mode =
  | Reachability
  | FileAccess
  | Termination
  | NonTermination
  | FairTermination
  | FairNonTermination
  | Trans
  | Quick_check
  | Verify_ref_typ
  | Verify_module

let mode = ref Reachability
let need_model_checker () = match !mode with Trans | Quick_check -> false | _ -> true
let long_name_len = 50

module External = struct
  let omega : string option ref = ref None
  let cvc3 : string option ref = ref None
end

module IO = struct
  let filenames : string list ref = ref []
  let main () = List.hd !filenames
  let spec = ref ""

  let make_check s () =
    let ext = "." ^ s in
    List.exists (String.ends_with -$- ext) !filenames

  let is_cegar = make_check "cegar"
  let is_smt2 = make_check "smt2"
  let is_bin = make_check "bin"
  let conf_file_default = "option.conf"
  let conf_file = ref conf_file_default
  let ignore_inc = ref false
  let ignore_lib = ref false
  let save_files = ref false
end

let pp : string option ref = ref None

module TRecS = struct
  let param1 = ref 1000
  let param2 = ref 10
end

module Limit = struct
  let time = ref 0
  let time_subproblem = ref 0
end

module Parallel = struct
  let child = ref ""
  let num = ref 0
  let time = ref 0
  let continue = ref true
  (* Continue the verification even if we found the result (unsupported) *)

  let on () = !num > 1
end

module Method = struct
  let init_trans = ref true
  let trans_to_CPS = ref true
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
  let abst_for_loop = ref true
  let encode_before_make_ext_fun = ref true
  let only_specified = ref false
  let occurence_param = ref false
  let slice = ref true
  let slice_i = ref (-1) (* just for test/debug *)
  let slice_target = ref "" (* just for test/debug *)
  let slice_num = ref 10
  let sub = ref false
  let sub_hops = ref false
  let targets : string list ref = ref []
  let target_exn : string list ref = ref []
  let verify_ref_interface = ref false
  let use_elim_may_div = ref false
  let use_set_theory = ref false
  let chc = ref false
  let expand_nonrec_full = ref true
end

module Abstract = struct
  let list_eq = ref false
  let literal = ref 10
  let over_approx : string list ref = ref []

  let under_approx : string list ref =
    ref [] (* List of messages that explain the side conditions for the safety *)

  let over s = over_approx := List.cons_unique s !over_approx
  let under s = under_approx := List.cons_unique s !under_approx
  let ignore_exn_arg = ref false
  let ignore_data_arg = ref false
  let base_to_int = ref true
  let list_to_int = ref false
  let data_to_int = ref false
  let data_to_int_but_exn = ref false
  let exn_to_bool = ref false
  let complex_data_to_int = ref true
  let menhir = ref true
  let div = ref false
end

module Encode = struct
  let bool_to_int = ref false
  let encode_list_opt = ref false

  module RecData = struct
    type dest = Tuple | Variant

    let dest = ref Tuple

    type additional = Nothing | Top | Unit_top

    let additional = ref Top
    let share_predicate = ref true
  end
end

module Print = struct
  let target = ref Format.std_formatter
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
  let target_ext_loc = ref false
  let id_loc = ref ""
  let exit_after_parsing = ref false
  let signature = ref false
  let exn = ref false
  let var_id = ref false
  let json = ref false
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
    let before_slice = ref (-1.)
  end

  type status =
    | Safe
    | Unsafe
    | Terminating
    | NonTerminating
    | Unknown of string
    | Error of string
    | Other of string

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
  let args = ref [ "" ] (* command-line options *)
  let json_file = ref ""
end

module Trans = struct
  type destination = Before_CPS | CPS | CHC | HFLz

  let destination = ref CPS

  let destinations =
    [
      ("Before_CPS", (Before_CPS, "ML program before CPS transformation (ADT is encoded)"));
      ("CPS", (CPS, "ML program after CPS transformation"));
      ("CHC", (CHC, "CHC for refinement types"));
      ("HFLz", (HFLz, "HFL(Z)"));
    ]

  let string_of_destinations () =
    List.fold_left
      (fun acc (s, (_, desc)) -> acc ^ Format.sprintf "%s: %s\n" s desc)
      "" destinations

  let set_trans s =
    mode := Trans;
    try
      let dest, _ = List.assoc s destinations in
      destination := dest
    with Not_found -> raise @@ Arg.Bad (Format.sprintf "Invalaid argument of -trans")
end

module PredAbst = struct
  let use_filter = ref false
  let never_use_neg_pred = ref false
  let wp_max_max = 8
  let remove_false = ref false (* remove false from pbs/pts in CEGAR_abst_util *)
  let assume = ref false (* use strongest post condition in if-term *)
  let assume_if = ref false
  (* whether replace if-term to branch or not (this flag is used only when !assume = true) *)

  let expand_non_rec = ref true
  let expand_non_rec_init = ref true (* whether to expand original top-level functions or not *)
  let decomp_pred = ref false
  let decomp_eq_pred = ref false
  let no_simplification = ref false
  let cartesian = ref true
  let shift_pred = ref true
  let bool_init_empty = ref true
end

module Refine = struct
  type solver = Hoice | Z3 | Z3_spacer

  let use_prefix_trace = false
  let merge_counterexample = ref false
  let use_multiple_paths = ref false
  let disable_predicate_accumulation = ref false
  let solver = ref Hoice
  let solver_timelimit = ref 5 (* seconds *)
  let hoice : string option ref = ref None
  let z3 : string option ref = ref None
  let z3_spacer : string option ref = ref None
  let use_rec_chc_solver = ref true
end

module ModelCheck = struct
  (* execution paths of model checkers *)
  let trecs : string option ref = ref None
  let horsat : string option ref = ref None
  let horsat2 : string option ref = ref None
  let horsatp : string option ref = ref None
  let church_encode = ref false
  let beta_reduce = false
  let useless_elim = false
  let rename_hors = ref false
end

module PrettyPrinter = struct
  let () = Format.set_margin 120
  let () = Format.set_max_indent 119
  let color = ref true
  let color_always = ref false
  let write_annot = ref false
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
  let use_omega = ref false
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

    let command : string option ref = ref None
    let use : use option ref = ref None
    let num = ref 5
    let cex_length_history : int list ref = ref []
  end

  module Slice = struct
    let alpha = ref (-1.0)
    let max_hop = ref 0
  end
end

(* Assume deterministic strategy *)
module EvalStrategy = struct
  let app_left_to_right =
    let r = ref true in
    (fun () -> r := false) (r := true);
    !r

  let binop_left_to_right =
    let r = ref true in
    ignore
      ((r := false;
        0)
      +
      (r := true;
       0));
    !r

  let constr_left_to_right =
    let r = ref true in
    ignore
      ((r := false)
      ::
      (r := true;
       []));
    !r

  let tuple_left_to_right =
    let r = ref true in
    ignore ((r := false), (r := true));
    !r

  type t = { left : unit; right : unit }

  let record_left_to_right =
    let r = ref true in
    ignore { left = r := false; right = r := true };
    !r

  let setref_left_to_right =
    let r = ref true in
    (r := false; ref ()) := (r := true);
    !r
    [@@ocamlformat "disable"]

  let setfield_left_to_right =
    let r = ref true in
    (r := false; ref ()).contents <- (r := true);
    !r
    [@@ocamlformat "disable"]
end

module Preprocess = struct
  let stop_after = ref ""
  let check_after = ref ""
  let check_flag = ref true
  let reduce_memory = ref false
  (* Forget the history of preprocess and types in AFV; disable some features *)

  let lazy_preprocess = ref true
end

module Debug = struct
  let check_fun_arg_typ = false
  let check_typ = false
  let check_tmodule = ref false
  let debuggable_modules : string list ref = ref []
  let debug_module : string list ref = ref []
  let abst = ref false
  let input_cex = ref false
  let minimize = ref false
  let print_ref_typ () = List.mem "Ref_type" !debug_module

  let make_check s =
    let s' = match String.split_on_string ~by:"Dune__exe__" s with [ ""; s' ] -> s' | _ -> s in
    debuggable_modules := s' :: !debuggable_modules;
    fun () -> List.mem s' !debug_module

  let set_debug_modules mods =
    let modules = String.split_on_string ~by:"," mods in
    let check m =
      if not @@ List.mem m !debuggable_modules then
        failwith {|Module "%s" is not registered for debug@.|} m
    in
    List.iter check modules;
    debug_module := modules @ !debug_module

  let print f = if !debug_module <> [] then Format.printf f else Format.iprintf f
end
