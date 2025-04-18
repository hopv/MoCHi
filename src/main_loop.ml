open Util
open Mochi_util
open Main_loop_util

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

type result = Safe | Unsafe | Unknown [@@deriving show { with_path = false }]

let bool_of_return { result } =
  match result with Safe _ -> true | Unsafe _ -> false | Unknown _ -> false

let result_of_return { result } =
  match result with Safe _ -> Safe | Unsafe _ -> Unsafe | Unknown _ -> Unknown

let add_results ?(complete = false) (tree : Preprocess_common.tree) (id, info, (r : return))
    (results : Preprocess_common.results) : Preprocess_common.results =
  Preprocess_common.IdMap.add id (info, r.result) results
  |> complete ^> (Preprocess.complete_results -$- tree)

let print_return id r = Verbose.printf "Result of #%d: %a@.@." id pp_result (result_of_return r)

module Parallel = struct
  type spawn = {
    id : Preprocess_common.id;
    prep_info : Preprocess_common.info;
    problem_info : Problem.info;
    make_get_rtyp : (string -> CEGAR_ref_type.t) -> Trans.get_rtyp;
    pid : Unix.pid;
  }

  let spawned : spawn list ref = ref []
  let print_spawn fm { id; pid } = Format.fprintf fm "#%d:%d" id pid
  let output_file_of id = Temp.S.file @@ Format.sprintf "%d.bin.out" id

  let spawn ~id ~prep_info ~problem_info ~make_get_rtyp ~prog =
    let input_file = Temp.S.file @@ Format.sprintf "%d.bin" id in
    let output_file = output_file_of id in
    Marshal.to_file ~flag:[ Closures ] input_file prog;
    let args = Array.append Sys.argv [| "-s"; "-child"; output_file; input_file |] in
    let pid = Unix.(create_process args.(0) args stdin stdout stderr) in
    at_exit (fun () -> try Unix.kill pid Sys.sigkill with _ -> ());
    Verbose.printf "Running process PID:%d for #%d.@.@." pid id;
    spawned := { id; prep_info; problem_info; make_get_rtyp; pid } :: !spawned

  let result_of { id; prep_info; problem_info; make_get_rtyp } =
    let file = output_file_of id in
    let r = Marshal.from_file_exn file in
    let result = Preprocess.verif_result_of_CEGAR_result make_get_rtyp r in
    (id, prep_info, { result; info = problem_info })

  let wrap_wait (pid', s) =
    match s with
    | Unix.WEXITED 0 ->
        let completed, spawned' = List.partition (fun { pid } -> pid = pid') !spawned in
        let comp = List.get completed in
        let r = result_of comp in
        print_return comp.id (Triple.trd r);
        spawned := spawned';
        r
    | _ -> assert false

  let wait () = wrap_wait !!Unix.wait

  let completed_jobs () =
    let check_and_wait { pid } =
      if Sys.file_exists @@ output_file_of pid then Some (wrap_wait @@ Unix.waitpid [] pid)
      else None
    in
    List.filter_map check_and_wait !spawned

  let add_results (results : Preprocess_common.results) (tree : Preprocess_common.tree) :
      Preprocess_common.results =
    if !!Flag.Parallel.on then
      let completed = !!completed_jobs in
      let completed =
        if completed = [] && !Flag.Parallel.num = List.length !spawned then [ wait () ]
        else completed
      in
      List.fold_right (add_results tree) completed results
    else results
end

(** Translate Problem.t to CEGAR_syntax.prog *)
let cegar_of_problem fun_list problem =
  let prog, map, _, make_get_rtyp = CEGAR_trans.trans_prog problem in
  let abst_cegar_env =
    Spec.get_abst_cegar_env problem.spec prog |@> Verbose.printf "%a@." Spec.print_abst_cegar_env
  in
  let prog = CEGAR_trans.add_env abst_cegar_env prog in
  let info =
    let orig_fun_list =
      List.L.filter_map fun_list ~f:(fun x -> List.assoc_opt (CEGAR_trans.trans_var x) map)
    in
    let inlined = List.map CEGAR_trans.trans_var problem.spec.inlined in
    let fairness = if Flag.(!mode = FairNonTermination) then Some problem.spec.fairness else None in
    CEGAR_syntax.{ prog.info with orig_fun_list; inlined; fairness }
  in
  (CEGAR_syntax.{ prog with info }, make_get_rtyp, problem.info)

let cegar_of_preprocessed ?fun_list (path : Preprocess_common.path) :
    CEGAR_syntax.prog * ((string -> CEGAR_ref_type.t) -> Trans.get_rtyp) * Problem.info =
  let { Preprocess_common.problem } = List.last path in
  if !!Dbg.check && Syntax.get_fv problem.term <> [] then (
    Format.eprintf "Unbound varibale: %a@." Print.(list id) (Syntax.get_fv problem.term);
    assert false);
  let fun_list =
    match fun_list with
    | None -> (
        match Preprocess_common.Path.assoc_label_opt Decomp_pair_eq path with
        | None -> []
        | Some { problem } -> problem |> Problem.term |> Term_util.get_top_funs)
    | Some fun_list -> fun_list
  in
  cegar_of_problem fun_list problem

let cegar_of_preprocessed ?fun_list results =
  Preprocess_common.measure_time (cegar_of_preprocessed ?fun_list) results

let write_annot env orig = env |> List.map (Pair.map_fst Id.name) |> WriteAnnot.f orig

let report_safe env orig =
  if !Flag.PrettyPrinter.write_annot then Option.iter (write_annot env) orig;
  let s =
    match !Flag.mode with
    | Flag.NonTermination -> "Non-terminating!"
    | Flag.FairNonTermination -> "Fair Infinite Execution found!"
    | _ -> "Safe!"
  in
  Color.fprintf !Flag.Print.target Bright "%s@." s;
  if !Flag.Abstract.under_approx <> [] then
    Format.fprintf !Flag.Print.target "  (if %a)@."
      (print_list Format.pp_print_string " and@\n")
      !Flag.Abstract.under_approx;
  Format.fprintf !Flag.Print.target "@.";
  if !Flag.Method.relative_complete then (
    let problem = [%unsupported] in
    let map =
      List.map
        (fun (x, t) ->
          ( Id.make ~id:(-1) (Fpat.Idnt.string_of x) Type_util.Ty.int,
            CEGAR_trans.trans_inv_term @@ FpatInterface.inv_term @@ t ))
        !Fpat.RefTypInfer.prev_sol
    in
    let t = Term_util.subst_map map (Problem.term problem) in
    Format.fprintf !Flag.Print.target "Problem with Quantifiers Added:@.";
    Format.fprintf !Flag.Print.target "  @[<v>%a@]@.@." Print.term t);
  if env <> [] && Flag.(!mode <> Termination) then (
    Verbose.printf "Refinement Types:@.";
    let env' = List.map (Pair.map_snd Ref_type.simplify) env in
    let pr (f, typ) = Verbose.printf "  %s: %a@." (Id.name f) Ref_type.print typ in
    List.iter pr env';
    Verbose.printf "@.";

    if !Flag.Print.abst_typ then (
      Verbose.printf "Abstraction Types:@.";
      let pr (f, typ) =
        Verbose.printf "  %s: %a@." (Id.name f) Print.typ @@ Ref_type.to_abst_typ typ
      in
      List.iter pr env';
      Verbose.printf "@."))

let report_unsafe (ce : (Syntax.term list * Syntax.term option) option) ptree =
  if !Flag.Abstract.over_approx <> [] then
    Color.printf Bright "Unknown (because of abstraction options %a)@.@."
      Print.(list string)
      !Flag.Abstract.over_approx
  else Color.printf Bright "Unsafe!@.@.";
  match (ce, Preprocess.get_set_main ptree) with
  | Some (ce, main), Some node -> (
      let pr main_fun =
        let arg_num = Type_util.arity @@ Lid.typ main_fun in
        if arg_num > 0 then
          Format.fprintf !Flag.Print.target "Input for %a:@.  %a@." Print.lid main_fun
            Print.(print_list term "; ")
            (List.take arg_num ce)
      in
      let set_main =
        match main with
        | None -> node.problem
        | Some main -> Problem.map (Trans.replace_main ~force:true ~main) node.problem
      in
      let main = match node.info with Some (Trans_problem.Info_main f) -> f | _ -> None in
      Option.may pr main;
      try Verbose.printf "@[<v 2>Error trace:%a@." Eval.print (ce, set_main)
      with _ -> Verbose.printf " ...@.@.")
  | _ -> ()

(* Run CEGAR-root (just for CEGAR input?) *)
let rec run_cegar prog =
  try
    match CEGAR.run prog with
    | CEGAR.Safe _env ->
        set_status Flag.Log.Safe;
        Color.printf Bright "Safe!@.@.";
        true
    | CEGAR.Unsafe _ ->
        set_status Flag.Log.Unsafe;
        Color.printf Bright "Unsafe!@.@.";
        false
    | CEGAR.Unknown _ -> unsupported "Main_loop.run_cegar"
  with
  | Fpat.RefTypInfer.FailedToRefineTypes
    when Flag.Method.((not !insert_param_funarg) && not !no_exparam) ->
      Flag.Method.insert_param_funarg := true;
      run_cegar prog
  | Fpat.RefTypInfer.FailedToRefineTypes
    when Flag.Method.((not !relative_complete) && not !no_exparam) ->
      Verbose.printf "@.REFINEMENT FAILED!@.";
      Verbose.printf "Restart with relative_complete := true@.@.";
      Flag.Method.relative_complete := true;
      run_cegar prog
  | Fpat.RefTypInfer.FailedToRefineExtraParameters ->
      Fpat.RefTypInfer.params := [];
      Fpat.RefTypInfer.prev_sol := [];
      Fpat.RefTypInfer.prev_constrs := [];
      incr Fpat.RefTypInfer.number_of_extra_params;
      run_cegar prog

let improve_precision e =
  match e with
  | Fpat.RefTypInfer.FailedToRefineTypes
    when Flag.Method.((not !insert_param_funarg) && not !no_exparam) ->
      Flag.Method.insert_param_funarg := true;
      true
  | Fpat.RefTypInfer.FailedToRefineTypes
    when Flag.Method.((not !relative_complete) && not !no_exparam) ->
      Verbose.printf "@.REFINEMENT FAILED!@.";
      Verbose.printf "Restart with relative_complete := true@.@.";
      Flag.Method.relative_complete := true;
      true
  | Fpat.RefTypInfer.FailedToRefineExtraParameters
    when !Flag.Method.relative_complete && not !Flag.Method.no_exparam ->
      Fpat.RefTypInfer.params := [];
      Fpat.RefTypInfer.prev_sol := [];
      Fpat.RefTypInfer.prev_constrs := [];
      incr Fpat.RefTypInfer.number_of_extra_params;
      true
  | Fpat.RefTypInfer.FailedToRefineTypes when !Flag.Method.slice ->
      Flag.Method.slice := false;
      true
  | _ -> false

let print_result_delimiter () =
  let width =
    let cols =
      try Unix.open_and_read_line "tput cols" |> int_of_string
      with Failure _ | End_of_file -> !!Format.get_margin
    in
    min cols !!Format.get_margin
  in
  if not !!is_only_result then
    Format.fprintf !Flag.Print.target "@.%a@.@." Color.s_green (String.make width '=')

let trans_env top_funs make_get_rtyp env : (Syntax.id * Ref_type.t) list =
  let get_rtyp f =
    List.assoc f env |@> Dbg.printf "trans_env %a: %a@." CEGAR_print.var f CEGAR_ref_type.print
  in
  let aux f = Option.try_with_any (fun () -> (f, Ref_type.rename @@ make_get_rtyp get_rtyp f)) in
  List.filter_map aux top_funs

let status_of_result (r : Preprocess_common.verif_result) : Flag.Log.status =
  match r with
  | Safe _env -> Safe
  | Unsafe _ when Flag.(!mode = NonTermination || !Method.ignore_non_termination) -> Unknown ""
  | Unsafe _ when !Flag.Abstract.over_approx <> [] ->
      Unknown
        (Format.asprintf "because of abstraction options %a"
           Print.(list string)
           !Flag.Abstract.over_approx)
  | Unsafe _ -> Unsafe
  | Unknown s when String.starts_with s "Error: " ->
      Error (snd @@ String.split_nth s (String.length "Error: "))
  | Unknown s -> Unknown s

let report ?(delim_first = true) orig parsed ptree { result; info } =
  if delim_first then print_result_delimiter ();
  List.iter (Verbose.fprintf !Flag.Print.target "  %s@.") info;
  if info <> [] then Verbose.fprintf !Flag.Print.target "@.";
  (if !Flag.Print.result then
     match result with
     | Safe get_rtyp when Flag.(!mode = FairTermination) => !!Verbose.check ->
         Problem.term parsed
         |> Term_util.get_top_funs
         |> List.filter_map (fun x ->
                try Some (x, get_rtyp x) with Unsupported _ | Not_found -> None)
         |> report_safe -$- orig
     | Unsafe { vals_main } ->
         let vals_main =
           if !!Dbg.check then Some !?vals_main
           else try Some !?vals_main with Unsupported _ -> None
         in
         report_unsafe vals_main ptree
     | Unknown s when String.starts_with s "Error: " -> Color.printf Bright "%s@.@." s
     | Unknown s ->
         Color.printf Bright "Unknown";
         if s <> "" then Color.printf Bright " %s" s;
         Color.printf Bright "@.@."
     | _ -> ());
  if not delim_first then print_result_delimiter ()

let check ?fun_list ?(exparam_sol = []) pp =
  let node = List.last pp in
  let preprocessed, make_get_rtyp, info =
    Preprocess_common.measure_time (cegar_of_preprocessed ?fun_list) pp
  in
  let cegar_prog =
    if Flag.(List.mem !mode [ FairTermination; Termination ] && !Termination.add_closure_exparam)
    then (
      Dbg.printf "exparam_sol: %a@." Print.(list (id * Format.pp_print_int)) exparam_sol;
      let exparam_sol' =
        List.map (Pair.map CEGAR_trans.trans_var CEGAR_syntax.make_int) exparam_sol
      in
      let prog'' = CEGAR_util.map_body_prog (CEGAR_util.subst_map exparam_sol') preprocessed in
      Dbg.printf "MAIN_LOOP: %a@." CEGAR_print.prog preprocessed;
      let info =
        { preprocessed.CEGAR_syntax.info with CEGAR_syntax.exparam_orig = Some preprocessed }
      in
      { prog'' with CEGAR_syntax.info })
    else preprocessed
  in
  if !Flag.Preprocess.stop_after = "Preprocess" then exit 0;
  if !Flag.Parallel.num > 0 then (
    Parallel.spawn ~id:node.id ~prep_info:node.info ~problem_info:info ~make_get_rtyp
      ~prog:cegar_prog;
    None)
  else
    let result = cegar_prog |> CEGAR.run |> Preprocess.verif_result_of_CEGAR_result make_get_rtyp in
    Some { result; info }

exception CheckTimeOut

(** Repeatedly run preprocess (expand preprocess-tree) and check preprocessed problems *)
let eval ?(fun_list : Syntax.id list option) ?(exparam_sol : (Syntax.id * int) list option)
    (tree : Preprocess_common.tree) : Preprocess_common.verif_result * Preprocess_common.tree =
  let rec loop counter results tree =
    let results, tree, counter =
      let { Preprocess.ready; tree; expanded; counter; results } =
        Preprocess.run counter results tree
      in
      let results =
        match ready with
        | None ->
            if !!Flag.Parallel.on && not expanded then
              let r = Parallel.wait () in
              add_results tree r results
            else results
        | Some (id, info, _) -> (
            Verbose.printf "Preprocessing:@\n  @[%a@]" Preprocess.print_tree tree;
            let path = Preprocess_common.get_path_of id tree in
            match check ?fun_list ?exparam_sol path with
            | None ->
                (* for parallel *)
                results
            | Some r ->
                print_return id r;
                add_results tree (id, info, r) results)
      in
      (results, tree, counter)
    in
    let results = Parallel.add_results results tree in
    match Preprocess.result_of results tree with
    | results, None -> loop counter results tree
    | _, Some (_, r) -> (r, tree)
  in
  loop 1 Preprocess_common.IdMap.empty tree

(** Loop for improving precision step by step
    (Redo a preprocessing for another option changed by improve_precision) *)
let rec loop ?(orig : Parser_wrapper.orig option) ?(make_pps : (unit -> Preprocess.t list) option)
    ?(fun_list : Syntax.id list option) ?(exparam_sol : (Syntax.id * int) list option)
    (problem : Problem.t) : return * Preprocess_common.tree =
  let pps = Option.default Preprocess.all make_pps () in
  let init_tree = Preprocess.make_init pps problem in
  try
    let result, t = eval ?fun_list ?exparam_sol init_tree in
    if not !!Flag.Parallel.on then
      Verbose.printf "Preprocessing:@\n  @[%a@]" Preprocess.print_tree t;
    let info = problem.info in
    ({ result; info }, t)
  with e when improve_precision e -> loop ?orig ?make_pps ?fun_list ?exparam_sol problem

(** Main function of the loop for various options
    make_pps: Preprocessor generator
    fun_list: List of original top-level functions (the list is used in CEGAR-loop)
    orig: Original input program used for type annotaitons in web-interface
    exparam_sol: Extra parameters for termination/fair-termination
    problem: Target problem
*)
let run ?(make_pps : (unit -> Preprocess.t list) option) ?(fun_list : Syntax.id list option)
    ?(orig : Parser_wrapper.orig option) ?(exparam_sol : (Syntax.id * int) list option)
    (problem : Problem.t) : bool =
  let return, ptree = loop ?orig ?make_pps ?fun_list ?exparam_sol problem in
  if !Flag.Print.result then report orig problem ptree return;
  set_status @@ status_of_result return.result;
  bool_of_return return
