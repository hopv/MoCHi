open Util
open Mochi_util
open CEGAR_syntax
open CEGAR_type
open CEGAR_util


(* gather error paths *)
type path =
    int list (* branch info. *)
    * bool list (* partially constructed external input info. *)
    * ((int * (bool list)) list) (* external input info. *)
let add_next_rand_info r (branch,bs,ext) = (branch, [], (decomp_randint_label r, bs) :: ext)
let add_tf_info b (branch,bs,ext) = (branch,b::bs,ext)
let add_branch_info b (branch,bs,ext) = (b::branch,bs,ext)
let rec error_trace_aux : (string Rose_tree.t) -> path list = function
  | Rose_tree.Node ("br_exists", [t1; t2]) ->
     error_trace_aux t1 @ error_trace_aux t2
  | Rose_tree.Node ("l0", [t]) -> List.map (add_branch_info 0) @@ error_trace_aux t
  | Rose_tree.Node ("l1", [t]) -> List.map (add_branch_info 1) @@ error_trace_aux t
  | Rose_tree.Node ("tt", [t]) -> List.map (add_tf_info true)  @@ error_trace_aux t
  | Rose_tree.Node ("ff", [t]) -> List.map (add_tf_info false) @@ error_trace_aux t
  | Rose_tree.Node (r, [t]) when CEGAR_syntax.is_randint_label r ->
     List.map (add_next_rand_info r) @@ error_trace_aux t
  | Rose_tree.Node (_, [t]) -> error_trace_aux t
  | Rose_tree.Node (_, []) -> (* Leaf *)
     [([], [], [])]
  | _ -> assert false

let error_trace tr =
  List.fold_left (fun (xs,ys) (x,_,y) -> (x::xs, y::ys)) ([],[]) @@ error_trace_aux tr

let cegar prog0 labeled is_cp ce_tree prog =
  let (cexs, ext_cexs) = error_trace ce_tree in
  Verbose.printf "cexs: %a@." (List.print (List.print Format.pp_print_int)) cexs;
  Verbose.printf "ext_cexs: %a@." (List.print (List.print (fun fm (a, bs)-> Format.fprintf fm "(%a, %a)" Format.pp_print_int a (List.print Format.pp_print_bool) bs))) @@ ext_cexs;
  let map_randint_to_preds = make_map_randint_to_preds prog0 in
  let renv = get_renv prog in
  let path_counter = ref 0 in

  let print_path fm p = Format.fprintf fm "%a" (print_list Format.pp_print_string ",") (List.map (fun n -> if n=0 then "then" else "else") p) in
  let print_ext_path_parts fm p = Format.fprintf fm "%s"
    (match p with
      | Positive -> "true"
      | Negative -> "false"
      | Do_not_Care -> "_") in
  let print_ext_path fm p = Format.fprintf fm "[%a]" (print_list print_ext_path_parts ",") p in
  let print_ext_paths fm (n, p) = Format.fprintf fm "%d:%a" n (print_list print_ext_path ",") p in
  let print_pred ppf (env, fml) =
    Format.fprintf ppf "%a |= %a" Fpat.TypEnv.pr_compact env Fpat.Formula.pr fml in
  let log_file =
    if !Flag.NonTermination.randint_refinement_log then
      let dirname = Filename.dirname !!Flag.Input.main in
      let basename = Filename.basename !!Flag.Input.main in
      dirname ^ "/refinement/" ^ Filename.change_extension basename "refinement"
    else ""
  in

  Verbose.printf "@.ABSTRACTION TYPE ENV:@.%a@." CEGAR_print.env_diff prog.env;

  let paths =
    List.filter_map2
      (fun orig_ce ext_ce ->
        path_counter := !path_counter + 1;
        let rand_num =
          if Flag.Method.(FairNonTermination = !mode) then
            Some (List.length ext_ce)
          else None in
        let ce = CEGAR_trans.trans_ce labeled prog orig_ce rand_num in
        if !Flag.Print.progress then Feasibility.print_ce_reduction ~map_randint_to_preds ~ext_ce ce prog;
        let ext_path = ext_ce |> arrange_ext_preds_sequence |> conv_path in
        (* let ext_preds = ext_path |> List.map (FpatInterface.trans_ext renv map_randint_to_preds) in *)
        let path = Feasibility.check_non_term ~map_randint_to_preds ~ext_ce ce prog in
        match path with
          | Feasibility.Feasible _ -> assert false
          | Feasibility.FeasibleNonTerm (true, env, sol) ->
            Verbose.printf "[%d: path %d] Found useless feasible path: [%a]@." !Flag.Log.cegar_loop !path_counter print_path orig_ce;
            None (* do not use a useless (i.e. already-used-in-CEGAR) error-path *)
          | Feasibility.FeasibleNonTerm (false, env, sol) ->
            Verbose.printf "[%d: path %d] Found feasible path: [%a]@." !Flag.Log.cegar_loop !path_counter print_path orig_ce;
            Some (path, orig_ce, ce, ext_path)
          | Feasibility.Infeasible prefix ->
            Verbose.printf "[%d: path %d] Found infeasible path: [%a]@." !Flag.Log.cegar_loop !path_counter print_path orig_ce;
            Some (path, orig_ce, ce, ext_path))
      cexs ext_cexs
  in

  (* Progress Check: checking whether an obtained counterexample tree has either infeasible paths or open feasible paths *)
  if paths = [] then raise NoProgress;

  Verbose.printf "ORIG:@.";
  List.iter (fun (_, orig_ce, _, ext_path) -> Verbose.printf "%a: @.  %a@." print_path orig_ce (print_list print_ext_paths ";") ext_path) paths;

  let paths = List.concat @@ List.map (if !Flag.NonTermination.merge_paths_of_same_branch then merge_similar_paths else (fun x -> x)) (group_by_same_branching paths) in

  if !Flag.NonTermination.merge_paths_of_same_branch then
    begin
      Verbose.printf "MERGED:@.";
      List.iter (fun (_, orig_ce, _, ext_path) -> Verbose.printf "%a: @.  %a@." print_path orig_ce (print_list print_ext_paths ";") ext_path) paths;
    end;

  path_counter := 0;
  let refinement_type_map = function
    | (Feasibility.Feasible _, _, _, _) -> assert false
    | (Feasibility.FeasibleNonTerm (true, env, sol), _, _, _) ->
        assert false
    | (Feasibility.FeasibleNonTerm (false, env, sol), orig_ce, ce, ext_path) ->
        let log_cout = if !Flag.NonTermination.randint_refinement_log then open_out_gen [Open_wronly; Open_append; Open_text; Open_creat] 0o666 log_file else stdout in
        let log_fm = Format.formatter_of_out_channel log_cout in

        Verbose.printf "[%d: path %d] Refining by feasible path: [%a]@." !Flag.Log.cegar_loop !path_counter print_path orig_ce;
        if !Flag.NonTermination.randint_refinement_log then Format.fprintf log_fm "[%d: path %d] Refining by feasible path: [%a]@." !Flag.Log.cegar_loop !path_counter print_path orig_ce;
        let ext_preds = ext_path |> List.map (FpatInterface.trans_ext renv map_randint_to_preds) in
        List.iter (fun (rand_var, preds_sequence) -> Verbose.printf "%a: %a@." Fpat.Idnt.pr rand_var (print_list print_pred " , ") preds_sequence) ext_preds;
        if !Flag.NonTermination.randint_refinement_log then List.iter (fun (rand_var, preds_sequence) -> Format.fprintf log_fm "%a: %a@." Fpat.Idnt.pr rand_var (print_list print_pred " , ") preds_sequence) ext_preds;
        let inlined_functions = inlined_functions prog0 in
        let map,_ = Refine.refine_with_ext inlined_functions is_cp [] [ce] [ext_preds] prog0 in
        let map = CEGAR_trans.add_neg_preds_renv map in
        Verbose.printf "REFINEMENT MAP:@.%a@." CEGAR_print.env_diff map;
        if !Flag.NonTermination.randint_refinement_log then Format.fprintf log_fm "REFINEMENT MAP:@.%a@." CEGAR_print.env_diff map;
        if !Flag.NonTermination.randint_refinement_log then close_out log_cout;
        map
    | (Feasibility.Infeasible prefix, orig_ce, ce, ext_path) ->
        let log_cout = if !Flag.NonTermination.randint_refinement_log then open_out_gen [Open_wronly; Open_append; Open_text; Open_creat] 0o666 log_file else stdout in
        let log_fm = Format.formatter_of_out_channel log_cout in

        Verbose.printf "[%d: path %d] Refining by infeasible path: [%a]@." !Flag.Log.cegar_loop !path_counter print_path orig_ce;
        if !Flag.NonTermination.randint_refinement_log then Format.fprintf log_fm "[%d: path %d] Refining by infeasible path: [%a]@." !Flag.Log.cegar_loop !path_counter print_path orig_ce;
        let ext_preds = ext_path |> List.map (FpatInterface.trans_ext renv map_randint_to_preds) in
        List.iter (fun (rand_var, preds_sequence) -> Verbose.printf "%a: %a@." Fpat.Idnt.pr rand_var (print_list print_pred " , ") preds_sequence) ext_preds;
        if !Flag.NonTermination.randint_refinement_log then List.iter (fun (rand_var, preds_sequence) -> Format.fprintf log_fm "%a: %a@." Fpat.Idnt.pr rand_var (print_list print_pred " , ") preds_sequence) ext_preds;
        let inlined_functions = inlined_functions prog0 in
        let map, p = Refine.refine inlined_functions is_cp prefix [ce] [ext_preds] prog0 in
        Verbose.printf "REFINEMENT MAP:@.%a@." CEGAR_print.env_diff map;
        if !Flag.NonTermination.randint_refinement_log then Format.fprintf log_fm "REFINEMENT MAP:@.%a@." CEGAR_print.env_diff map;
        if !Flag.NonTermination.randint_refinement_log then close_out log_cout;
        map
  in
  let maps = List.map (fun path -> path_counter := !path_counter + 1; refinement_type_map path) paths in
  let env' = List.fold_left (fun a b -> Refine.add_preds_env b a) prog.env maps in
  {prog with env=env'}
