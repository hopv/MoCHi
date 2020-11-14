open Util
open Mochi_util
open Main_loop_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type result = Safe | Unsafe | Unknown [@@deriving show]
type result_tree = (result * return option) Rose_tree.t

let cegar_of_preprocessed ?fun_list results =
  let set_main = Option.map fst @@ List.assoc_opt Preprocess.Set_main results in
  let main = Option.(set_main >>= return-|Problem.term >>= Trans.get_set_main)  in
  let problem = Preprocess.last_problem results in
  let fun_list' =
    match fun_list with
    | None ->
        begin
          try
            Preprocess.(take_result Decomp_pair_eq results)
            |> Problem.term
            |> Term_util.get_top_funs
          with Not_found -> []
        end
    | Some fun_list' -> fun_list'
  in

  let prog,map,_,make_get_rtyp_trans = CEGAR_trans.trans_prog problem in
  let abst_cegar_env =
    Spec.get_abst_cegar_env problem.spec prog
    |@> Verbose.printf "%a@." Spec.print_abst_cegar_env
  in
  let prog = CEGAR_trans.add_env abst_cegar_env prog in
  let make_get_rtyp =
    if !!Debug.check then
      let aux f (label,(_,g)) map x =
        Format.printf "BEGIN[%s]@." @@ Preprocess.string_of_label label;
        let r =
          try
            g (f map) x
          with e ->
            Format.printf "GET_RTYP ERROR[%s]: %s@." (Preprocess.string_of_label label) (Printexc.to_string e);
            assert false
        in
        Format.printf "END %s@." @@ Preprocess.string_of_label label;
        r
      in
      List.fold_left aux make_get_rtyp_trans results
    else
      List.fold_left (fun f (_,(_,g)) -> g -| f) make_get_rtyp_trans results
  in

  let info =
    let orig_fun_list =
      let aux x = List.assoc_opt (CEGAR_trans.trans_var x) map in
      List.filter_map aux fun_list'
    in
    let inlined = List.map CEGAR_trans.trans_var problem.spec.Spec.inlined in
    let fairness =
      if Flag.(!mode = FairNonTermination) then
        Some problem.spec.Spec.fairness
      else
        None
    in
    CEGAR_syntax.{prog.info with orig_fun_list; inlined; fairness}
  in
  CEGAR_syntax.{prog with info}, make_get_rtyp, set_main, main, problem.Problem.info


let run_preprocess ?make_pps problem =
  let pps' =
    match make_pps with
    | None -> Preprocess.all ()
    | Some make_pps' -> make_pps' ()
  in
  Preprocess.run_problem pps' problem


let write_annot env orig =
  env
  |> List.map (Pair.map_fst Id.name)
  |> WriteAnnot.f !!Flag.Input.main orig

let report_safe env orig {Problem.term=t0} =
  if !Flag.PrettyPrinter.write_annot then Option.iter (write_annot env) orig;

  let s =
    match !Flag.mode with
    | Flag.NonTermination -> "Non-terminating!"
    | Flag.FairNonTermination -> "Fair Infinite Execution found!"
    | _ -> "Safe!"
  in
  Color.printf Color.Bright "%s@.@." s;

  if !Flag.Method.relative_complete then
    begin
      let map =
        List.map
          (fun (x, t) ->
           Id.make (-1) (Fpat.Idnt.string_of x) [] Type.Ty.int,
           CEGAR_trans.trans_inv_term @@ FpatInterface.inv_term @@ t)
          !Fpat.RefTypInfer.prev_sol
      in
      let t = Term_util.subst_map map t0 in
      Format.printf "Problem with Quantifiers Added:@.";
      Format.printf "  @[<v>%a@]@.@." Print.term t
    end;

  if env <> [] && Flag.(!mode <> Termination) then
    begin
      Verbose.printf "Refinement Types:@.";
      let env' = List.map (Pair.map_snd Ref_type.simplify) env in
      let pr (f,typ) = Verbose.printf "  %s: %a@." (Id.name f) Ref_type.print typ in
      List.iter pr env';
      Verbose.printf "@.";

      if !Flag.Print.abst_typ then
        begin
          Verbose.printf "Abstraction Types:@.";
          let pr (f,typ) = Verbose.printf "  %s: %a@." (Id.name f) Print.typ @@ Ref_type.to_abst_typ typ in
          List.iter pr env';
          Verbose.printf "@."
        end
    end


let report_unsafe main ce set_main =
  if !Flag.Abstract.used <> [] then
    Color.printf Color.Bright "Unknown (because of abstraction options %a)@.@." Print.(list string) !Flag.Abstract.used
  else
    let pr main_fun =
      let arg_num = Type.arity @@ Id.typ main_fun in
      if arg_num > 0 then
        Format.printf "Input for %a:@.  %a@." Id.print main_fun (print_list Format.pp_print_int "; ") (List.take arg_num ce)
    in
    Color.printf Color.Bright "Unsafe!@.@.";
    Option.may pr main;
    match set_main with
    | None -> ()
    | Some set_main ->
        if not !Flag.Method.slice then
          Format.printf "@[<v 2>Error trace:%a@." Eval.print (ce,set_main)


let rec run_cegar prog =
  try
    match CEGAR.run prog with
    | CEGAR.Safe _env ->
        set_status Flag.Log.Safe;
        Color.printf Color.Bright "Safe!@.@.";
        true
    | CEGAR.Unsafe _ ->
        set_status Flag.Log.Unsafe;
        Color.printf Color.Bright "Unsafe!@.@.";
        false
    | CEGAR.Unknown _ -> unsupported "Main_loop.run_cegar"
  with
  | Fpat.RefTypInfer.FailedToRefineTypes when Flag.Method.(not !insert_param_funarg && not !no_exparam) ->
      Flag.Method.insert_param_funarg := true;
      run_cegar prog
  | Fpat.RefTypInfer.FailedToRefineTypes when Flag.Method.(not !relative_complete && not !no_exparam) ->
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
  | Fpat.RefTypInfer.FailedToRefineTypes when Flag.Method.(not !insert_param_funarg && not !no_exparam) ->
      Flag.Method.insert_param_funarg := true;
      true
  | Fpat.RefTypInfer.FailedToRefineTypes when Flag.Method.(not !relative_complete && not !no_exparam) ->
      Verbose.printf "@.REFINEMENT FAILED!@.";
      Verbose.printf "Restart with relative_complete := true@.@.";
      Flag.Method.relative_complete := true;
      true
  | Fpat.RefTypInfer.FailedToRefineExtraParameters when !Flag.Method.relative_complete && not !Flag.Method.no_exparam ->
      Fpat.RefTypInfer.params := [];
      Fpat.RefTypInfer.prev_sol := [];
      Fpat.RefTypInfer.prev_constrs := [];
      incr Fpat.RefTypInfer.number_of_extra_params;
      true
  | _ ->
      false

let print_result_delimiter () =
  let width =
    let cols =
      try
        Unix.open_and_read_line "tput cols"
        |> int_of_string
      with Failure _ | End_of_file -> !!Format.get_margin
    in
    min cols !!Format.get_margin
  in
  if not !!is_only_result then
    Format.printf "@.%a@.@." Color.s_green (String.make width '=')

let trans_env top_funs make_get_rtyp env : (Syntax.id * Ref_type.t) list =
  let get_rtyp f =
    List.assoc f env
    |@> Debug.printf "trans_env %a: %a@." CEGAR_print.var f CEGAR_ref_type.print
  in
  let aux f = Option.try_any (fun () -> f, Ref_type.rename @@ make_get_rtyp get_rtyp f) in
  List.filter_map aux top_funs

let status_of_result r =
  match r with
  | CEGAR.Safe _env -> Flag.Log.Safe
  | CEGAR.Unsafe _ when Flag.(!mode = NonTermination || !Method.ignore_non_termination) ->
      Flag.Log.Unknown ""
  | CEGAR.Unsafe _ when !Flag.Abstract.used <> [] ->
      Flag.Log.Unknown (Format.asprintf "because of abstraction options %a" Print.(list string) !Flag.Abstract.used)
  | CEGAR.Unsafe _ ->
      Flag.Log.Unsafe
  | CEGAR.Unknown s when String.starts_with s "Error: " ->
      Flag.Log.Error (snd @@ String.split_nth s (String.length "Error: "))
  | CEGAR.Unknown s ->
      Flag.Log.Unknown s

let report ?(delim_first=true) orig parsed multiple {result; stats; make_get_rtyp; set_main; main; info} =
  if delim_first then print_result_delimiter ();
  if multiple then Format.printf "Sub-problem:@.";
  List.iter (Format.printf "  %s@.") info;
  if info <> [] then Format.printf "@.";
  begin
    match result with
    | CEGAR.Safe env ->
        Debug.printf "report env: %a@." Print.(list (CEGAR_print.var * CEGAR_ref_type.print)) env;
        let top_funs = Term_util.get_top_funs @@ Problem.term parsed in
        Debug.printf "report top_funs: %a@." Print.(list id) top_funs;
        let env' = trans_env top_funs make_get_rtyp env in
        Debug.printf "report env': %a@." Print.(list (id * Ref_type.print)) env';
        if Flag.(!mode = FairTermination) => !!Verbose.check then
          if !Flag.Print.result then
            report_safe env' orig parsed
    | CEGAR.Unsafe(sol,_) ->
        if !Flag.Print.result then
          report_unsafe main sol set_main
    | CEGAR.Unknown s when String.starts_with s "Error: " ->
        Color.printf Color.Bright "%s@.@." s
    | CEGAR.Unknown s ->
        Color.printf Color.Bright "Unknown";
        if s <> "" then Color.printf Color.Bright " %s" s;
        Color.printf Color.Bright "@.@."
  end;
  begin
    if multiple then
      match stats with
      | None -> ()
      | Some {cycles; total; abst; mc; refine} ->
          Format.printf "CEGAR-cycles: %d@." cycles;
          Format.printf "total: %.3f sec@." total;
          Format.printf "  abst: %.3f sec@." abst;
          Format.printf "  mc: %.3f sec@." mc;
          Format.printf "  refine: %.3f sec@." refine
  end;
  if not delim_first then print_result_delimiter ()


let check_by_spawn ?(exparam_sol=[]) preprocessed =
  if exparam_sol <> [] then unsupported "check_by_spawn";
  let args = List.filter_out ((=) "-spawn") !Flag.Log.args in
  let bin = {args; preprocessed} in
  let file = Filename.change_extension !!Flag.Input.main @@ Format.sprintf "bin" in
  Marshal.to_file ~flag:[Marshal.Closures] file bin;
  ignore @@ Sys.command @@ Format.sprintf "%s -s -limit %d %s" Sys.argv.(0) !Flag.Limit.time_subproblem file;
  let json_file = Filename.change_extension file "json" in
  let result,info = JSON.load json_file result_of_json in
  add_to_log info;
  make_result result (Some info) preprocessed

let check ?fun_list ?(exparam_sol=[]) pp =
  if !Flag.Experiment.spawn then
    check_by_spawn ~exparam_sol pp
  else
    let preprocessed, make_get_rtyp, set_main, main, info =
      Preprocess.measure_time (cegar_of_preprocessed ?fun_list) pp
    in
    let cegar_prog =
      if Flag.(List.mem !mode [FairTermination;Termination] && !Termination.add_closure_exparam) then
        begin
          Debug.printf "exparam_sol: %a@." Print.(list (id * Format.pp_print_int)) exparam_sol;
          let exparam_sol' = List.map (Pair.map CEGAR_trans.trans_var CEGAR_syntax.make_int) exparam_sol in
          let prog'' = CEGAR_util.map_body_prog (CEGAR_util.subst_map exparam_sol') preprocessed in
          Debug.printf "MAIN_LOOP: %a@." CEGAR_print.prog preprocessed;
          let info = {preprocessed.CEGAR_syntax.info with CEGAR_syntax.exparam_orig=Some preprocessed} in
          {prog'' with CEGAR_syntax.info}
        end
      else
        preprocessed
    in
    let result = CEGAR.run cegar_prog in
    {result; stats=None; make_get_rtyp; set_main; main; info}

let bool_of_return {result} =
  match result with
  | CEGAR.Safe _ -> true
  | CEGAR.Unsafe _ -> false
  | CEGAR.Unknown _ -> false

let result_of_return {result} =
  match result with
  | CEGAR.Safe _ -> Safe
  | CEGAR.Unsafe _ -> Unsafe
  | CEGAR.Unknown _ -> Unknown

let result_of_rtree (t : result_tree) =
  match t with
  | Node(result,_) -> fst result

exception CheckTimeOut

let rec loop ?orig ?make_pps ?fun_list ?exparam_sol problem =
  let preprocessed = run_preprocess ?make_pps problem in
  let print_log_tree () =
    Verbose.printf "Preprocessing:@\n  @[%a@]" Preprocess.print_log_tree preprocessed
  in
  if !Flag.Parallel.num > 1 then
    if Preprocess.exists_or preprocessed then
      unsupported "parallel check for 'or'"
    else
      let pps = Preprocess.lists_of_paths preprocessed in
      Parallel.check ?exparam_sol pps
  else
    let is_singleton = Exception.not_raise Preprocess.get preprocessed in
    try
      let rec eval label acc r : result_tree =
        match r with
        | Preprocess.Before p ->
            if not is_singleton then
              begin
                print_log_tree ();
                Verbose.printf "Start checking sub-problem.@."
              end;
            let r =
              try
                Timer.set_handler (fun _ -> raise CheckTimeOut);
                Timer.set @@ float !Flag.Limit.time_subproblem;
                let r = check ?fun_list ?exparam_sol ((label,p)::acc) in
                Timer.reset ();
                if not is_singleton then report ~delim_first:false orig problem true r;
                r
              with CheckTimeOut ->
                Verbose.printf "@.TIMEOUT: sub-problem@.@.";
                return_of_timeout
            in
            Rose_tree.leaf (result_of_return r, Some r)
        | Preprocess.After {label; problem; op; result} ->
            let acc' = (label,problem)::acc in
            match op with
            | Preprocess.And ->
                let aux (t:result_tree) (acc: (result * result_tree list) Lazy.t) =
                  match result_of_rtree t with
                  | Safe ->
                      let summary,ts = Lazy.force acc in
                      summary, t::ts
                  | r -> r, [t]
                in
                let summary,ts =
                  result
                  |> LazyList.map (eval label acc')
                  |> LazyList.lazy_fold_right aux -$- (lazy (Safe,[]))
                  |> Lazy.force
                in
                Rose_tree.Node((summary, None), ts)
            | Preprocess.Or ->
                let aux (t:result_tree) (acc: (result * result_tree list) Lazy.t) =
                  match result_of_rtree t with
                  | Safe ->
                      Safe, [t]
                  | r ->
                      let summary,ts = Lazy.force acc in
                      match r, summary with
                      | _, Safe -> Safe, ts
                      | Unknown, Unknown -> Unknown, t::ts
                      | Unknown, Unsafe -> Unknown, [t]
                      | Unsafe, Unknown -> Unknown, ts
                      | Unsafe, Unsafe -> Unsafe, t::ts
                      | Safe, _ -> assert false
                in
                let summary,rs =
                  result
                  |> LazyList.map (eval label acc')
                  |> LazyList.lazy_fold_right aux -$- (lazy (Unsafe,[]))
                  |> Lazy.force
                in
                Rose_tree.Node((summary, None), rs)
      in
      let rs = eval Preprocess.Init [] preprocessed in
      print_log_tree ();
      rs
      |> Rose_tree.flatten
      |> List.filter_map snd
    with e ->
           if !!Debug.check then Printexc.print_backtrace stdout;
           if improve_precision e then
             loop ?orig ?make_pps ?fun_list ?exparam_sol problem
           else
             begin
               print_log_tree ();
               raise e
             end

let merge_result b r1 r2 =
  match r1, r2 with
  | CEGAR.Safe _, r
  | r, CEGAR.Safe _ -> r
  | CEGAR.Unsafe _ as r, _
  | _, (CEGAR.Unsafe _ as r) -> r
  | CEGAR.Unknown s1, CEGAR.Unknown s2 when b -> CEGAR.Unknown (Format.sprintf "%s, %s" s1 s2)
  | CEGAR.Unknown _, CEGAR.Unknown _ -> CEGAR.Unknown ""

let run ?make_pps ?fun_list ?orig ?exparam_sol problem =
  let returns = loop ?orig ?make_pps ?fun_list ?exparam_sol problem in
  let result =
    if returns = [] then
      begin
        set_status Flag.Log.Safe;
        if Flag.(!mode = FairTermination) => !!Verbose.check then
          if !Flag.Print.result then
            report_safe [] orig problem;
        CEGAR.Safe []
      end
    else
      let r = List.reduce (merge_result false) @@ List.map (fun r -> r.result) returns in
      set_status @@ status_of_result r;
      r
  in
  let num = List.length returns in
  if !Flag.Print.result then
    begin
      List.iter (report orig problem (num > 1)) returns;
      if num > 1 && !Flag.Parallel.num > 1 then
        report orig problem (List.length returns > 1) {(List.hd returns) with result; stats=None; info=[]};
    end;
  List.for_all bool_of_return returns
