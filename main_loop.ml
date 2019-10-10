open Util
open Mochi_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)


type return =
    {result : CEGAR.result;
     stats : stats option;
     make_get_rtyp : (CEGAR_syntax.var -> CEGAR_ref_type.t) -> Syntax.id -> Ref_type.t;
     set_main: Problem.t option;
     main: Syntax.id option;
     info: Problem.info}
and stats =
  {cycles : int;
   total : float;
   abst : float;
   mc : float;
   refine : float}

let cegar_of_preprocessed ?fun_list spec results =
  let set_main = Option.map fst @@ List.assoc_option Preprocess.Set_main results in
  let main = Option.(set_main >>= return-|Problem.term >>= Trans.get_set_main)  in
  let problem = Preprocess.last_problem results in
  let fun_list' =
    match fun_list with
    | None ->
        begin
          try
            let t = Problem.term Preprocess.(take_result Decomp_pair_eq results) in
            Term_util.get_top_funs t
          with Not_found -> []
        end
    | Some fun_list' -> fun_list'
  in

  let prog,map,_,make_get_rtyp_trans = CEGAR_trans.trans_prog problem in
  let abst_cegar_env =
    Spec.get_abst_cegar_env spec prog
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
      let aux x = List.assoc_option (CEGAR_trans.trans_var x) map in
      List.filter_map aux fun_list'
    in
    let inlined = List.map CEGAR_trans.trans_var spec.Spec.inlined in
    let fairness =
      if Flag.Method.(!mode = FairNonTermination) then
        Some spec.Spec.fairness
      else
        None
    in
    CEGAR_syntax.{prog.info with orig_fun_list; inlined; fairness}
  in
  CEGAR_syntax.{prog with info}, make_get_rtyp, set_main, main, problem.Problem.info


let run_preprocess ?make_pps spec problem =
  let pps' =
    match make_pps with
    | None -> Preprocess.all spec
    | Some make_pps' -> make_pps' spec
  in
  Preprocess.run_problem pps' problem


let write_annot env orig =
  env
  |> List.map (Pair.map_fst Id.name)
  |> WriteAnnot.f !!Flag.Input.main orig

let report_safe env orig {Problem.term=t0} =
  if !Flag.PrettyPrinter.write_annot then Option.iter (write_annot env) orig;

  let s =
    match !Flag.Method.mode with
    | Flag.Method.NonTermination -> "Non-terminating!"
    | Flag.Method.FairNonTermination -> "Fair Infinite Execution found!"
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

  if env <> [] && Flag.Method.(!mode <> Termination) then
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
  Color.printf Color.Bright "%s@.@." (Flag.Log.string_of_result false);
  if !Flag.Encode.used_abst = [] then
    let pr main_fun =
      let arg_num = Type.arity @@ Id.typ main_fun in
      if arg_num > 0 then
        Format.printf "Input for %a:@.  %a@." Id.print main_fun (print_list Format.pp_print_int "; ") (List.take arg_num ce)
    in
    Option.may pr main;
    match set_main with
    | None -> ()
    | Some set_main -> Format.printf "@[<v 2>Error trace:%a@." Eval.print (ce,set_main)

(** TODO: merge with report_unsafe *)
let report_unsafe_par main ce set_main =
  if !Flag.Encode.used_abst = [] then
    begin
      Color.printf Color.Bright "Unsafe@.@.";
      report_unsafe main ce set_main
    end
  else
    Color.printf Color.Bright "Unknown@.@.";
    let pr main_fun =
      let arg_num = Type.arity @@ Id.typ main_fun in
      if arg_num > 0 then
        Format.printf "Input for %a:@.  %a@." Id.print main_fun (print_list Format.pp_print_int "; ") (List.take arg_num ce)
    in
    Option.may pr main;
    match set_main with
    | None -> ()
    | Some set_main -> Format.printf "@[<v 2>Error trace:%a@." Eval.print (ce,set_main)


let rec run_cegar prog =
  try
    match CEGAR.run prog with
    | CEGAR.Safe env ->
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
      Flag.Method.insert_param_funarg := true
  | Fpat.RefTypInfer.FailedToRefineTypes when not !Flag.Method.relative_complete && not !Flag.Method.no_exparam ->
      Verbose.printf "@.REFINEMENT FAILED!@.";
      Verbose.printf "Restart with relative_complete := true@.@.";
      Flag.Method.relative_complete := true
  | Fpat.RefTypInfer.FailedToRefineExtraParameters when !Flag.Method.relative_complete && not !Flag.Method.no_exparam ->
      Fpat.RefTypInfer.params := [];
      Fpat.RefTypInfer.prev_sol := [];
      Fpat.RefTypInfer.prev_constrs := [];
      incr Fpat.RefTypInfer.number_of_extra_params
  | _ -> raise e

let print_result_delimiter () =
  if not !!is_only_result then
    Format.printf "@.%s@.@." @@ String.make !!Format.get_margin '='

let trans_env top_funs make_get_rtyp env : (Syntax.id * Ref_type.t) list =
  let get_rtyp f =
    List.assoc f env
    |@> Debug.printf "trans_env %a: %a@." CEGAR_print.var f CEGAR_ref_type.print
  in
  let aux f = Option.try_any (fun () -> f, Ref_type.rename @@ make_get_rtyp get_rtyp f) in
  List.filter_map aux top_funs

let status_of_result r =
  match r with
  | CEGAR.Safe env -> Flag.Log.Safe
  | CEGAR.Unsafe _ when Flag.Method.(!mode = NonTermination || !ignore_non_termination) ->
      Flag.Log.Unknown ""
  | CEGAR.Unsafe _ when !Flag.Encode.used_abst <> [] ->
      Flag.Log.Unknown (Format.asprintf "because of abstraction options %a" Print.(list string) !Flag.Encode.used_abst)
  | CEGAR.Unsafe _ ->
      Flag.Log.Unsafe
  | CEGAR.Unknown s when String.starts_with s "Error: " ->
      Flag.Log.Error (snd @@ String.split_nth s (String.length "Error: "))
  | CEGAR.Unknown s ->
      Flag.Log.Unknown s

let report orig parsed num i {result; stats; make_get_rtyp; set_main; main; info} =
  print_result_delimiter ();
  if num > 1 then
    begin
      match i with
      | None -> Format.printf "Whole result:@."
      | Some i -> Format.printf "Sub-problem %d/%d:@." i num
    end;
  List.iter (Format.printf "%s@.") info;
  if info <> [] then Format.printf "@.";
  begin
    match result with
    | CEGAR.Safe env ->
        Debug.printf "report env: %a@." Print.(list (CEGAR_print.var * CEGAR_ref_type.print)) env;
        let top_funs = Term_util.get_top_funs @@ Problem.term parsed in
        Debug.printf "report top_funs: %a@." Print.(list id) top_funs;
        let env' = trans_env top_funs make_get_rtyp env in
        Debug.printf "report env': %a@." Print.(list (id * Ref_type.print)) env';
        if Flag.Method.(!mode = FairTermination) => !!Verbose.check then
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
  if num > 1 then
    match stats with
    | None -> ()
    | Some {cycles; total; abst; mc; refine} ->
        Format.printf "CEGAR-cycles: %d@." cycles;
        Format.printf "total: %.3f sec@." total;
        Format.printf "  abst: %.3f sec@." abst;
        Format.printf "  mc: %.3f sec@." mc;
        Format.printf "  refine: %.3f sec@." refine


let check ?fun_list ?(exparam_sol=[]) spec pp =
  let preprocessed, make_get_rtyp, set_main, main, info = cegar_of_preprocessed ?fun_list spec pp in
  let cegar_prog =
    if Flag.(Method.(List.mem !mode [FairTermination;Termination]) && !Termination.add_closure_exparam) then
      begin
        Debug.printf "exparam_sol: %a@." (List.print @@ Pair.print Id.print Format.pp_print_int) exparam_sol;
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


type bin_input =
    {args : string list;
     preprocessed : Preprocess.result list}

exception QuitWithUnsafe

let check_parallel ?fun_list ?(exparam_sol=[]) spec pps =
  if !Flag.Print.progress
  then Color.printf Color.Green "Verifying sub-problems in parallel ... @?";
  if exparam_sol <> [] then unsupported "check_parallel";
  if spec.Spec.abst_cegar_env <> [] then unsupported "check_parallel";
  let problem i preprocessed =
    let input = Filename.change_extension !!Flag.Input.main @@ Format.sprintf "%d.bin" i in
    let status = Filename.change_extension input "status" in
    let cmd = Format.sprintf "%s -s -limit %d %s" Sys.argv.(0) !Flag.Parallel.time input in
    i, (input, status, cmd, preprocessed)
  in
  let problems = List.mapi problem pps in
  let prepare (_,(input,status,_,preprocessed)) =
    let args = !Flag.Log.args in
    let bin = {args; preprocessed} in
    Marshal.to_file ~flag:[Marshal.Closures] input bin;
    IO.empty_file status
  in
  let len = List.length pps in
  List.iter prepare problems;
  let print_status (i,(_,status,_,_)) =
    let s = BatPervasives.input_file status in
    let f,st =
      try
        let f,st = String.split s ~by:"," in
        float_of_string f, st
      with _ -> -1., s
    in
    if f < 0. then
      Verbose.printf "%d: %-40s@." i st
    else
      let len = 40 in
      let l = int_of_float (0.5 +. f *. float_of_int len) in
      let l' = min l len in
      let s1 = String.make l' '#' in
      let s2 =
        let finished = List.exists (String.starts_with st) ["Done: ";"Error: "] in
        String.make (len - l') (if finished then '#' else ' ')
      in
      Verbose.printf "%d: [%s%s]  %-40s@." i s1 s2 st
  in
  let b = Unix.isatty Unix.stdout in
  let result_of i =
    let input,_,_,_ = List.assoc i problems in
    let file = Filename.change_extension input "json" in
    let of_json json =
      let open JSON.Util in
      let result =
        match json |> member "result" |> to_string with
        | "Safe" -> CEGAR.Safe []
        | "Unsafe" when !Flag.Encode.used_abst <> [] -> CEGAR.Unknown (Format.asprintf "because of abstraction options %a" Print.(list string) !Flag.Encode.used_abst)
        | "Unsafe" -> CEGAR.Unsafe([], ModelCheck.CESafety [])
        | r when !Flag.Parallel.continue -> CEGAR.Unknown r
        | r -> failwith r
      in
      let cycles = json |> member "cycles" |> to_int in
      let total = json |> member "total" |> to_float in
      let abst = json |> member "abst" |> to_float in
      let mc = json |> member "mc" |> to_float in
      let refine = json |> member "refine" |> to_float in
      Flag.Log.cegar_loop := cycles + !Flag.Log.cegar_loop;
      Flag.Log.Time.abstraction := abst +. !Flag.Log.Time.abstraction;
      Flag.Log.Time.mc := mc +. !Flag.Log.Time.mc;
      Flag.Log.Time.cegar := refine +. !Flag.Log.Time.cegar;
      result, Some {cycles; total; abst; mc; refine}
    in
    JSON.load file of_json
  in
  let finished = ref [] in
  let rec wait running =
    let pid,st = Unix.(waitpid [WNOHANG] (-1)) in
    if b then List.iter print_status problems;
    if b then Verbose.printf "%a" Cursor.up_begin len;
    if pid = 0 then
      wait running
    else
      let i = List.assoc pid running in
      let r = result_of i in
      let is_safe = match r with CEGAR.Safe _, _ -> true | _ -> false in
      finished := (i,r) :: !finished;
      if not (is_safe || !Flag.Parallel.continue) then raise QuitWithUnsafe;
      pid, st
  in
  if b then Verbose.printf "%t" Cursor.hide;
  Exception.finally (fun () -> if b then Verbose.printf "%t%a" Cursor.show Cursor.down len)
                    (Unix.parallel ~wait !Flag.Parallel.num)
                    (List.map (fun (_,(_,_,cmd,_)) -> cmd) problems);
  if !Flag.Print.progress then Color.printf Color.Green "DONE!@.@.";
  let result_of (i,(input,status,cmd,preprocessed)) =
    let result,stats = List.assoc_default (CEGAR.Unknown "", None) i !finished in
    let make_get_rtyp _ _ = unsupported "check_parallel" in
    let set_main = None in
    let main = None in
    let info = (Preprocess.last_problem preprocessed).Problem.info in
    {result; stats; make_get_rtyp; set_main; main; info}
  in
  List.map result_of problems

let rec loop ?make_pps ?fun_list ?exparam_sol spec problem =
  let preprocessed = run_preprocess ?make_pps spec problem in
  if !Flag.Parallel.num > 1 && preprocessed <> [] then
    check_parallel ?fun_list ?exparam_sol spec preprocessed
  else
    try
      List.map (check ?fun_list ?exparam_sol spec) preprocessed
    with e ->
         if !!Debug.check then Printexc.print_backtrace stdout;
         improve_precision e;
         loop ?make_pps ?fun_list ?exparam_sol spec problem

let merge_result b r1 r2 =
  match r1, r2 with
  | CEGAR.Safe _, r
  | r, CEGAR.Safe _ -> r
  | CEGAR.Unsafe _ as r, _
  | _, (CEGAR.Unsafe _ as r) -> r
  | CEGAR.Unknown s1, CEGAR.Unknown s2 when b -> CEGAR.Unknown (Format.sprintf "%s, %s" s1 s2)
  | CEGAR.Unknown _, CEGAR.Unknown _ -> CEGAR.Unknown ""

let run ?make_pps ?fun_list ?orig ?exparam_sol ?(spec=Spec.init) parsed =
  let results = loop ?make_pps ?fun_list ?exparam_sol spec parsed in
  let bool_of_result {result; make_get_rtyp; set_main; main} =
    match result with
    | CEGAR.Safe _ -> true
    | CEGAR.Unsafe _ -> false
    | CEGAR.Unknown _ -> false
  in
  let r =
    if results = [] then
      begin
        set_status Flag.Log.Safe;
        if Flag.Method.(!mode = FairTermination) => !!Verbose.check then
          if !Flag.Print.result then
            report_safe [] orig parsed;
        CEGAR.Safe []
      end
    else
      let r = List.reduce (merge_result false) @@ List.map (fun r -> r.result) results in
      set_status @@ status_of_result r;
      r
  in
  let num = List.length results in
  if !Flag.Print.result then
    List.iteri (fun i -> report orig parsed num (Some (i+1))) results;
  if !Flag.Print.result && num > 1 && !Flag.Parallel.num > 1 then
    report orig parsed (List.length results) None {(List.hd results) with result=r; stats=None; info=[]};
  List.for_all bool_of_result results
