open Util

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

let return_of_timeout =
  {result = CEGAR.Unknown "TimeOut";
   stats = None;
   make_get_rtyp = (fun _ -> assert false);
   set_main = None;
   main = None;
   info = Problem.init_info}

type bin_input =
    {args : string list;
     preprocessed : Preprocess.path}

let result_of_json json =
  let open JSON.Util in
  let result =
    match json |> member "result" |> to_string with
    | "Safe" -> CEGAR.Safe []
    | "Unsafe" when !Flag.Abstract.used <> [] -> CEGAR.Unknown (Format.asprintf "because of abstraction options %a" Print.(list string) !Flag.Abstract.used)
    | "Unsafe" -> CEGAR.Unsafe([], ModelCheck.CESafety [])
    | r when !Flag.Parallel.continue -> CEGAR.Unknown r
    | r -> failwith r
  in
  let cycles = json |> member "cycles" |> to_int in
  let total = json |> member "total" |> to_float in
  let abst = json |> member "abst" |> to_float in
  let mc = json |> member "mc" |> to_float in
  let refine = json |> member "refine" |> to_float in
  result, {cycles; total; abst; mc; refine}

let make_result
      ?(make_get_rtyp = fun _ _ -> unsupported "Main_loop_util.make_result")
      ?set_main
      ?main
      result
      stats
      preprocessed
  =
  let {Problem.info} = Preprocess.last_problem preprocessed in
  {result; stats; make_get_rtyp; set_main; main; info}

let add_to_log info =
  Flag.Log.cegar_loop := info.cycles + !Flag.Log.cegar_loop;
  Flag.Log.Time.abstraction := info.abst +. !Flag.Log.Time.abstraction;
  Flag.Log.Time.mc := info.mc +. !Flag.Log.Time.mc;
  Flag.Log.Time.cegar := info.refine +. !Flag.Log.Time.cegar;
