open Util

type return = { result : Preprocess_common.verif_result; info : Problem.info }
and stats = { cycles : int; total : float; abst : float; mc : float; refine : float }

let return_of_timeout = { result = Unknown "TimeOut"; info = Problem.init_info }

let result_of_json json =
  let open JSON.Util in
  let result =
    match json |> member "result" |> to_string with
    | "Safe" -> CEGAR.Safe []
    | "Unsafe" when !Flag.Abstract.over_approx <> [] ->
        CEGAR.Unknown
          (Format.asprintf "because of abstractions %a"
             Print.(list string)
             !Flag.Abstract.over_approx)
    | "Unsafe" -> CEGAR.Unsafe ([], Model_check.CESafety [])
    | r when !Flag.Parallel.continue -> CEGAR.Unknown r
    | r -> failwith "%s" r
  in
  let cycles = json |> member "cycles" |> to_int in
  let total = json |> member "total" |> to_float in
  let abst = json |> member "abst" |> to_float in
  let mc = json |> member "mc" |> to_float in
  let refine = json |> member "refine" |> to_float in
  (result, { cycles; total; abst; mc; refine })

let add_to_log info =
  Flag.Log.cegar_loop := info.cycles + !Flag.Log.cegar_loop;
  Flag.Log.Time.abstraction := info.abst +. !Flag.Log.Time.abstraction;
  Flag.Log.Time.mc := info.mc +. !Flag.Log.Time.mc;
  Flag.Log.Time.cegar := info.refine +. !Flag.Log.Time.cegar
