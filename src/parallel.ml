open Util
open Mochi_util
open Main_loop_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

exception QuitWithUnsafe

let result_of i problems =
  let input,_,_,_ = List.assoc i problems in
  let file = Filename.change_extension input "json" in
  let result,info = JSON.load file result_of_json in
  add_to_log info;
  result, info

let print_status (i,(_,status,_,_)) =
  let s = BatPervasives.input_file status in
  let f,st =
    try
      let f,st = String.split s ~by:"," in
      float_of_string f, st
    with Failure "float_of_string" -> -1., s
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

let make_wait isatty num problems finished =
  let rec wait running =
    let pid,st = Unix.(waitpid [WNOHANG] (-1)) in
    if isatty then List.iter print_status problems;
    if isatty then Verbose.printf "%a" Cursor.up_begin num;
    if pid = 0 then
      wait running
    else
      let i = List.assoc pid running in
      let r = result_of i problems in
      let is_safe = match r with CEGAR.Safe _, _ -> true | _ -> false in
      finished := (i, r) :: !finished;
      if not (is_safe || !Flag.Parallel.continue) then raise QuitWithUnsafe;
      pid, st
  in
  wait

let make_problem i preprocessed =
  let file = Filename.change_extension !!Flag.IO.temp @@ Format.sprintf "%d.bin" i in
  let status = Filename.change_extension file "status" in
  let cmd = Format.sprintf "%s -s -limit %d %s" Sys.argv.(0) !Flag.Parallel.time file in
  i, (file, status, cmd, preprocessed)

(* make the binary input file *.bin and empty the status file *)
let prepare (_,(file,status,_,preprocessed)) =
  let bin =
    let args = !Flag.Log.args in
    {args; preprocessed}
  in
  Marshal.to_file ~flag:[Marshal.Closures] file bin;
  IO.empty_file status

let check ?(exparam_sol=[]) pps =
  if exparam_sol <> [] then unsupported "Parallel.check";

  let isatty = Unix.isatty Unix.stdout in
  let finished = ref [] in
  let num = List.length pps in

  Verbose.printf ~color:Green "Verifying sub-problems in parallel ... @?";

  let problems = List.mapi make_problem pps in
  List.iter prepare problems;
  let wait = make_wait isatty num problems finished in
  if isatty then Verbose.printf "%t" Cursor.hide;
  let commands = List.map (fun (_,(_,_,cmd,_)) -> cmd) problems in
  Exception.finally
    (fun () -> if isatty then Verbose.printf "%t%a" Cursor.show Cursor.down num)
    (Unix.parallel ~wait !Flag.Parallel.num) commands;
  Verbose.printf ~color:Green "DONE!@.@.";

  let result_of (i,(_file,_status,_cmd,preprocessed)) =
    let result,stats =
      !finished
      |> List.map (fun (i,(r,s)) -> i, (r, Some s))
      |> List.assoc_default (CEGAR.Unknown "", None) i
    in
    make_result result stats preprocessed
  in
  List.map result_of problems
