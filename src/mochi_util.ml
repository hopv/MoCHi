open Util

module Verbose = Debug.Make(struct let check () = !Flag.Print.progress end)
module MVerbose = Debug.Make(struct let check () = !Flag.Print.modular_progress end)

let set_print_target s =
  let fm =
    s
    |> open_out
    |> Format.formatter_of_out_channel
  in
  Flag.Print.target := fm;
  Verbose.set_default_formatter fm;
  MVerbose.set_default_formatter fm;
  Flag.PrettyPrinter.color := false

let set_only_result () =
  Flag.Print.progress := false;
  Flag.Print.modular_progress := false
let is_only_result () =
  not !Flag.Print.progress &&
  not !Flag.Print.modular_progress

let set_silent () =
  set_only_result ();
  Flag.Print.result := false
let is_silent () =
  !!is_only_result && not !Flag.Print.result

let set_status s =
  Flag.Log.result := s;
  let filename = Filename.change_extension !!Flag.IO.temp "status" in
  let f = if !Flag.Limit.time = 0 then -1. else !!Time.get /. float_of_int !Flag.Limit.time in
  let text = Format.sprintf "%.2f,%s" f (Flag.Log.string_of_result true) in
  IO.output_file ~filename ~text
