open Util

module Verbose = Debug.Make (struct
  let check () = !Flag.Print.progress
end)

module MVerbose = Debug.Make (struct
  let check () = !Flag.Print.modular_progress
end)

module Temp = struct
  let dir_ref : Fpath.t option ref = ref None

  let dir () =
    match !dir_ref with
    | Some dir -> dir
    | None -> (
        match Bos.OS.Dir.tmp "mochi_%s" with
        | Ok dir ->
            dir_ref := Some dir;
            dir
        | Error msg -> failwith "%a" Rresult.R.pp_msg msg)

  let file s = Fpath.add_seg !!dir s
  let ext s = Filename.basename !!Flag.IO.main |> Fpath.add_seg !!dir |> Fpath.set_ext s

  module S = struct
    let dir () = Fpath.to_string !!dir
    let file s = Fpath.to_string @@ file s
    let ext s = Fpath.to_string @@ ext s
  end
end

let set_print_target s =
  let fm = s |> open_out |> Format.formatter_of_out_channel in
  Flag.Print.target := fm;
  Verbose.set_default_formatter fm;
  MVerbose.set_default_formatter fm;
  Flag.PrettyPrinter.color := false

let set_only_result () =
  Flag.Print.progress := false;
  Flag.Print.modular_progress := false

let is_only_result () = (not !Flag.Print.progress) && not !Flag.Print.modular_progress

let set_silent () =
  set_only_result ();
  Flag.Print.result := false

let is_silent () = !!is_only_result && not !Flag.Print.result

let set_status s =
  Flag.Log.result := s;
  let filename = Temp.S.ext "status" in
  let f = if !Flag.Limit.time = 0 then -1. else !!Time.get /. float_of_int !Flag.Limit.time in
  let text = Format.sprintf "%.2f,%s" f (Flag.Log.string_of_result true) in
  IO.output_file ~filename ~text

let check_env () =
  if !!Flag.need_model_checker then
    if List.for_all Option.is_none Flag.ModelCheck.[ !trecs; !horsat; !horsat2; !horsatp ] then
      failwith "Model checker not found";
  (if !Flag.Refine.use_rec_chc_solver then
     match !Flag.Refine.solver with
     | Flag.Refine.Hoice -> if !Flag.Refine.hoice = None then failwith "HoIce not found"
     | Flag.Refine.Z3 | Flag.Refine.Z3_spacer ->
         if !Flag.Refine.z3 = None then failwith "Z3 binary not found");
  if Flag.Experiment.HORS_quickcheck.(!use <> None) then
    if !Flag.Experiment.HORS_quickcheck.command = None then failwith "hors_quickcheck not found";
  if !Flag.NonTermination.use_omega then
    if !Flag.External.omega = None then failwith "Omega Calculator not found"

let find_binaries () =
  let find s =
    match Bos.(OS.Cmd.find_tool (Result.get_ok (Bos.Cmd.of_string s))) with
    | Ok (Some path) -> Some (Fpath.to_string path)
    | _ -> None
  in
  Flag.External.omega := find "oc";
  Flag.External.cvc3 := find "cvc3";
  Flag.Refine.hoice := find "hoice";
  Flag.Refine.z3 := find "z3";
  Flag.Refine.z3_spacer := Option.map (fun s -> s ^ " fixedpoint.engine=spacer") !Flag.Refine.z3;
  Flag.ModelCheck.trecs := find "trecs";
  Flag.ModelCheck.horsat := find "horsat";
  Flag.ModelCheck.horsat2 := find "horsat2";
  Flag.ModelCheck.horsatp := find "horsatp";
  Flag.Experiment.HORS_quickcheck.command := find "hors_quickcheck"
