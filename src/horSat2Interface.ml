include HorSatInterface

let version () = version_aux !Flag.ModelCheck.horsat2 "HorSat2"
let options = "-merge"

let cmd_of cmd =
  match cmd with None -> failwith "HorSat2 not found" | Some cmd -> cmd ^ " " ^ options

let check_apt t =
  let cmd = cmd_of !Flag.ModelCheck.horsat2 in
  check_apt_aux cmd HorSat2_parser.output_apt HorSat2_lexer.token t

let check_safety t =
  let cmd = cmd_of !Flag.ModelCheck.horsat2 in
  check_aux cmd HorSat2_parser.output HorSat2_lexer.token t
