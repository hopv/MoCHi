include HorSatInterface

let version () = version_aux !Flag.ModelCheck.horsat2 "HorSat2"
let check_apt t = check_apt_aux !Flag.ModelCheck.horsat2 HorSat2_parser.output_apt HorSat2_lexer.token t
let check t = check_aux !Flag.ModelCheck.horsat2 HorSat2_parser.output HorSat2_lexer.token t
