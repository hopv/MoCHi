open Util
open Mochi_util
open CEGAR_syntax
open CEGAR_type
open CEGAR_util

exception UnknownOutput

exception HorSatPVersionError

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let version () =
  let cin,cout = Unix.open_process (Format.sprintf "%s --version 2> /dev/null" !Flag.ModelCheck.horsatp) in
  let v =
    try
      Some (input_line cin)
    with Sys_error _ | End_of_file -> None in
  ignore(Unix.close_process (cin, cout));
  v

let required_ver = "1.1.0"

(* Syntax for Alternating Parity Tree automata *)
type state = string
type symbol = string
type priority = state * int

type label =
  | Ev of string
  | Br_A
  | Br_E
  | L of int
  | Tt
  | Ff
  | End

let string_of_label = function
  | Ev x -> x
  | Br_A -> "br_forall"
  | Br_E -> "br_exists"
  | L i  -> "l"^(string_of_int i)
  | Tt   -> "tt"
  | Ff   -> "ff"
  | End  -> "unit"

type formula =
  | True | False
  | Label of int * symbol
  | And of formula * formula
  | Or  of formula * formula

let rec string_of_formula = function
  | True  -> "true"
  | False -> "false"
  | Label (i, q) -> "(" ^ string_of_int i ^ ", " ^ q ^ ")"
  | And (f1, f2) -> "(" ^ string_of_formula f1 ^ " /\\ " ^ string_of_formula f2 ^ ")"
  | Or  (f1, f2) -> "(" ^ string_of_formula f1 ^ " \\/ " ^ string_of_formula f2 ^ ")"

type transition = state * symbol * formula
type spec = transition list * priority list

type result =
  | Satisfied | Unsatisfied

let make_apt events (a, b) =
  let q0, q1, q2 = "q0", "q1", "q2" in
  let rec trans = function
    | Ev x when x = a -> Label (1, q1)
    | Ev x when x = b -> Label (1, q2)
    | Ev x when x = "event_fail" -> False
    | Ev _ -> Label (1, q0)
    | Br_A -> And (Label (1, q0), Label (2, q0))
    | Br_E -> Or  (Label (1, q0), Label (2, q0))
    | L _ | Tt | Ff -> Label (1, q0)
    | End  -> False
  in
  let default_sym = [Br_A; Br_E; L 0; L 1; End; Tt; Ff] in
  let syms  = [Ev a; Ev b] @ events @ default_sym in
  let states = [q0; q1; q2] in
  let omega = List.sort compare [(q0, 0); (q1, 1); (q2, 2)] in
  let delta =
    List.map
      (fun state ->
        List.map
          (fun sym ->
            (state, string_of_label sym, trans sym))
          syms
      )
      states in
  let delta' = List.sort compare (List.flatten delta) in
  delta', omega

(** make APT from streett fairness constraints *)
let make_fair_nonterm_spec labels streett : spec =
  if List.length streett <> 1 then
    (Format.eprintf "Error: size of fairness constraints list must be 1";
     assert false);
  let a, b = List.hd streett in
  let ev_a, ev_b = "event_"^a, "event_"^b in
  let events = List.filter_map
    (fun e ->
      if e <> ev_a && e <> ev_b then
        Some (Ev e)
      else
        None)
    labels in
  make_apt events (ev_a, ev_b)


(*********************************)
(* Execute Model Checking *)

let trans_spec (delta, priority) =
  let string_of_delta ds =
    String.join "\n" (List.map (fun (q, a, formula) -> q ^ " " ^ a ^ " -> " ^ (string_of_formula formula) ^ ".") ds)
  in
  String.join "\n" [
    "%TRANSITION";
    string_of_delta delta;
    "%PRIORITY";
    (String.join ".\n" (List.map
                          (fun (q, m) -> q ^ " -> " ^ string_of_int m)
                          priority))^".";
  ]

(** transform HORS and spec to string *)
let trans ({defs}, spec) =
  let defs':HorSat_syntax.prerules = List.map (HorSatInterface.trans_fun_def "br_forall") defs in
  let spec' = trans_spec spec in
  let prerules = String.join ".\n" (List.map HorSat_syntax.string_of_prerule defs') in
  "%GRAMMAR\n"^ prerules ^".\n" ^ spec'

(** write HORS and spec into "*.hors" file *)
let write_log filename target =
  let cout = open_out filename in
  output_string cout target;
  close_out cout

let read_as_string in_channel =
  let result = ref "" in
  try
    while true do
      let line = input_line in_channel in
      result := (!result)^line
    done;
    !result
  with End_of_file ->
    close_in in_channel;
    !result

let rec verifyFile_aux filename =
  let default = "empty" in
  let result_file = Filename.change_extension !!Flag.Input.main "horsatp_out" in
  let oc = open_out result_file in
  output_string oc default;
  close_out oc;
  let ver = Option.get @@ version () in
  if ver < required_ver then
    (Format.printf "HorSatP: minimum version required is %s, but %s@." required_ver ver;
     raise HorSatPVersionError);
  let cmd = Format.sprintf "%s --iter=10000 %s > %s 2>/dev/null" !Flag.ModelCheck.horsatp filename result_file in
  ignore @@ Sys.command cmd;
  let ic = open_in result_file in
  read_as_string ic

(** run HorSatP on `filename` *)
let verifyFile filename =
  let r = verifyFile_aux filename in
  Verbose.eprintf "[Info] HorSatP returned \"%s\"@." r;
  match r with
  | "Satisfied"   | "safe"   -> Satisfied
  | "Unsatisfied" | "unsafe" -> Unsatisfied
  | _ -> failwith "Return value from HorSatP is invalid"

(**
   Execute model checking by HorSatP
   target = (HORS, APT)
*)
let check target =
  let target' = trans target in
  let ext =
    if !Flag.ModelCheck.rename_hors then
      string_of_int !Flag.Log.cegar_loop ^ ".hors"
    else
      "hors"
  in
  let input = Filename.change_extension !!Flag.Input.main ext in
  try
    Debug.printf "%s." target';
    write_log input target';
    verifyFile input
  with Failure("lex error") -> raise UnknownOutput


(*********************************)


(** Get rewriting rules that generate counter-example tree *)
let read_HORS_file filename =

  let show_error_pos fname filebuf =
    let pos = filebuf.Lexing.lex_start_p in
    Format.eprintf "File \"%s\", line %d, character %d:@."
      fname
    pos.Lexing.pos_lnum
      (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1) in

  let inchan = open_in filename in
  let filebuf = Lexing.from_channel inchan in
  try
    let rules = HORS_parser.top HORS_lexer.token filebuf in
    rules
  with _ ->
    show_error_pos filename filebuf;
    let s = Lexing.lexeme filebuf in
    Format.eprintf "error: syntax error near '%s'@." s;
    if s = "->" then
      Format.eprintf "Did you forget '.' at end of line?@.";
    assert false
