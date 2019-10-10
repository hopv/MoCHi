open Util
open CEGAR_syntax
open CEGAR_type
open CEGAR_util

exception UnknownOutput

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type apt_transition =
  | APT_True | APT_False
  | APT_State of (int (* branch *) * int (* state ID *))
  | APT_And of apt_transition list
  | APT_Or of apt_transition list

type spec = (string * int) list * (int * string * apt_transition) list

type counterexample_apt = string Rose_tree.t
type counterexample = int list

type result =
  | Safe of (var * Inter_type.t) list
  | UnsafeAPT of counterexample_apt
  | Unsafe of counterexample

module HS = HorSat_syntax


(* returen "" if the version cannot be obtained *)
let version_aux cmd name =
  let cin,cout = Unix.open_process (Format.sprintf "%s /dev/null 2> /dev/null" cmd) in
  let v =
    try
      let s = input_line cin in
      if Str.string_match (Str.regexp (name ^ " \\([.0-9]+\\)")) s 0
      then Some (String.sub s (Str.group_beginning 1) (Str.group_end 1 - Str.group_beginning 1))
      else None
    with Sys_error _ | End_of_file -> None
  in
  match Unix.close_process (cin, cout) with
    Unix.WEXITED(_) | Unix.WSIGNALED(_) | Unix.WSTOPPED(_) -> v
let version () = version_aux !Flag.ModelCheck.horsat "HorSat"


let string_of_arity_map arity_map =
  "%BEGINR\n" ^ String.join "\n" (List.map (fun (f, a) -> f ^ " -> " ^ string_of_int a ^ ".") arity_map) ^ "\n%ENDR\n"

let string_of_parseresult_apt (prerules, arity_map, tr) =
  (HS.string_of_prerules prerules)^"\n"^string_of_arity_map arity_map ^ HS.string_of_transitions_ATA tr

let string_of_parseresult (prerules, tr) =
  (HS.string_of_prerules prerules)^"\n"^(HS.string_of_transitions tr)

let trans_const = function
  | Unit -> HS.PTapp(HS.Name "unit", [])
  | True -> HS.PTapp(HS.FD 0, [])
  | False -> HS.PTapp(HS.FD 1, [])
  | TreeConstr(_,s) -> HS.PTapp(HS.Name s, [])
  | c -> Format.eprintf "trans_const: %a@." CEGAR_print.term (Const c); assert false


let rec trans_id x =
  let x' = String.sign_to_letters x in
  if x'.[0] = '_' then "under_score" ^ x' else x'

let rec trans_term br = function
  | Const c -> trans_const c
  | Var x when Char.is_uppercase x.[0] -> HS.PTapp(HS.NT (trans_id x), [])
  | Var x -> HS.PTapp (HS.Name (trans_id x), [])
  | App(Const (Label n), t) -> HS.PTapp(HS.Name ("l" ^ string_of_int n), [trans_term br t])
  | App(App(App(Const If, Const (Rand(TBool,_))), t2), t3) ->
      HS.PTapp(HS.Name br, [trans_term br t2; trans_term br t3])
  | App(App(App(Const If, t1), t2), t3) ->
      HS.PTapp(HS.CASE 2, [trans_term br t1; trans_term br t2; trans_term br t3])
  | App(t1,t2) ->
      let HS.PTapp(hd, ts1) = trans_term br t1 in
      let t2' = trans_term br t2 in
      HS.PTapp(hd, ts1@[t2'])
  | Fun _ -> assert false
  | Let _ -> assert false

let rec trans_fun_def br (f,xs,t1,es,t2) =
  let rec add_event e t =
    match e with
    | Event s -> HS.PTapp(HS.Name ("event_" ^ s), [t])
    | Branch n -> assert false(* HS.PTapp(HS.Name ("l" ^ string_of_int n), [t])*)
  in
  assert (t1 = Const True);
  trans_id f, List.map trans_id xs, List.fold_right add_event es (trans_term br t2)

let trans_spec_apt (q,e,qs) =
  let aux q = "q" ^ string_of_int q in
  let parens s = "(" ^ s ^ ")" in
  let rec apt_transition_to_string is_top = function
    | APT_True -> "tt"
    | APT_False -> "ff"
    | APT_State(br, q) -> parens (string_of_int br ^ "," ^ aux q)
    | APT_And ts -> let s = String.join "/\\" (List.map (apt_transition_to_string false) ts) in if is_top then s else parens s
    | APT_Or ts -> let s = String.join "\\/" (List.map (apt_transition_to_string false) ts) in if is_top then s else parens s
  in
    (aux q, e), [apt_transition_to_string true qs]

let trans_apt ({defs}, (arity_map, spec)) =
  let defs':HS.prerules = List.map (trans_fun_def "br_forall") defs in
  let spec':HS.transitions = List.map trans_spec_apt spec in
  (defs', arity_map, spec')

let trans_spec (q,e,qs) =
  let aux q = "q" ^ string_of_int q in
  (aux q, e), List.map aux qs

let trans ({defs},spec) =
  let defs':HS.prerules = List.map (trans_fun_def "br") defs in
  let spec':HS.transitions = List.map trans_spec spec in
  (defs', spec')


let trans_ce ce =
  let aux (s,_) =
    match s with
    | "unit" -> []
    | "br" -> []
    | s when s.[0] = 'l' -> [int_of_string @@ String.slice ~first:1 s]
    | s when String.starts_with s "event_" -> []
    | _ -> assert false
  in
  List.flatten_map aux ce


let get_pair s =
  let n1 = String.index s ',' in
  let n2 = String.index s ')' in
  let q = String.sub s 1 (n1-1) in
  let n = int_of_string (String.sub s (n1+1) (n2-n1-1)) in
  let s' = String.sub s (n2+1) (String.length s-n2-1) in
  (q, n), s'

let rec verifyFile_aux cmd filename =
  let default = "empty" in
  let result_file = Filename.change_extension !!Flag.Input.main "horsat_out" in
  let oc = open_out result_file in
  output_string oc default;
  close_out oc;
  let cmd = Format.sprintf "%s %s > %s" cmd filename result_file in
  let r = Sys.command cmd in
  if r = 128+9 then killed();
  let ic = open_in result_file in
  let lb = Lexing.from_channel ic in
  lb.Lexing.lex_curr_p <-
    {Lexing.pos_fname = result_file;
     Lexing.pos_lnum = 1;
     Lexing.pos_cnum = 0;
     Lexing.pos_bol = 0};
  ic, lb

let rec verifyFile cmd parser token filename =
  let ic,lb = verifyFile_aux cmd filename in
  let r =
    try
      parser token lb
    with Parsing.Parse_error ->
      let open Lexing in
      let open Parsing in
      let open Location in
      let loc = curr lb in
      let file = loc.loc_start.pos_fname in
      let line = loc.loc_start.pos_lnum in
      let startchar = loc.loc_start.pos_cnum - loc.loc_start.pos_bol in
      let endchar = loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startchar in
      Format.eprintf "File \"%s\", line %d@?" file line;
      if startchar >= 0 then Format.eprintf ", characters %d-%d@." startchar endchar;
      raise Parse_error
  in
  close_in ic;
  match r with
  | HS.Satisfied env ->
      Safe []
  | HS.UnsatisfiedAPT ce ->
      (*
      let debug = !Flag.debug_level > 0 in
      if debug then Format.printf "Unsatisfied non-terminating condition.@. Counter-example:@. %s@." (HS.string_of_result_tree ce);
      let cexs, ext_cexs = error_trace ce in
      let ppppp fm (n, l) = Format.fprintf fm "[%d: %a]" n (print_list Format.pp_print_bool ",") l in
      if debug then List.iter2 (fun c1 c2 -> Format.printf "FOUND:  %a | %a@." (print_list (fun fm n -> Format.fprintf fm (if n=0 then "then" else "else")) ",") c1 (print_list ppppp ",") c2) cexs ext_cexs;
       (*let ext_cexs = List.map (fun _ -> [Fpat.Idnt.V("tmp"), []]) cexs (* TODO: Implement *) in*)
       *)
      UnsafeAPT ce
  | HS.Unsatisfied ce ->
      let ce' =
        let module QC = Flag.Experiment.HORS_quickcheck in
        match !QC.use with
        | None -> ce
        | Some use ->
            let option =
              match use with
              | QC.Shortest -> "-shortest"
              | QC.Longest -> "-longest"
              | QC.LowestCoverage -> "-lowest-coverage"
              | QC.HighestCoverage -> "-highest-coverage"
            in
            let cmd = Format.sprintf "%s %s %d %s" !QC.command filename !Flag.Experiment.HORS_quickcheck.num option in
            let r = Time.measure_and_add Flag.Log.Time.hors_quickcheck (Unix.CPS.open_process_in cmd) IO.input_all in
            let ce =
              r
              |> String.trim
              |> String.split_on_char '\n'
              |> List.map (String.split_on_char ';'
                           |- List.map (String.split_on_char ',')
                           |- List.map (function [s;n] -> s, int_of_string n | _ -> assert false))
              |> List.sort (Compare.on List.length)
              |> List.hd
            in
            Flag.Experiment.HORS_quickcheck.(cex_length_history := List.length ce :: !cex_length_history);
            ce
      in
      Unsafe (trans_ce ce')


let write_log string_of filename target =
  let cout = open_out filename in
  output_string cout @@ string_of target;
  close_out cout


let check_apt_aux cmd parser token target =
  let target' = trans_apt target in
  let ext =
    if !Flag.ModelCheck.rename_hors then
      string_of_int !Flag.Log.cegar_loop ^ ".hors"
    else
      "hors"
  in
  let input = Filename.change_extension !!Flag.Input.main ext in
  try
    Debug.printf "%s@." @@ string_of_parseresult_apt target';
    write_log string_of_parseresult_apt input target';
    verifyFile cmd parser token input
  with Failure("lex error") -> raise UnknownOutput
let check_apt = check_apt_aux !Flag.ModelCheck.horsat HorSat_parser.output_apt HorSat_lexer.token

let check_aux cmd parser token target =
  let target' = trans target in
  let ext =
    if !Flag.ModelCheck.rename_hors then
      string_of_int !Flag.Log.cegar_loop ^ ".hors"
    else
      "hors"
  in
  let input = Filename.change_extension !!Flag.Input.main ext in
  try
    Debug.printf "%s@." @@ string_of_parseresult target';
    write_log string_of_parseresult input target';
    verifyFile cmd parser token input
  with Failure("lex error") -> raise UnknownOutput
let check = check_aux !Flag.ModelCheck.horsat HorSat_parser.output HorSat_lexer.token


let rec make_label_spec = function
  | [] -> []
  | r::rs -> (0, r, APT_State(1, 0)) :: make_label_spec rs

let make_apt_spec labels =
  let spec =
    (0,"event_fail", APT_False)
    ::(0,"unit", APT_True)
    ::(0, "l0", APT_State(1, 0))
    ::(0, "l1", APT_State(1, 0))
    ::(0, "tt", APT_State(1, 0))
    ::(0, "ff", APT_State(1, 0))
    ::(0,"br_forall", APT_And([APT_State(1, 0); APT_State(2, 0)]))
    ::(0,"br_exists", APT_Or([APT_State(1, 0); APT_State(2, 0)]))::make_label_spec labels
  in
  List.sort compare spec

let make_arity_map labels =
  let init = [("br_forall", 2); ("br_exists", 2); ("event_fail", 1); ("unit", 0); ("tt", 1); ("ff", 1); ("l0", 1); ("l1", 1)] in
  let funs_map = List.map (fun l -> (l, 1)) labels in
  init @ funs_map

let make_spec_nonterm labels =
  make_arity_map labels, make_apt_spec labels

let make_spec = TrecsInterface.make_spec
