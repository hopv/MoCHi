(* from trecs-1.22/syntax.ml *)

type head = Name of string | NT of string | FD of int | CASE of int | PAIR | DPAIR
type preterm = PTapp of head * preterm list
type prerule = string * string list * preterm
type prerules = prerule list
type transition = (string * string) * string list
type transitions = transition list

type result = Safe of (string * Inter_type.t) list | Unsafe of (string * int) list | TimeOut

let string_of_head h =
  match h with
    Name(s) -> s
  | NT(s) -> s
  | FD(n) -> (string_of_int n)
  | CASE(n) -> "_case "^(string_of_int n)
  | PAIR -> "_cons"
  | DPAIR -> "_dcons"

let rec string_of_preterm pterm =
  match pterm with
    PTapp(h, pterms) ->
      (string_of_head h)^" "^(string_of_preterms pterms)
and string_of_preterms pterms =
  match pterms with
    [] -> ""
  | pt::pterms' ->
    match pt with
      PTapp(_,[]) -> (string_of_preterm pt)^" "^(string_of_preterms pterms')
    | _ ->
      "("^(string_of_preterm pt)^") "^(string_of_preterms pterms')

let rec string_of_vars vl =
  match vl with
    [] -> ""
  | v::vl' -> v^" "^(string_of_vars vl')

let string_of_prerule (f, vl, pterm) =
  f^" "^(string_of_vars vl)^" -> "^(string_of_preterm pterm)

let rec string_of_prerules_aux prerules =
  match prerules with
    [] -> ""
  | prule::prerules' ->
    (string_of_prerule prule)^".\n"^(string_of_prerules_aux prerules')

let string_of_prerules prerules =
  "%BEGING\n"^(string_of_prerules_aux prerules)^"%ENDG\n"


let rec string_of_states qs =
  match qs with
    [] -> ""
  | q::qs' -> q^" "^(string_of_states qs')

let string_of_transition ((q,a), qs) =
  q^" "^a^" -> "^(string_of_states qs)

let rec string_of_transitions_aux trs =
  match trs with
    [] -> ""
  | tr::trs' ->
    (string_of_transition tr)^".\n"^(string_of_transitions_aux trs')

let string_of_transitions trs =
  "%BEGINA\n"^(string_of_transitions_aux trs)^"%ENDA\n"
