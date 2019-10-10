open Util
open Combinator

(** Trace expressions *)

type t = Elm of Trace.elem | Seq of t list | Br of t * t

let rec pr ppf = function
  | Elm(elm) -> Trace.pr_elem ppf elm
  | Seq(es) -> List.pr pr "" ppf es
  | Br(es1, es2) -> Format.fprintf ppf "(%a | %a)" pr es1 pr es2

let trace_exp_of tr = Seq(List.map (fun elm -> Elm(elm)) tr)
