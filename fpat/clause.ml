open Util
open Combinator

type t = Literal.t list

(** {6 Printers} *)

let pr ppf = Format.fprintf ppf "@[<hov>%a@]" (List.pr Literal.pr " \\/@ ")

(** {6 Auxiliary destructors} *)

let disjunction_of = List.map Literal.formula_of
let formula_of = disjunction_of >> Disjunction.formula_of
