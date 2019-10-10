open Util
open Combinator

(** S-expressions *)

type t = S of string | L of t list

let rec pr ppf = function
  | S(str) -> Format.fprintf ppf "%a" String.pr str
  | L(es) -> Format.fprintf ppf "(%a)" (List.pr_app pr "@ ") es
