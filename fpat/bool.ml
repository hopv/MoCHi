open Util
open Combinator

(** Booleans *)

let string_of b = if b then "true" else "false"
let pr ppf b = Format.fprintf ppf "%s" (string_of b)
let pr_yn ppf b = Format.fprintf ppf "%s" (if b then "yes" else "no")

let imply b1 b2 = not b1 || b2
