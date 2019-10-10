open Util

(** Type binders *)

type t =
  | Forall
  | Exists

let string_of = function
  | Forall -> "forall"
  | Exists -> "exists"

let string_of' = function
  | Forall -> "$\\forall$"
  | Exists -> "$\\exists$"

let pr p upr ppf b =
  Format.fprintf
    ppf
    "@[<hov2>%s %a.@ %a@]"
    (string_of b)
    Pattern.pr p
    upr ()

let pr_tex p upr ppf b =
  Format.fprintf
    ppf
    "@[<hov2>%s %a.@ %a@]"
    (string_of' b)
    Pattern.pr_tex p
    upr ()
