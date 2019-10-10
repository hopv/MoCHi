open Util

(** Ordinals *)

type t = int

let make n = n

let pr ppf n =
  if n = 11 || n = 12 || n = 13 then
    Format.fprintf ppf "%dth" n
  else
    match n mod 10 with
    | 1 -> Format.fprintf ppf "%dst" n
    | 2 -> Format.fprintf ppf "%dnd" n
    | 3 -> Format.fprintf ppf "%drd" n
    | _ -> Format.fprintf ppf "%dth" n

let string_of = Printer.string_of pr
