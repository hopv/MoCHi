open Combinator
open Util

(** Unit term expressions *)

let make = Term.mk_const Const.Unit

let simplify t = t
