open Combinator
open Util

(** Boolean term expressions *)

let mk_true = Term.mk_const Const.True
let mk_false = Term.mk_const Const.False
let make b = if b then mk_true else mk_false
