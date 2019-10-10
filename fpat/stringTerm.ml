open Util
open Combinator

include Term

(** String term expressions *)

let make s = mk_const (Const.String(s))
