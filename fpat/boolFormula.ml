open Util
open Combinator

(** Formulas on booleans *)

let eq = Formula.eq Type.mk_bool
let neq = Formula.neq Type.mk_bool

let mk_var = Term.mk_var >> Formula.of_term
