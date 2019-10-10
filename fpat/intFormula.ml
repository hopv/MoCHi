open Util
open Combinator

(** Formulas on integers *)

let eq = Formula.eq Type.mk_int
let neq = Formula.neq Type.mk_int
let eq_tt = Formula.eq_tt

let gt = NumFormula.gt Type.mk_int
let lt = NumFormula.lt Type.mk_int
let geq = NumFormula.geq Type.mk_int
let leq = NumFormula.leq Type.mk_int
let within = NumFormula.within Type.mk_int

let divides n t = IntAtom.divides n t |> Formula.of_atom
