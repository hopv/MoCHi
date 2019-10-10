open Util
open Combinator

(** Formulas on reals *)

let eq = Formula.eq Type.mk_real
let neq = Formula.neq Type.mk_real
let eq_tt = Formula.eq_tt

let gt = NumFormula.gt Type.mk_real
let lt = NumFormula.lt Type.mk_real
let geq = NumFormula.geq Type.mk_real
let leq = NumFormula.leq Type.mk_real
let within = NumFormula.within Type.mk_real
