open Util
open Combinator

(** Literals on integers *)

let eq = Literal.eq Type.mk_int
let neq = Literal.neq Type.mk_int
let eq_tt = Literal.eq_tt

let gt = NumLiteral.gt Type.mk_int
let lt = NumLiteral.lt Type.mk_int
let geq = NumLiteral.geq Type.mk_int
let leq = NumLiteral.leq Type.mk_int

let divides n t = IntAtom.divides n t |> Literal.of_atom
