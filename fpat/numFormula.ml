open Util
open Combinator

(** Formulas on numbers *)

let eq = Formula.eq
let neq = Formula.neq
let eq_tt = Formula.eq_tt

let gt ty t1 t2 = NumAtom.gt ty t1 t2 |> Formula.of_atom
let lt ty t1 t2 = NumAtom.lt ty t1 t2 |> Formula.of_atom
let geq ty t1 t2 = NumAtom.geq ty t1 t2 |> Formula.of_atom
let leq ty t1 t2 = NumAtom.leq ty t1 t2 |> Formula.of_atom
let within = NumAtom.within
