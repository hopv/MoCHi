open Util
open Combinator

(** Literals on numbers *)

let eq = Literal.eq
let neq = Literal.neq
let eq_tt = Literal.eq_tt

let gt ty t1 t2 = NumAtom.gt ty t1 t2 |> Literal.of_atom
let lt ty t1 t2 = NumAtom.lt ty t1 t2 |> Literal.of_atom
let geq ty t1 t2 = NumAtom.geq ty t1 t2 |> Literal.of_atom
let leq ty t1 t2 = NumAtom.leq ty t1 t2 |> Literal.of_atom
