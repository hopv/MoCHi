open Util
open Combinator
open Literal

(** Literals on unit, booleans, integers, and pvas *)

let simplify = fold (CunAtom.simplify >> of_atom) CunAtom.negate
let negate = fold CunAtom.negate (CunAtom.simplify >> of_atom)
