open Util
open Combinator

(** Linear expressions with integer coefficients *)

include LinExp.Make(Coeff.CoeffInt)
