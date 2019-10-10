open Util
open Combinator

(** Polynomial expressions with integer coefficients *)

include PolyExp.Make(Coeff.CoeffInt)
