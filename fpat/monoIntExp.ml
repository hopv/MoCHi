open Util
open Combinator

(** Monomial expressions with integer coefficients *)

include MonoExp.Make(Coeff.CoeffInt)
