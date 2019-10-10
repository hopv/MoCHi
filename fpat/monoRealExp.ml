open Util
open Combinator

(** Monomial expressions with real coefficients *)

include MonoExp.Make(Coeff.CoeffReal)
