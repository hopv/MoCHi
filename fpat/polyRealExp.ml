open Util
open Combinator

(** Polynomial expressions with real coefficients *)

include PolyExp.Make(Coeff.CoeffReal)
