open Util
open Combinator

(** Linear expressions with real coefficients *)

include LinExp.Make(Coeff.CoeffReal)
