open Util
open Combinator

(** only for recursion-free HCCS *)
let solve is_inlined (solver : HCCSSolver.t) =
  FwHCCSSolver.inline_forward is_inlined >> solver
let solve = Logger.log_block3 "InlineHCCSSolver.solve" solve
