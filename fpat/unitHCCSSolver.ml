open Util
open Combinator
open HCCSSolver

(** A unit HCCS solver *)

let solve (solver : HCCSSolver.t) = HCCS.map_phi CunFormula.elim_unit >> solver
let solve = Logger.log_block2 "UnitHCCSSolver.solve" solve
