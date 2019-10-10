open Util
open Combinator

(** A boolean HCCS solver *)

(** @todo use SAT solver to compute minimal unsat core *)
let solve hcs =
  let lbs = FwHCCSSolver.solve hcs in
  hcs
  |> FwHCCSSolver.formula_of_forward_with_lbs lbs
  |> FormulaSimplifier.simplify
  |> SMTProver.is_sat_dyn
  |> not
  |> if_ id
    (fun true -> Logger.debug_assert (fun () -> PredSubst.wo_fvs lbs); lbs)
    (fun false -> raise HCCSSolver.NoSolution)

