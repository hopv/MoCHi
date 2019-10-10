open Util
open Combinator

let solve solver hcs : PredSubst.t =
  let tenv = HCCS.tenv hcs in
  hcs
  |> HCCS.undefined_pvs
  |> List.unique
  |> List.map (fun p -> p, List.assoc_fail p tenv)
  |> PredSubst.bot_of_tenv
  |> HCCS.of_psub
  |> (@) hcs
  |> solver
let solve = Logger.log_block2 "UndefHCCSSolver.solve" solve
