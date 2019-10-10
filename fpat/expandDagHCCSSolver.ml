open Util
open Combinator
open HCCSSolver

(** A dag HCCS solver based on dag expansion *)

let solve tree_solver hcs =
  let hcs, inv_map = HCCS.expand_dag hcs in
  hcs
  |> tree_solver
  |> List.map (Pair.map_fst (fun p -> List.assocD p p inv_map))
  |> PredSubst.merge
