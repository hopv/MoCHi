open Util
open Combinator

let complement hcs sol =
  HCCS.tenv hcs
  |> List.filter (fst >> flip List.mem_assoc sol >> not)
  |> PredSubst.top_of_tenv
  |> (@) sol

let solve solver hcs = solver hcs |> complement hcs
