open Util
open Combinator

let solve solver hcs =
  let reachable  = hcs |> HCCS.reachable |> List.assoc_fail None in
  Logger.printf
    "reachable pred. vars.: %a@,"
    (List.pr (Option.pr Idnt.pr "root") ",")
    reachable;
  let sol_unreach =
    hcs
    |> HCCS.tenv
    |> List.filter
      (fst >> Option.return >> flip List.mem reachable >> not)
    |> PredSubst.top_of_tenv
  in
  hcs
  |> List.filter (HornClause.nodeH >> flip List.mem reachable)
  |> solver
  |> (@) sol_unreach
let solve =
  Logger.log_block2 "UnusedHCCSSolver.solve"
    ~before:(fun _ -> Logger.printf "input: %a@," HCCS.pr)
    solve

let solve_rec find_sol_unreach solver hcs =
  let reachable = hcs |> HCCS.reachable |> List.assoc_fail None in
  Logger.printf
    "reachable pred. vars.: %a@,"
    (List.pr (Option.pr Idnt.pr "root") ",")
    reachable;
  let sol_unreach =
    if find_sol_unreach then
      hcs
      |> HCCS.tenv
      |> List.filter
        (fst >> Option.return >> flip List.mem reachable >> not)
      |> PredSubst.top_of_tenv
    else []
  in
  hcs
  |> List.filter (HornClause.nodeH >> flip List.mem reachable)
  |> solver
  |> Pair.map_fst ((@) sol_unreach)
let solve_rec find_sol_unreach solver hcs =
  Logger.log_block3 "UnusedHCCSSolver.solve_rec"
    ~before:(fun _ _ -> Logger.printf "input: %a@," HCCS.pr)
    solve_rec find_sol_unreach solver hcs
