open Util
open Combinator

let solve is_not_reduced solve_heavy solve_light hcs =
  let sol =
    hcs
    |> HCCS.reduce is_not_reduced
    |> Logger.pprintf "reduced HCCS:@,  %a@," HCCS.pr_verbose
    |> solve_heavy
  in
  hcs
  (*|> HCCS.subst ~simplify_hc:(HornClause.simplify_full []) sol*)
  |> ComplementHCCSSolver.solve solve_light
  |> (@) sol
let solve = Logger.log_block3 "ReduceHCCSSolver.solve" solve

let solve_ehccs is_not_reduced solve_heavy solve_light hcs =
  let sol, sub =
    hcs
    |> HCCS.reduce is_not_reduced
    |> Logger.pprintf "reduced HCCS:@,  %a@," HCCS.pr_verbose
    |> solve_heavy
  in
  let hcs' =
    hcs
    |> HCCS.subst_varsB sub
    |> HCCS.subst ~simplify_hc:(HornClause.simplify_full []) sol
  in
  let sub' = HCCS.coeffs hcs' |> List.map (fun c -> c, IntTerm.zero) in
  hcs'
  |> HCCS.subst_varsB sub'
  |> HCCS.simplify_full []
  |> solve_light
  |> (@) sol, sub @ sub'
