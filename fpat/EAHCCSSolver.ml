open Util
open Combinator

(** An exists-forall HCCS solver (see [Unno et al. POPL 2013] for detals) *)

let accumulate_ext_constrs = ref false
let linear_farkas = ref false
let use_nat = ref false

exception NoSolution
exception Unknown

let fold_coeffs =
  List.partition
    (HornClause.fold
       (fun _ _ -> false)
       (fun pv _ _ -> Idnt.is_coeff (PredVar.idnt_of pv)))
  >> Pair.fold HCCS.resolve(*_fixed*)

let is_solution hcs sol =
  hcs
  |> if_ (const true)
    (HCCS.subst_varsB sol >> fold_coeffs >> FwHCCSSolver.formula_of)
    (FwHCCSSolver.formula_of >> Formula.subst sol >> FormulaSimplifier.simplify)
  |> Formula.bnot
  |> SMTProver.is_valid_dyn

let solve_main cand_sol prev_constrs masked_coeffs solver hcs =
  let sub, constr =
    let vc =
      hcs
      |> EncBoolHCCSSolver.encode false
      |> HCCS.map_phi CunFormula.elim_unit
      |> HCCS.subst_varsB(*@todo*) cand_sol
      |> FwHCCSSolver.formula_of_forward
      |> FormulaSimplifier.simplify
      |> Logger.pprintf
        "verification condition (using_cand_sol):@,  %a |= bot@," Formula.pr
    in
    if Formula.coeffs vc = [] &&
       not (SMTProver.is_sat_dyn vc) (*is_solution hcs cand_sol*) then
      cand_sol
      |> (Logger.pprintf
            "the candidate solution is genuine:@,  %a@,"
            PolyConstrSolver.pr)
      |> TermSubst.complement ~real:false (HCCS.coeffs hcs),
      Formula.mk_true(*@todo*)
(*
    else if Formula.coeffs constr = [] && Formula.is_false constr then
      raise NoSolution
*)
    else
      let constr =
        hcs
        |> EncBoolHCCSSolver.encode false
        |> HCCS.map_phi CunFormula.elim_unit
        |> FwHCCSSolver.formula_of
        |> Logger.pprintf "verification condition:@,  %a |= bot@," Formula.pr
        |> (PolyConstrSolver.gen_coeff_constr
              ~pos:!use_nat ~linear:!linear_farkas)
        |> Logger.pprintf
          "constraints on the conefficients:@,  %a@," Formula.pr
      in
      try
        (if !accumulate_ext_constrs
         then Formula.band (constr :: prev_constrs)
         else constr)
        |> (PolyConstrSolver.solve_dyn
            |> (fun s -> PolyConstrSolver.solve_coeffs_opt s true true)
            |> PolyConstrSolver.solve_with_zcs masked_coeffs
            |> PolyConstrSolver.solve_with_cand_sol cand_sol)
        |> TermSubst.complement ~real:false (HCCS.coeffs hcs),
        constr
      with
      | PolyConstrSolver.NoSolution ->
        Logger.printf0 "no solution@,"; raise Unknown (*NoSolution*)
      | PolyConstrSolver.Unknown ->
        Logger.printf0 "failed to find a solution@,"; raise Unknown
  in
  let psub =
    hcs
    |> HCCS.subst_varsB sub
    |> fold_coeffs
    |> HCCS.simplify_full [] (* this may remove predicate variables *)
    |> solver
  in
  (psub, sub), constr
let solve_main =
  Logger.log_block5 "EAHCCSSolver.solve_main"
    solve_main
    ~before:(fun _ _ _ _ -> Logger.printf "hccs:@,  %a@," HCCS.pr)
    ~after:(fun ((psub, sub), _) ->
        Logger.printf2 "solution:@,  @[<v>psub: %a@,sub: %a@]"
          PredSubst.pr psub
          PolyConstrSolver.pr sub)

let solve_check solver hcs =
  let (psub, sub), constr = solver hcs in
  Logger.debug_assert
    (fun () ->
       HCCS.is_solution
         (hcs
          |> HCCS.subst_varsB sub
          |> fold_coeffs)
         psub);
  (psub, sub), constr
let solve_check = Logger.log_block2 "EAHCCSSolver.solve_check" solve_check

let elapsed_time = ref 0.0
let solve_timer cand_sol prev_constrs masked_coeffs solver hcs =
  let timer = ref (Timer.make ()) in
  let solve_hccs hcs =
    elapsed_time := !timer ();
    let ret = solver hcs in
    timer := Timer.make ();
    ret
  in
  let ret =
    (solve_hccs
     |> solve_main cand_sol prev_constrs masked_coeffs
     |> solve_check)
      hcs
  in
  SMTProver.finalize (); SMTProver.initialize ();
  elapsed_time := !elapsed_time +. !timer ();
  ret

let solve cand_sol prev_constrs masked_coeffs solver hcs =
  if HCCS.coeffs hcs = [] then (solver hcs, []), Formula.mk_true
  else solve_timer cand_sol prev_constrs masked_coeffs solver hcs
let solve =
  Logger.log_block5 "EAHCCSSolver.solve"
    ~before:(fun _ _ _ _ -> Logger.printf "input:@,  %a@," HCCS.pr)
    solve
