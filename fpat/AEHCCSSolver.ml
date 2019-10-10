open Util
open Combinator

(** A forall-exists dag HCCS solver *)

let skolemize template_gen hc =
  HornClause.ae_fold
    (fun htenv hpv hphi bpvas bphi ->
       match hpv with
       | None -> [HornClause.mk_goal bpvas bphi]
       | Some(pv) ->
         let bphis, hphis =
           let tenv =
             PredVar.args_of pv @
             List.map (flip Pair.make Type.mk_int) (Formula.fvs_int hphi)
             |> List.unique
             |> List.filter (snd >> (=) Type.mk_int)
             (*@todo bool maybe encoded as int*)
             |> List.filter (fst >> flip List.mem_assoc htenv >> not)
           in
           htenv
           |> List.map
             (fun (x, ty) ->
                assert (ty = Type.mk_int || ty = Type.mk_real);
                List.gen
                  1(*unsound: !TemplateBasedHCCSSolver.num_conj*)
                  (fun _ -> template_gen ty x tenv)
                |> List.split
                |> Pair.lift Formula.band)
           |> List.split
         in
         HornClause.mk_def pv bpvas (Formula.band (bphi :: bphis))
         :: (if Formula.is_true hphi then []
             else
               [HornClause.mk_goal
                  bpvas
                  (Formula.band (Formula.bnot hphi :: [bphi](* why not bphi :: bphis?*)))])
         @ (if Formula.is_true (Formula.band hphis) then []
            else [HornClause.mk_goal bpvas
                    (Formula.band [Formula.bnot (Formula.band hphis); bphi])]))
    hc
let skolemize = Logger.log_block2 "AEHCCSSolver.skolemize" skolemize

let template_leq ty x tenv =
  NumFormula.leq ty (Term.mk_var x) (Template.mk_linexp tenv),
  Formula.mk_true

let template_geq ty x tenv =
  NumFormula.geq ty (Term.mk_var x) (Template.mk_linexp tenv),
  Formula.mk_true

let template_eq ty x tenv =
  Formula.eq ty (Term.mk_var x) (Template.mk_linexp tenv),
  Formula.mk_true

let template_bound ty x tenv =
  let elb = Template.mk_linexp tenv in
  let eub = Template.mk_linexp tenv in
  Formula.mk_and
    (NumFormula.leq ty elb (Term.mk_var x))
    (NumFormula.leq ty (Term.mk_var x) eub),
  NumFormula.leq ty elb eub (*@todo there must exist an integer point within the interval*)

let template_general ty x tenv =
  let c1 = Term.new_coeff () in
  let c2 = Term.new_coeff () in
  let e = Template.mk_linexp tenv in
  Formula.mk_and
    (NumFormula.leq ty
       (NumTerm.mul ty c1 e)
       (NumTerm.mul ty c1 (Term.mk_var x)))
    (NumFormula.leq ty
       (NumTerm.mul ty c2 (Term.mk_var x))
       (NumTerm.mul ty c2 e)),
  Formula.mk_true

let bor ty gen1 gen2 x tenv =
  let c = Term.new_coeff () in
  let bphi1, hphi1 = gen1 ty x tenv in
  let bphi2, hphi2 = gen2 ty x tenv in
  Formula.bor
    [Formula.band [NumFormula.geq ty c IntTerm.zero; bphi1];
     Formula.band [NumFormula.lt ty c IntTerm.zero; bphi2]],
  Formula.bor
    [Formula.band [NumFormula.geq ty c IntTerm.zero; hphi1];
     Formula.band [NumFormula.lt ty c IntTerm.zero; hphi2]]

let solve eahccs_solver hcs =
  try
    hcs
    |> List.concat_map (skolemize template_leq)
    |> eahccs_solver
  with
  | EAHCCSSolver.NoSolution
  | EAHCCSSolver.Unknown ->
    (*need this?*)try
      hcs
      |> List.concat_map (skolemize template_geq)
      |> eahccs_solver
    with
    | EAHCCSSolver.NoSolution
    | EAHCCSSolver.Unknown ->(**)
      try
        hcs
        |> List.concat_map (skolemize template_eq)
        |> eahccs_solver
      with
      | EAHCCSSolver.NoSolution
      | EAHCCSSolver.Unknown ->
        hcs
        |> List.concat_map (skolemize template_bound)
        |> eahccs_solver
let solve eahccs_solver hcs =
  Logger.log_block2 "AEHCCSSolver.solve" solve eahccs_solver hcs
