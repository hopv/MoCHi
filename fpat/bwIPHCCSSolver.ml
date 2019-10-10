open Util
open Combinator

let solve_body_left_to_right = ref false

let rec solve_pv lbs pv pvas phi =
  let xs = List.map fst (PredVar.args_of pv) in
  let simplify =
    if !InterpProver.interp_simplify
    then QelimBody.elim_int_vars_full xs
    else id
  in
  let phi1 =
    try
      PredSubst.lookup_fresh lbs (Pva.of_pvar pv) |> simplify
    with Not_found -> assert false
  in
  let phi2 =
    try
      pvas
      |> List.map (PredSubst.lookup_fresh lbs)
      |> List.cons phi
      |> Formula.band
      |> simplify
    with Not_found -> assert false
  in
  try
    GeneralizingInterpProver.gen_pivot := PredVar.idnt_of pv;
    InterpProver.interpolate_dyn
      (fun x -> List.mem x xs || Idnt.is_coeff x)
      phi1
      phi2
    |> Pair.unfold id (fun interp -> Formula.band [interp; phi])
  with
  | InterpProver.NoInterpolant -> raise HCCSSolver.Unknown (* HCCSSolver.NoSolution *)
  (* "raise HCCSSolver.NoSolution" is not correct?
     InterpProver.NoInterpolant may be raised due to an incorrect
     interpolant previously inferred? *)
  | InterpProver.Fail -> raise HCCSSolver.Unknown (* @todo *)
  | InterpProver.Unknown -> raise HCCSSolver.Unknown

(* val solve_pvas : PredSubst.t -> Pva.t list -> Formula.t -> PredSubst.t *)
let rec solve_pvas lbs pvas phi =
  match pvas with
  | [] -> []
  (*| [pva] -> @todo optimization *)
  | pva :: pvas' ->
    let pv, phi_eq = Pva.pvar_of pva in
    Logger.printf "finding a solution to %a@," PredVar.pr pv;
    let interp, rest = solve_pv lbs pv pvas' (Formula.band [phi; phi_eq]) in
    interp
    |> PredSubst.elem_of_pvar pv
    |> Logger.pprintf "solution:@,  %a@," PredSubst.pr_elem
    |> flip List.cons (solve_pvas lbs pvas' rest)
let solve_pvas lbs pvas =
  solve_pvas lbs (if !solve_body_left_to_right then pvas else List.rev pvas)
let solve_pvas =
  Logger.log_block3
    "BwIPHCCSSolver.solve_pvas"
    ~before:(fun lbs pvas phi ->
        let pvs = List.map Pva.idnt_of pvas in
        Logger.printf2
          "input:@,  @[<v>%a@,%a@]@,"
          PredSubst.pr (List.filter (fun (p, _) -> List.mem p pvs) lbs)
          HornClause.pr (HornClause.mk_goal pvas phi))
    solve_pvas

(* val solve_hc : PredSubst.t -> PredSubst.t -> HornClause.t -> PredSubst.t *)
let solve_hc lbs part_sol hc =
  let phi' =
    HornClause.hpv_of hc
    |> PredSubst.lookup_node part_sol
    |> Formula.bnot
    |> Formula.mk_and (HornClause.bphi_of hc)
    |> (if !InterpProver.interp_simplify then FormulaSimplifier.simplify else id)
  in
  (* begin optimization *)
  if not (SMTProver.is_sat_dyn phi') then
    HornClause.bpvas_of hc
    |> List.map (fun pva -> Pva.idnt_of pva, Pred.mk_top (Pva.type_of pva))
  else if HornClause.bpvas_of hc = [] then
    raise HCCSSolver.NoSolution
  else
    (* end optimization *)
    solve_pvas lbs (HornClause.bpvas_of hc) phi'
let solve_hc =
  Logger.log_block3
    "BwIPHCCSSolver.solve_hc"
    ~before:(fun _ _ -> Logger.printf "input: %a@," HornClause.pr)
    solve_hc

let rec solve lbs sol hcs =
  let not_used = HCCS.not_used hcs in
  let hcs1, hcs2 =
    List.partition
      ((* ready to solve? *)
        HornClause.fold
          (fun _ _ -> true)
          (fun pv _ _ -> PredVar.idnt_of pv |> not_used))
      hcs
  in
  if hcs1 = [] then
    begin
      Logger.debug_assert
        ~on_failure:(fun () ->
            Logger.printf0 "error: recursive HCCS not supported@,")
        (fun () -> hcs2 = []);
      sol
    end
  else
    let sol' =
      sol @ List.concat_map (solve_hc lbs sol) hcs1
      |> PredSubst.merge_and
    in
    solve lbs sol' hcs2
let solve hcs =
  let lbs =
    (if !InterpProver.interp_simplify then FwHCCSSolver.solve hcs
     else FwHCCSSolver.solve ~simplify_hc:id hcs)
    |> Logger.pprintf "lower bounds:@,  %a@," PredSubst.pr
  in
  solve lbs [] hcs
let solve =
  Logger.log_block1
    "BwIPHCCSSolver.solve"
    ~before:(Logger.printf "input: %a@," HCCS.pr)
    solve
