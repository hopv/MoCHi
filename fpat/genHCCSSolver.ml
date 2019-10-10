open Util
open Combinator

(** A dag HCCS solver based on generalizing interpolation
    (see [Sato et al. PEPM 2013] for details) *)
(* generalize constraints from multiple calls of each function *)

let always_use_gen_interp_prover = ref false

exception UseBackward

let lb_ub_of lbs ubs = fun pv ->
  let tenv = PredSubst.args_of pv lbs in
  let pva = Pva.of_pvar (PredVar.make pv tenv) in
  tenv,
  handle
    (fun () -> PredSubst.lookup_fresh lbs pva)
    (fun Not_found ->
       Logger.debug_assert_false
         ~on_failure:(fun () ->
             Format.printf "lower bound of %a is not found@," Idnt.pr pv)
         ()),
  handle
    (fun () -> PredSubst.lookup_fresh ubs pva)
    (fun Not_found ->
       Logger.debug_assert_false
         ~on_failure:(fun () ->
             Format.printf "upper bound of %a is not found@," Idnt.pr pv)
         ())

let lbs_ubs_of lb_ub_of = fun pvs ->
  assert (pvs <> []);
  let (tenv, lb, ub) :: rs = List.map lb_ub_of pvs in
  let lbs, ubs =
    rs
    |> List.map
      (fun (tenv', lb', ub') ->
          let xts =
            List.map2
              (fun (x1, ty1) (x2, ty2) ->
                 Logger.debug_assert (fun () -> ty1 = ty2);
                 x1, Term.mk_var x2)
              tenv' tenv
          in
          Formula.subst xts lb', Formula.subst xts ub')
    |> List.split
  in
  tenv, lb :: lbs, ub :: ubs

(** heuristic for classifying predicate variables to be merged *)
let classify_pvs lbs_ubs_of pvs =
  let check pvs =
    let _, lbs, ubs = lbs_ubs_of pvs in
    SMTProver.implies_dyn [Formula.bor lbs] [Formula.band ubs]
  in
  let rec add p pvss =
    match pvss with
    | [] -> [[p]]
    | pvs :: pvss ->
      if check (p :: pvs) then (p :: pvs) :: pvss else pvs :: (add p pvss)
  in
  let rec classify pvs pvss =
    match pvs with
    | [] -> pvss
    | p :: pvs -> classify pvs (add p pvss)
  in
  List.sort_dec_by List.length (classify pvs [])
let classify_pvs =
  Logger.log_block2
    "GenHCCSSolver.classify_pvs"
    ~after:(fun pvss ->
        Logger.printf0 "output:@,  @[<v>";
        let pr_aux ppf pvs =
          Format.fprintf ppf "[%a]" (List.pr Idnt.pr ";") pvs
        in
        Logger.printf "%a" (List.pr pr_aux ",") pvss;
        Logger.printf0 "@]")
    classify_pvs

(** upper bounds computation is too slow *)
let pvs_ubs_obsolete pvss hcs =
  let ubs, ndpvs = FwHCCSSolver.ubs_of hcs in
  Logger.printf "upper bounds:@,  %a@," PredSubst.pr ubs;
  (* pick one from pvss *)
  handle
    (fun () ->
       List.find_map
         (fun pvs ->
            let pvs = Set_.diff pvs ndpvs in
            if pvs = [] then None else Some(pvs))
         pvss)
    (fun Not_found -> assert false),
  ubs

let pvs_ubs pvss hcs =
  try
    (* pick one from pvss *)
    List.find_map
      (fun pvs ->
         let ubs, ndpvs = FwHCCSSolver.ubs_of ~pvs:(Some(pvs)) hcs in
         let pvs = Set_.diff pvs ndpvs in
         if pvs = [] then None
         else
           begin
             Logger.printf "upper bounds:@,  %a@," PredSubst.pr ubs;
             Some(pvs, ubs)
           end)
      pvss
  with Not_found -> raise UseBackward

let gen_interp gip pvs tenv lbs nubs =
  try gip pvs tenv lbs nubs
  with
  | GenInterpProver.NoInterpolant -> raise HCCSSolver.NoSolution
  | GenInterpProver.Fail -> raise HCCSSolver.Unknown

let ord_interp pv tenv lb nub =
  let interp =
    try
      InterpProver.interpolate_dyn
        (fun x -> List.mem_assoc x tenv || Idnt.is_coeff x)
        lb nub
    with
    | InterpProver.NoInterpolant -> raise HCCSSolver.NoSolution
    | InterpProver.Fail -> raise HCCSSolver.Unknown
    | InterpProver.Unknown -> raise (Global.NotImplemented "integer interpolation?")
  in
  [pv, (tenv, interp)]

let solve_step gip pvss hcs =
  Logger.printf "Horn clauses:@,  %a@," HCCS.pr hcs;
  (*let hcs = inline_forward (fun p -> not (List.mem p pvss)) hcs in*)
  let pvs, lbs_ubs_of =
    let lbs = FwHCCSSolver.solve hcs in
    Logger.printf "lower bounds:@,  %a@," PredSubst.pr lbs;
    let pvs, ubs = pvs_ubs pvss hcs in
    List.iter
      (fun pv ->
         let _, lb, ub = lb_ub_of lbs ubs pv in
         Logger.debug_assert
           (fun () -> not !HCCSSolver.check_solvability_first
                      || SMTProver.implies_dyn [lb] [ub])
           ~on_failure:(fun () ->
               Logger.printf3
                 "pv: %a@,not |= %a => %a@,"
                 Idnt.pr pv
                 Formula.pr lb
                 Formula.pr ub))
      pvs;
    pvs, lbs_ubs_of (lb_ub_of lbs ubs)
  in
  let sol, hcs' =
    let pvs = pvs |> classify_pvs lbs_ubs_of |> List.hd in
    let tenv, lbs, ubs = lbs_ubs_of pvs in
    let nubs = List.map Formula.bnot ubs in
    if List.length pvs = 1 then
      (if !always_use_gen_interp_prover then
         gen_interp gip pvs tenv lbs nubs
       else
         let [lb], [nub] = lbs, nubs in
         ord_interp (List.hd pvs) tenv lb nub)
      |> Pair.unfold
        id
        (flip (HCCS.subst ~simplify_hc:(HornClause.simplify_full [])) hcs)
    else
      let sol = gen_interp gip pvs tenv lbs nubs in
      try
        FwHCCSSolver.find_valid_sol sol hcs
      with Not_found ->
        Logger.debug_assert_false
          ~on_failure:(fun () ->
              Format.printf "Horn clauses:@,  %a@," HCCS.pr hcs;
              Format.printf "solution:@,  %a@," PredSubst.pr sol)
          ()
  in
  hcs
  |> HCCS.tenv
  |> List.filter (fun (p, _) -> not (List.mem_assoc p sol)
                                && not (List.mem p (HCCS.pvs hcs')))
  |> PredSubst.bot_of_tenv
  |> (@) sol
  |> Logger.pprintf "part. solution:@,  %a@," PredSubst.pr
  |> flip Pair.make hcs'

let rec solve gip hcs =
  hcs
  |> HCCS.pvs
  |> List.unique
  |> List.classify Idnt.cong
  |> List.sort_dec_by List.length
  |> (function
      | [] -> []
      | pvss ->
        let sol, hcs' =
          try solve_step gip pvss hcs
          with UseBackward -> BwIPHCCSSolver.solve hcs, []
        in
        sol @ solve gip hcs'
        |> PredSubst.merge_and)
let solve =
  Logger.log_block2
    "GenHCCSSolver.solve"
    ~after:(Logger.printf "solution:@,  %a" PredSubst.pr)
    solve
