open Combinator
open Util

(** A dag HCCS solver based on bottom-up iterative propagation *)

(* val fol_backward : bool ref *)
let fol_backward = ref false

(*
(** @return the least lower bound *)
val solve_hc :
  ?simplify:(HornClause.t -> HornClause.t) ->
  PredSubst.t -> HornClause.t -> PredSubst.elem
*)
let solve_hc simplify lbs hc =
  match
    hc
    |> HornClause.substB (*~simplify:simplify*) lbs
    |> List.return
    |> HCCS.elim_disj
    |> HCCS.simplify_full []
    |> HCCS.merge
  with
  | [] ->
    PredSubst.elem_of_pvar
      (HornClause.hpv_of hc |> Option.elem_of)
      Formula.mk_false
  | [hc'] ->
    assert (HornClause.bpvas_of hc'= []);
    PredSubst.elem_of_pvar
      (HornClause.hpv_of hc' |> Option.elem_of)
      (HornClause.bphi_of hc')
  | _ -> assert false
let solve_hc ?(simplify = HornClause.simplify_full []) =
  Logger.log_block2
    "FwHCCSSolver.solve_hc"
    ~after:(Logger.printf "output:@,  %a" PredSubst.pr_elem)
    (solve_hc simplify)


let rec solve simplify_hc lbs hcs =
  let not_defined = HCCS.not_defined hcs in
  let hcs1, hcs2 =
    let ready_to_compute_lb =
      HornClause.fold
        (fun _ _ -> assert false)
        (fun _ pvas _ ->
           List.for_all
             (Pva.idnt_of >> fun p -> List.mem_assoc p lbs && not_defined p)
             pvas)
    in
    List.partition ready_to_compute_lb hcs
  in
  if hcs1 = [] then
    begin
      (** @todo need to relax the assumption [is_well_defined hcs]? *)
      assert (hcs2 = []);
      lbs
    end
  else
    hcs1
    |> List.map (solve_hc ~simplify:simplify_hc lbs)
    |> (@) lbs
    (*|> Logger.pprintf "before merge: %a@," PredSubst.pr*)
    |> PredSubst.merge
    (*|> Logger.pprintf "after merge: %a@," PredSubst.pr*)
    |> flip (solve simplify_hc) hcs2
let solve simplify_hc =
  HCCS.complement
  >> List.filter (HornClause.is_root >> not)
  >> solve simplify_hc []
(** @return the least lower bounds
    @require is_non_recursive hcs
    @require is_well_defined hcs
    @ensure Map_.is_map ret
    @ensure Set_.equiv (Map_.dom ret) (HornClause.pvs hcs) *)
(* val solve :
   ?simplify_hc:(HornClause.t -> HornClause.t) ->
   t -> PredSubst.t*)
let solve ?(simplify_hc = HornClause.simplify_full []) =
  Logger.log_block1
    "FwHCCSSolver.solve"
    ~after:(Logger.printf "output:@,  %a" PredSubst.pr)
    (solve simplify_hc)

let solve_simp = solve ~simplify_hc:(HornClause.simplify_full [])

let rec extlbs_of extlbs hcs =
  let not_defined = HCCS.not_defined hcs in
  let hcs1, hcs2 =
    let ready_to_compute_extlb =
      HornClause.fold
        (fun _ _ -> assert false)
        (fun _ pvas _ -> List.for_all (Pva.idnt_of >> not_defined) pvas)
    in
    List.partition ready_to_compute_extlb hcs
  in
  if hcs1 = [] then
    begin
      Logger.debug_assert
        (fun () -> hcs2 = [])
        ~on_failure:(fun () -> Format.printf "hcs2: %a@," HCCS.pr hcs2);
      extlbs
    end
  else
    hcs1
    |> List.concat_map (HCCS.resolve_hc extlbs)
    |> HCCS.simplify_full []
    (* cannot replace the above code with: resolve extlbs *)
    |> Logger.pprintf "inlined horn clauses:@,  %a@," HCCS.pr
    |> (@) extlbs
    (*|> merge @todo this may cause error *)
    |> flip extlbs_of hcs2

let extlbs_of = List.filter (HornClause.is_root >> not) >> extlbs_of []
(** @return the least lower bounds
    @require is_non_recursive hcs
    @ensure Map_.is_map ret
    @ensure is_well_defined hcs =>
              Set_.equiv (Map_.dom ret)
                         (HornClause.pvs hcs)
    a predicate not in the domain of [ret]
    should have the solution [false] *)
(*val extlbs_of : t -> t*)
let extlbs_of =
  Logger.log_block1
    "FwHCCSSolver.extlbs_of"
    ~before:(Logger.printf "input:@,  %a@," HCCS.pr)
    ~after:(Logger.printf "output:@,  %a" HCCS.pr)
    extlbs_of

let formula_of_forward_with_lbs lbs =
  List.filter HornClause.is_root
  >> List.map (HornClause.formula_of_forward lbs)
  >> Formula.bor
  >> FormulaSimplifier.simplify
(** @require [is_non_recursive hcs]
    @ensure [lbs] is a solution for [hcs]
      iff [formula_of_forward hcs] => bot *)
(*val formula_of_forward_with_lbs :
  PredSubst.t -> t -> Formula.t*)
let formula_of_forward_with_lbs =
  Logger.log_block2
    "FwHCCSSolver.formula_of_forward_with_lbs"
    ~before:(fun _ -> Logger.printf "input:@,  %a@," HCCS.pr)
    ~after:(Logger.printf "output:@,  %a" Formula.pr)
    formula_of_forward_with_lbs

(* val formula_of_forward : t -> Formula.t*)
let formula_of_forward hcs = formula_of_forward_with_lbs (solve hcs) hcs

(** @return a FOL formula equivalent to [hcs]
    @require [is_non_recursive hcs]
    @ensure [hcs] is solvable
      iff [formula_of_forward_ext hcs => bot] *)
(* val formula_of_forward_ext : t -> Formula.t *)
let formula_of_forward_ext hcs =
  let hcs1, (hcs2, hcs3) =
    hcs
    |> HCCS.elim_disj
    |> HCCS.simplify_full []
    |> HCCS.complement
    |> List.partition HornClause.is_root
    |> Pair.map_snd (List.partition HornClause.is_coeff)
  in
  Logger.printf "def. clauses:@,  %a@," HCCS.pr hcs3;
  let extlbs = extlbs_of hcs3 in
  Logger.printf
    "extended least lower bounds:@,  %a@,"
    (List.pr HornClause.pr "@,") extlbs;
  hcs1
  |> Logger.pprintf "goal clauses:@,  %a@," HCCS.pr
  |> HCCS.resolve extlbs
  |> Logger.pprintf "resolved goal clauses:@,  %a@," HCCS.pr
  |> HCCS.resolve hcs2
  |> Logger.pprintf "further resolved goal clauses:@,  %a@," HCCS.pr
  |> List.map
    (fun hc ->
       HornClause.fold
         (fun pvas phi ->
            Logger.debug_assert (fun () -> pvas = [])
              ~on_failure:(fun () ->
                  Format.printf "error: %a@," HornClause.pr hc);
            phi)
         (fun _ _ _ ->
            Logger.debug_assert_false
              ~on_failure:(fun () ->
                  Format.printf "error: %a@," HornClause.pr hc)
              ())
         hc)
  |> Formula.bor
  |> FormulaSimplifier.simplify
let formula_of_forward_ext =
  Logger.log_block1
    "FwHCCSSolver.formula_of_forward_ext"
    ~after:(Logger.printf "output: %a" Formula.pr)
    formula_of_forward_ext

let formula_of_backward hcs =
  hcs
  |> List.partition
    (fun hc -> not (HornClause.is_root hc || HornClause.is_coeff hc))
  |> uncurry2 HCCS.resolve_fixed
  |> List.partition (HornClause.is_root >> not)
  |> uncurry2 HCCS.resolve
  |> List.map
    (HornClause.fold
       (fun pvas phi -> assert (pvas = []); phi)
       (fun _ _ _ -> assert false))
  |> Formula.bor
  |> FormulaSimplifier.simplify
(** @require [is_non_recursive hcs]
    @ensure [hcs] is solvable
      iff [formula_of_backward hcs => bot] *)
(* val formula_of_backward : t -> Formula.t *)
let formula_of_backward =
  Logger.log_block1  "FwHCCSSolver.formula_of_backward" formula_of_backward

(* val formula_of : t -> Formula.t *)
let formula_of hcs =
  let hcs = HCCS.complement hcs in
  if !fol_backward then formula_of_backward hcs
  else formula_of_forward_ext hcs
let formula_of = Logger.log_block1  "FwHCCSSolver.formula_of" formula_of

(* val complement_sol : t -> PredSubst.t -> PredSubst.t *)
let complement_sol hcs sol =
  hcs
  |> HCCS.subst ~simplify_hc:(HornClause.simplify_full []) sol
  |> List.map (HornClause.simplify_full [])
  |> solve
  |> (@) sol

let inline_other_than p hcs =
  hcs
  |> List.partition
    (fun hc -> not (HornClause.is_root hc || HornClause.pvsH hc = [p]))
  |> Pair.map_fst
    (Set_.inter (HCCS.backward_depend [None; Some(p)] hcs) >> extlbs_of)
  |> uncurry2 HCCS.resolve
  |> HCCS.simplify_lv1
(** inline other than [Some(p)] and [None] *)
(* val inline_other_than : Idnt.t -> t -> t *)
let inline_other_than =
  Logger.log_block2
    "FwHCCSSolver.inline_other_than"
    ~after:(Logger.printf "output:@,  %a" HCCS.pr)
    inline_other_than

(** inline predicates that satisfy [p]
    @require [is_non_recursive hcs]
    @ensure the result does not contain
            a predicate variable that satisfies [p] *)
(* val inline_forward : (Idnt.t -> bool) -> t -> t *)
let inline_forward p hcs =
  hcs
  |> HCCS.elim_non_defined
  |> Logger.pprintf "non defined vars eliminated:@,  %a@," HCCS.pr
  |> List.partition
    (HornClause.fold
       (fun _ _ -> false)
       (fun pv _ _ -> pv |> PredVar.idnt_of |> p))
  |> Pair.map extlbs_of id
  |> Pair.fold HCCS.resolve
  |> HCCS.elim_non_defined
  |> List.filter
    (HornClause.fold
       (fun pvas phi ->
          if pvas = [] then
            if SMTProver.is_sat_dyn phi then
              (* assert false
                 if hcs is assumed to be satisfiable *)
              true
            else false
          else true)
       (fun _ _ _ -> true))
let inline_forward =
  Logger.log_block2
    "FwHCCSSolver.inline_forward"
    ~before:(fun _ -> Logger.printf "input:@,  %a@," HCCS.pr)
    ~after:(Logger.printf "output:@,  %a" HCCS.pr(*_verbose*))
    inline_forward

let inline_backward p hcs =
  hcs
  |> List.partition
    (HornClause.fold
       (fun _ _ -> false)
       (fun pv _ _ -> p (PredVar.idnt_of pv)))
  |> Pair.fold HCCS.resolve_fixed
(** inline predicates that satisfy [p]
    @require [is_non_recursive hcs] *)
(* val inline_backward : (Idnt.t -> bool) -> t -> t *)
let inline_backward =
  Logger.log_block2 "FwHCCSSolver.inline_backward" inline_backward

(* val is_partial_solution : t -> PredSubst.t -> bool *)
let is_partial_solution hcs sol =
  sol
  |> complement_sol hcs
  |> HCCS.is_solution hcs(* @todo check whether sol is a map *)
let is_partial_solution =
  Logger.log_block2 "FwHCCSSolver.is_partial_solution" is_partial_solution

let is_solvable hcs =
  hcs
  |> formula_of_forward
  |> Formula.bnot
  |> SMTProver.is_valid_dyn
(* val is_solvable : t -> bool *)
let is_solvable = Logger.log_block1 "FwHCCSSolver.is_solvable" is_solvable

let find_valid_sol_inc sol hcs =
  sol
  |> List.fold_left
    (fun (sol, hcs) s ->
       Logger.printf "checking:@,  %a@," PredSubst.pr_elem s;
       hcs
       |> HCCS.subst ~simplify_hc:(HornClause.simplify_full []) [s]
       |> if_ is_solvable
         (Pair.make (s :: sol))
         (fun hcs' ->
            Logger.printf "not solvable:@,  %a@," HCCS.pr hcs';
            (sol, hcs)))
    ([], hcs)
  |> if_ (fst >> (=) []) (fun _ -> raise Not_found) id

(** the following code is faster but incorrect? *)
let find_valid_sol_sim sol hcs =
  let rec aux sol =
    match sol with
    | [] -> raise Not_found
    | _ ->
      hcs
      |> HCCS.subst ~simplify_hc:(HornClause.simplify_full []) sol
      |> if_ is_solvable (fun hcs' -> sol, hcs') (fun _ -> aux (List.tl sol))
  in
  aux sol

let find_inc = ref true
let find_valid_sol sol hcs =
  let sorted_sol =
    (** decreasing order seems better (e.g. copy-intro)
        @todo implement topological sort of [sol]
              w.r.t. the parent-child relation of
              the tree structure of HCCS *)
    List.sort (fun (p1, _) (p2,_) ->
        if p1 = p2 then 0  else if Idnt.lt p2 p1 then -1 else 1)
      sol
  in
  if !find_inc then find_valid_sol_inc sorted_sol hcs
  else find_valid_sol_sim sorted_sol hcs
(* val find_valid_sol : PredSubst.t -> t -> PredSubst.t * t *)
let find_valid_sol =
  Logger.log_block2 "FwHCCSSolver.find_valid_sol" find_valid_sol

let simplify_formula xs =
  HornClause.mk_goal [] >> HornClause.simplify_full xs >> HornClause.bphi_of

(** @raise Not_found if ub is not computable
    filter horn clauses that use (but do not define) [p] *)
let psub_of_use p =
  List.filter_map
    (HornClause.fold
       (fun pvas phi ->
          match pvas with
          | [] ->
            (*Logger.debug_assert
               (fun () ->
                phi |>
                  Formula.bnot |>
                  SMTProver.is_valid_dyn)
               ~on_failure:
               (fun () ->
                Format.printf
                  "not valid: %a => bot@,"
                  Formula.pr phi);*)
            None
          | [pva] ->
            Logger.debug_assert (fun () -> Pva.idnt_of pva = p);
            let p' = Pva.idnt_of pva in
            let ttsub =
              pva
              |> Pva.args_of
              |> TypTermSubst.of_tts
            in
            Logger.debug_assert
              (fun () -> p' = p)
              ~on_failure:(fun () ->
                  Format.printf "p': %a@,p: %a@," Idnt.pr p' Idnt.pr p);
            [phi; Formula.of_ttsub ttsub]
            |> Formula.band
            |> simplify_formula (TypTermSubst.dom ttsub)
            |> Formula.bnot
            |> Pair.make (TypTermSubst.tenv_of ttsub)
            |> Pair.make p
            |> Option.return
          | _ -> raise Not_found(* does not support dag *))
       (fun pv pvas phi ->
          if pvas = [] then
            begin
              Logger.debug_assert (fun () -> PredVar.idnt_of pv = p);
              None
            end
          else raise Not_found(* does not support recursion *)))

let ub_of_pvar hcs (p, ty) =
  hcs
  |> (if false then inline_other_than p else inline_forward ((<>) p))
  |> Logger.pprintf "inlined hcs: %a@," HCCS.pr
  |> psub_of_use p
  |> if_ ((=) [])
    (fun _ -> Pair.make p (Pred.mk_top ty))
    (PredSubst.merge_and(*this should not be merge*) >> List.elem_of_singleton)
(** compute the greatest upper bound for [p]
    @require rhs never contains [false]?
    @raise Not_found if the function fail to
           compute the greatest upper bound *)
(* val ub_of_pvar : t -> (Idnt.t * Type.t) -> PredSubst.elem *)
let ub_of_pvar =
  Logger.log_block2
    "FwHCCSSolver.ub_of_pvar"
    ~before:(fun hcs _ -> Logger.printf "original hcs: %a@," HCCS.pr hcs)
    ub_of_pvar

(** @require [is_non_recursive hcs]
    @require rhs never contains [false]?
    @ensure [Map_.is_map ret]
    @ensure [Set_.equiv (Map_.dom (fst ret) \@ snd ret)
                        (List.map fst tenv)]
    upper bounds for some predicate variables P
    may not be computed if a subset of [hcs] is
    equivalent to a constraint like
    "P(x) and P(y) => phi"

    the predicate variables P are also returned *)
(* val ubs_of :
   ?pvs:(Idnt.t list option) ->
   t ->
   PredSubst.t * Idnt.t list *)
let ubs_of pvs hcs =
  let tenv =
    match pvs with
    | None -> HCCS.tenv hcs
    | Some(pvs) -> hcs |> HCCS.tenv |> List.filter (fst >> flip List.mem pvs)
  in
  tenv
  |> List.partition_map
    (fun (p, ty) -> try `L(ub_of_pvar hcs (p, ty)) with Not_found -> `R(p))
let ubs_of ?(pvs = None) =
  Logger.log_block1
    "FwHCCSSolver.ubs_of"
    ~after:(fst >> Logger.printf "output:@,  %a" PredSubst.pr)
    (ubs_of pvs)
