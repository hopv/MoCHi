open Util
open Combinator

(** A refinement type inference algorithm based on HCCS solving
    (see [Unno et al. PPDP 2009, PLDI 2011, and POPL 2013] for detals) *)

let exp_mode = ref false

exception FailedToRefineTypes
exception FailedToRefineInputTypes
exception FailedToRefineExtraParameters

(** {6 (Forall-exists) HCCS generation} *)

let flag_coeff = ref false

let root_id_of (x, uid) = CallId.root_id_of (Idnt.T(x, uid, (*dummy*)-1))

let refinable ty =
  Type.is_base ty
  && ty <> Type.mk_unit(*sound @todo*)

let pres env loc x =
  try
    Zipper.root loc
    |> Zipper.find_all
         (fun nd ->
          CallId.is_ancestor_or_eq
            (CallId.root_id_of x)
            nd.CallTree.name
          && RefType.visible
               x
               (RefType.find_last_base env nd.CallTree.name))
    |> List.filter_map
         (fun (Zipper.Loc(tr, _)) ->
          try
            (Zipper.get tr).CallTree.name
            |> RefType.find_last_base_exc env
            |> RefType.pva_of_var env
            |> Option.some
          with Not_found ->
            None)
  with Not_found ->
    Format.printf "RefTypInfer.pres: %a is not found@," Idnt.pr x;
    assert false
let posts env loc x =
  try
    Zipper.root loc
    |> Zipper.find_all
         (fun nd ->
          match nd.CallTree.ret with
          | None -> false
          | Some(xuid) ->
             CallId.is_ancestor_or_eq
               (CallId.root_id_of x)
               xuid
             && RefType.visible
                  x
                  (RefType.find_last_base env xuid))
    |> List.filter_map
         (fun (Zipper.Loc(tr, _)) ->
          let Some(xuid) = (Zipper.get tr).CallTree.ret in
          try
            RefType.find_last_base_exc env xuid
            |> RefType.pva_of_var env
            |> Option.some
          with Not_found ->
            None)
  with Not_found ->
    Format.printf "RefTypInfer.posts: %a is not found@," Idnt.pr x;
    assert false

let rec cgen_etr env (Zipper.Loc(tr, p) as loc) etr0 hcs0 =
  match etr0 with
  | Trace.Call(y, guard) :: etr when Idnt.is_top (fst y) ->
     let loc' = Zipper.insert_down loc (CallTree.make y true (guard, [])) in
     cgen_etr env loc' etr hcs0
  | Trace.Call(y, guard) :: etr when Idnt.is_pos (fst y) ->
     assert (Formula.is_true guard);
     let loc' = Zipper.insert_down loc (CallTree.make y true (guard, [])) in
     cgen_etr env loc' etr hcs0
  | Trace.Call(y, guard) :: etr when Idnt.is_neg (fst y) ->
     assert (Formula.is_true guard);
     let nd = Zipper.get tr in
     let loc' =
       let nd' = { nd with ret = Some(y) } in
       Zipper.up (Zipper.Loc(Zipper.set tr nd', p))
     in
     cgen_etr env loc' etr hcs0
  | Trace.Arg(ttsub) :: etr ->
     begin
       match ttsub |> List.filter (snd >> snd >> RefType.refinable) with
       | [] ->
         if !RefType.refine_function then
           (* @todo need function type refinement *)
           raise (Global.NotImplemented "RefTypInfer.cgen_etr")
         else cgen_etr env loc etr hcs0
       | ttsub' ->
          let nd = Zipper.get tr in
          let target, (source, _) = List.last ttsub' in
          let ttsub_ord, ttsub_exp =
            List.partition (snd >> fst >> Term.coeffs >> (=) []) ttsub'
          in
          let locs =
            Zipper.find_all
              (fun nd' -> CallId.is_ancestor_or_eq
                            (root_id_of nd.CallTree.name)
                            nd'.CallTree.name)
              (Zipper.root loc)
          in
          let pvas_arg =
            try
              root_id_of nd.CallTree.name
              |> RefType.find_last_base_exc env
              |> RefType.pva_of_var env
              |> List.return
            with Not_found ->
              []
          in
          let pvas_source =
            let last_base =
              RefType.find_last_base
                env
                (root_id_of nd.CallTree.name)
            in
            match List.unique (Term.fvs source) with
            | xs when List.for_all (RefType.visible last_base) xs ->
               []
            | [src] when Idnt.is_top src ->
               []
            | [src] when Idnt.is_pos src ->
               posts env loc src
            | [src] ->
               pres env loc src
            | _ ->
               Format.printf "%a,%a@," Term.pr source Idnt.pr last_base;
               assert false
          in
          let pvas_target =
            if Idnt.is_top target then
              assert false
            else if Idnt.is_pos target then
              posts env loc target
            else
              pres env loc target
          in
          let pvas_comm =
            pvas_arg @ pvas_source @ pvas_target |> List.unique
          in
          let pvas_guard, phi_guard =
            locs
            |> List.map
                 (fun (Zipper.Loc(tr, _)) ->
                  fst (Zipper.get tr).CallTree.data)
            |> (@) (List.map Formula.of_ttsub_elem ttsub_ord)
            |> Formula.band
            |> Formula.conjuncts_of
            |> HornClause.body_of_formulas
            |> Pair.unfold HornClause.pvas_of_body HornClause.phi_of_body
          in
          let hcs_exparam, pvas_exparam =
            ttsub_exp
            |> List.map
                 (fun (x, (t, ty)) ->
                  let tenv =
                    SimTypJudge.env_of t ty
                    |> TypEnv.filter_ty Type.mk_int
                    |> List.map (fun x -> x, Type.mk_int)
                    |> List.sort compare
                    |> flip (@) [x, ty]
                  in
                  let pid =
                    if not !flag_coeff then
                      Idnt.new_coeff ()
                    else
                      List.hd (List.sort compare (Term.coeffs t))
                  in
                  HornClause.mk_def
                    (PredVar.make pid tenv)
                    []
                    (Formula.of_ttsub [x, (t, ty)]),
                  Pva.of_tenv pid tenv)
            |> List.split
          in
          let hcs =
            HornClause.mk_def
              (RefType.pred_of_var env target)
              (pvas_guard
               @ (List.concat_map
                    (fun (Zipper.Loc(tr, _)) -> snd (Zipper.get tr).CallTree.data)
                    locs) @ pvas_exparam
               @ pvas_comm)
              phi_guard
            |> flip List.cons (hcs_exparam @ hcs0)
          in
          let loc' =
            let nd' =
              { nd with
                data =
                  fst nd.CallTree.data
                  |> flip List.cons (List.map Formula.of_ttsub_elem ttsub_ord)
                  |> Formula.band,
                  snd nd.CallTree.data @ pvas_exparam }
            in
            Zipper.Loc (Zipper.set tr nd', p)
          in
          cgen_etr env loc' etr hcs
     end
  | Trace.Ret(Idnt.T(f, _, _) as x, (t, ty)) :: etr ->
     assert (Type.is_base ty);
     let hcs =
       (if refinable ty then [x, (t, ty)] else [])
       |> List.map Formula.of_ttsub_elem
       |> List.cons (fst (Zipper.get tr).CallTree.data)
       |> Formula.band
       |> HornClause.mk_def
            (RefType.pred_of_var env x)
            [assert false(*@todo implement*)]
       |> flip List.cons hcs0
     in
     if Idnt.is_pos f then
       let loc' = Zipper.up loc in
       cgen_etr env loc' etr hcs
     else if Idnt.is_neg f then
       let loc' =
         Zipper.insert_down
           loc
           (CallTree.make (CallId.parent_id_of f) true (Formula.mk_true, []))
       in
       cgen_etr env loc' etr hcs
     else
       assert false
  | Trace.Nop :: etr ->
     cgen_etr env loc etr hcs0
  | Trace.Assume(None, phi) :: etr ->
     let nd = Zipper.get tr in
     assert (nd.CallTree.name |> fst |> Idnt.is_top);
     let loc' =
       let nd' =
         { nd with data = Formula.band [fst nd.CallTree.data;
                                        phi],
                          snd nd.CallTree.data }
       in
       Zipper.Loc (Zipper.set tr nd', p)
     in
     cgen_etr env loc' etr hcs0
  | Trace.Assume(Some pva, phi) :: etr ->
     let nd = Zipper.get tr in
     assert (nd.CallTree.name |> fst |> Idnt.is_top);
     let hcs =
       let pvas_arg =
         try
           nd.CallTree.name
           |> RefType.find_last_base_exc env
           |> RefType.pva_of_var env
           |> List.return
         with Not_found ->
           []
       in
       let pvas_guard, phi_guard =
         fst nd.CallTree.data
         |> Formula.conjuncts_of
         |> HornClause.body_of_formulas
         |> Pair.unfold HornClause.pvas_of_body HornClause.phi_of_body
       in
       (* can we assume that [phi_eq] is a tautology? *)
       let pv, phi_eq = Pva.pvar_of pva in
       let phi_head = Formula.band [phi; phi_eq] in
       let tenv =
         let ys = Pva.fvs pva in
         Pva.args_of pva
         |> List.last
         |> Pair.map_fst Term.var_of
         |> flip List.cons
           (List.filter
              (fun (x, _) -> List.mem x ys |> not)
              (PredVar.args_of pv))
       in
       HornClause.make
         (HornClause.mk_head ~tenv ~phi:phi_head (Some pv))
         (HornClause.mk_body
            (pvas_guard @ snd nd.CallTree.data @ pvas_arg)
            phi_guard)
       |> flip List.cons hcs0
     in
     let loc' =
       let nd' =
         Logger.printf "adding %a to the env@," Pva.pr pva;
         { nd with data = Formula.band [fst nd.CallTree.data;
                                        Pva.to_formula pva],
                          snd nd.CallTree.data }
       in
       Zipper.Loc (Zipper.set tr nd', p)
     in
     cgen_etr env loc' etr hcs
  | Trace.Error :: etr ->
    assert (etr = []);
    let nd = Zipper.get tr in
    assert (nd.CallTree.name |> fst |> Idnt.is_top);
    let pvas_arg =
      try
        nd.CallTree.name
        |> RefType.find_last_base_exc env
        |> RefType.pva_of_var env
        |> List.return
      with Not_found ->
        []
    in
    let pvas_guard, phi_guard =
      fst nd.CallTree.data
      |> Formula.conjuncts_of
      |> HornClause.body_of_formulas
      |> Pair.unfold HornClause.pvas_of_body HornClause.phi_of_body
    in
    Zipper.root
      (Zipper.Loc
         (Zipper.set tr { nd with closed = false }, CallTree.path_set_open p)),
    HornClause.mk_goal
      (pvas_guard
       @ snd nd.CallTree.data
       @ pvas_arg)
      phi_guard
    |> flip List.cons hcs0
  | _ ->
    assert false
(** generate a set of constraints from an error trace
    @require a function definition that contains [assert false] is of the form [f ~x | phi = assert false] *)
let cgen_etr env etr =
  match etr with
  | Trace.Call(x, guard) :: etr ->
    let loc = Zipper.zipper (CallTree.make x true (guard, [])) in
    let ctr, hcs = cgen_etr env loc etr [] in
    if not !flag_coeff then
      begin
        Logger.debug_assert
          (fun () ->
             hcs
             |> List.filter_map
               (HornClause.fold
                  (fun _ _ -> None)
                  (fun pv _ _ -> Some(PredVar.idnt_of pv)))
             |> Bag.non_duplicated);
        ctr, hcs
      end
    else
      hcs
      |> List.classify
        (fun hc1 hc2 ->
           match HornClause.nodeH hc1, HornClause.nodeH hc2 with
           | Some(p1), Some(p2) -> p1 = p2
           | _ -> false)
      |> List.map List.hd
      |> Pair.make ctr
  | _ -> assert false

let cgen_prog prog =
  Logger.printf0 "@[<v>";
  prog
  |> Logger.pprintf "prog:@,  %a@," Prog.pr
  |> RefTypJudge.constr_of_prog
  |> Logger.pprintf "typability constraint:@,  %a@," Formula.pr
  |> HCCS.of_formula []
  |> List.map HornClause.normalize
  |> Logger.pprintf "HCCS generated:@,  %a@," HCCS.pr_verbose
  |> HCCS.backward_depend [None]
  |> Logger.pprintf "HCCS after backward slicing:@,  %a@," HCCS.pr_verbose
  |> HCCS.reduce (fun pid -> false)
  |> Logger.pprintf "HCCS after reduction:@,  %a@]@," HCCS.pr_verbose

let cut_points_of prog =
  prog
  |> cgen_prog
  |> HCCS.pvs
  |> List.unique
  |> Logger.pprintf "Cut points:@,  %a@," (List.pr Idnt.pr ",")

(** {6 Extra parameter inference for relatively complete verification} *)

let enable_coeff_const = ref false
let number_of_extra_params = ref 1

let param_header = "_ep"
let is_parameter s = String.starts_with s param_header

let prev_sol = ref ([] : (Idnt.t * Term.t) list)
let prev_constrs = ref ([] : Formula.t list)
let masked_params : Idnt.t list ref = ref []
let params = ref []

(** @todo [exs] may contain ex-quantified vars not related to the recursive calls *)
let new_params recursive bvs exs =
  List.gen
    !number_of_extra_params
    (fun i ->
       let ps =
         List.gen
           (List.length bvs + if !enable_coeff_const then 1 else 0)
           (fun i -> Idnt.new_coeff ~header:param_header ())
       in
       params := !params @ ps;
       let xs =
         match recursive with
         | None -> []
         | Some(xs) -> xs
       in
       if !enable_coeff_const (*&& recursive = None*) then
         masked_params := List.hd ps :: !masked_params;
       (if !enable_coeff_const then [Term.mk_var (List.hd ps)] else [])
       @
       (*
         let b = recursive <> None
                 && xs = []
                 && Set_.subset bvs exs
         in
        *)
       List.map2
         (fun p x ->
            begin
              (* some heuristics *)
              (*if b then () else*)
              if recursive <> None then
                (if xs = [] then
                   begin
                     (*this is necessary for l-length_cps-append.ml*)
                     if List.mem x exs then
                       masked_params := p :: !masked_params
                   end
                 else if not (List.mem x xs) then
                   masked_params := p :: !masked_params)
                (* how to deal with non-recursive function calls here? *)
          (*
              else if List.mem x exs then
                masked_params := p :: !masked_params
           *)
            end;
            IntTerm.mul (Term.mk_var p) (Term.mk_var x))
         (if !enable_coeff_const then List.tl ps else ps)
         bvs
       |> IntTerm.sum)

let init_sol prog =
  prog
  |> Prog.coeffs
  |> List.unique
  |> Logger.pprintf "parameters: %a@," Idnt.pr_list
  |> List.map (flip Pair.make IntTerm.zero)
  |> fun sol -> prev_sol := sol
let init_sol = Logger.log_block1 "RefTypInfer.init_sol" init_sol

let update_sol sol =
  prev_sol :=
    sol @ List.filter (fst >> flip List.mem_assoc sol >> not) !prev_sol

let update_constrs constr = prev_constrs := constr :: !prev_constrs

let solve_ext_params hcs =
  let (psub, sub), constr =
    try
      EAHCCSSolver.solve
        !prev_sol
        !prev_constrs
        !masked_params
        (fun hcs ->
           try
             HCCSSolver.solve_dyn hcs
           with
           | HCCSSolver.NoSolution
           | HCCSSolver.Unknown ->
             raise FailedToRefineTypes
           | EAHCCSSolver.NoSolution
           | EAHCCSSolver.Unknown ->
             raise FailedToRefineInputTypes)
        hcs
    with
    | EAHCCSSolver.NoSolution
    | EAHCCSSolver.Unknown (*@todo*) ->
      raise FailedToRefineExtraParameters
  in
  update_constrs constr;
  update_sol sub;
  psub
let solve_ext_params =
  Logger.log_block1 "RefTypInfer.solve_ext_params" solve_ext_params

(** {6 Refinement type inference} *)

let cut_points_only = ref false
let no_inlining = ref false

let rec rty_of_sol env sol fcs x =
  env x
  |> Type.visit
    (object
      method fvar _ = assert false
      method fbase c =
        sol
        |> List.filter_map
          (function
            | (x', (tenv, phi)) when x' = x ->
              phi
              |> Formula.subst
                (PredVar.pat_match
                   (PredVar.make x tenv)
                   (RefType.pred_of_var env x))
              |> Option.some
            | _ -> None)
        |> Formula.band
        |> fun phi -> RefType.Base(x, c, phi)
      method farrow ty1 ty2 =
        let ty = Type.mk_fun_args_ret [ty1] ty2 in
        try
          fcs
          |> List.filter_map
            (fun (y, uid) -> if x = y then Some(uid) else None)
          |> List.map
            (fun uid ->
               List.init
                 (Type.arity_of ty + 1)
                 (fun i -> Idnt.T(x, uid, i) |> rty_of_sol env sol fcs)
               |> RefType.mk_fun)
          |> RefType.merge
        with Not_found ->
          RefType.of_simple_type ty
      method fforall p ty1 = assert false
      method fexists p ty1 = assert false
    end)
let rty_of_sol = Logger.log_block4 "RefTypInfer.rty_of_sol" rty_of_sol

let rtenv_of_sol env fcs sol =
  fcs
  |> List.map fst
  |> List.filter Idnt.is_top
  |> List.unique
  |> List.map
    (Pair.unfold id (rty_of_sol env sol fcs >> RefType.canonize))
let rtenv_of_sol = Logger.log_block3 "RefTypInfer.rtenv_of_sol" rtenv_of_sol

let comp_rtenv prog rtenv =
  prog.Prog.types
  |> List.filter_map
    (fun (f, sty) ->
       if not (Map_.in_dom f rtenv) then
         Some(f, RefType.of_simple_type sty)
       else
         None)
  |> (@) rtenv
let comp_rtenv = Logger.log_block2 "RefTypInfer.comp_rtenv" comp_rtenv

(** refinement type inference via HCCS solving
    @param fs inlined functions
    @param etrs error traces *)
let infer_etrs fs is_cut_point prog solver etrs =
  let is_inlined p =
    not (Idnt.is_coeff p)
    && let Idnt.V(f), _ = CallId.root_id_of p in
    List.exists ((=) f) fs
  in
  let solver' = solver solve_ext_params in
  etrs
  |> List.map (cgen_etr (TypEnv.lookup prog.Prog.types))
  |> List.unzip
  |> Pair.map_fst
    (Logger.printf "call trees:@,  %a@," (List.pr CallTree.pr "@,"))
  |> snd
  |> List.concat
  |> List.map (HornClause.simplify_full [])
  |> List.map HornClause.normalize
  |> Logger.pprintf "HCCS generated:@,  %a@," HCCS.pr_verbose
  |> (if_
        (const (false && !exp_mode))
        (sef
           (HCCS.save_smtlib
              (Filename.chop_extension !Global.target_filename
               ^ "_orig_hccs"
               ^ string_of_int !Global.cegar_iterations
               ^ ".smt")))
        id)
  |> (if_
        (const !exp_mode)
        (sef
           (HCCS.save_graphviz
              (Filename.chop_extension !Global.target_filename
               ^ "_orig_hccs"
               ^ string_of_int !Global.cegar_iterations
               ^ ".dot")))
        id)
  |> (solver'
      |> (if_ (const !cut_points_only)
            (flip
               (ReduceHCCSSolver.solve
                  (Pair.unfold Idnt.is_coeff is_cut_point >> uncurry2 (||)))
               (GenHCCSSolver.solve (CHGenInterpProver.interpolate true)))
            id)
      |> (if_ (const !no_inlining)
            id
            (InlineHCCSSolver.solve is_inlined)))
  |> rtenv_of_sol
    (TypEnv.lookup prog.Prog.types)
    ((* this seems not necessary (@todo use sol instead) *)
      etrs
      |> List.map Trace.function_calls_of
      |> List.flatten
      |> List.unique)
  |> comp_rtenv prog
let infer_etrs = Logger.log_block5 "RefTypInfer.infer_etrs" infer_etrs

let is_cut_point prog =
  if !cut_points_only then
    let pvs = cut_points_of prog in
    fun p -> List.exists (Idnt.cong p) pvs
  else
    fun _ -> true
