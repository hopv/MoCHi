open Util
open Combinator

(** Ranking function inference *)

let rank_widen = ref false

exception LRFNotFound
exception LLRFNotFound

let find_atom hcs =
  let is_fail pid =
    let s = Idnt.base pid in
    String.length s >= 4 && String.sub s 0 4 = "fail"
  in
  if List.exists is_fail (HCCS.pvsH hcs) then begin
    let [hc] =
      List.filter
        (HornClause.fold
           (fun _ _ -> false)
           (fun pv _ _ -> is_fail (PredVar.idnt_of pv)))
        hcs
    in
    HornClause.fold
      (fun _ _ -> assert false)
      (fun _ [atm] phi ->
         let phis = Formula.conjuncts_of phi in
         let pred phi =
           match Formula.term_of phi with
           | Term.Var(x) -> is_fail x(* <fail:??:0> *)
           | _ -> false
         in
         (*         assert (List.exists pred phis);*)
         atm, (List.filter (pred >> not) phis) |> Formula.band)
      hc
  end else
    let [hc] = List.filter HornClause.is_root hcs in
    HornClause.fold
      (fun [atm] _ -> atm, Formula.mk_true)
      (fun _ _ _ -> assert false)
      hc

let compute_strongest_post prog ce ext_cex =
  let penv =
    List.map
      (fun (p, ps) ->
         let cnt = ref 0 in
         p,
         fun ts ->
           let (tenv, phi) = List.nth ps !cnt in
           cnt := !cnt + 1;
           let tsub = List.map2 (fun (x, _) t -> x, t) tenv ts in
           let tts = List.map2 (fun (_, ty) t -> t, ty) tenv ts in
           Pva.make (Idnt.T(p, !cnt, 0)) tts,
           Formula.subst tsub phi)
      ext_cex
  in
  let etr =
    match CompTreeExpander.error_traces_of prog false penv [ce] with
    | [etr] -> etr
    | etrs ->
      Format.printf "prog: %a@," Prog.pr prog;
      Format.printf "ce: %a@," (List.pr Integer.pr ":") ce;
      Format.printf "traces: %a@," (List.pr Trace.pr "@,") etrs;
      assert false
  in
  let _, hcs = RefTypInfer.cgen_etr (TypEnv.lookup prog.Prog.types) etr in
  let hcs = List.map (HornClause.simplify_full []) hcs in
  Logger.printf "Horn clauses:@,  %a@," HCCS.pr hcs;
  let env, spc =
    let atm, phi = find_atom hcs in
    let env =
      RefType.visible_vars (TypEnv.lookup prog.Prog.types) (Pva.idnt_of atm)
    in
    assert
      (List.for_all2
         (fun (x, _) -> function
            | (Term.Var(y), _) -> true (*x = y*)
            (* @todo how x is related to y? *)
            | _ -> true (*assert false*))
         env
         (Pva.args_of atm));
    env,
    try
      Formula.mk_and phi (PredSubst.lookup_fresh (FwHCCSSolver.solve hcs) atm)
    with Not_found -> assert false
  in
  let spc, env =
    let f = Idnt.base (fst (List.hd env)) in
    let typ = TypEnv.lookup prog.Prog.types (Idnt.make f) in
    let targs, _ = Type.args_ret typ in
    let fdef = List.hd (Prog.fdefs_of prog (Idnt.make f)) in
    let args =
      List.filter_map2
        (fun x ty ->
           if Type.is_base ty then Some(x) else None)
        fdef.Fdef.args
        targs
    in
    assert (List.length args = List.length env);
    let map =
      List.combine
        (List.map fst env)
        (List.map (function Pattern.V(x) -> x |> Term.mk_var) args)
    in
    Formula.subst map spc,
    List.map2 (fun (_, ty) (Pattern.V(x)) -> x, ty) env args
  in
  env
  |> List.filter (* remove variables prev_set_flag_* *)
    (fst >> Idnt.base >> flip String.starts_with "prev_set_flag" >> not)
  |> List.filter (snd >> (<>) Type.mk_unit)
  |> List.filter (snd >> (<>) Type.mk_bool)
  |> Logger.pprintf "variables in the scope:@,  %a@," TypEnv.pr,
  spc
  |> CunFormula.elim_unit
  |> Qelim.elim_bool_vars (Formula.fvs_bool spc)
  |> Logger.pprintf "strongest post condition:@,  %a@," Formula.pr



let inferCoeffs argumentVariables linear_templates constraints =
  (* reduce to linear constraint solving *)
  (** solve constraint and obtain coefficients **)
  let correspondenceVars =
    constraints
    |> PolyConstrSolver.gen_coeff_constr ~pos:false ~linear:true
    |> PolyConstrSolver.solve_dyn
  in
  if correspondenceVars = [] then begin
    Format.printf "Invalid ordered.@."; raise PolyConstrSolver.Unknown
  end;
  Logger.printf
    "Inferred coefficients:@.  %a@." PolyConstrSolver.pr correspondenceVars;
  List.map
    (fun linTemp ->
       let correspondenceCoeffs, const_part =
         LinTermIntExp.of_term (Term.subst correspondenceVars linTemp)
       in
       (** extract coefficients **)
       let coefficients =
         let cor dict x = try List.assoc x dict with Not_found -> 0 in
         let formatter (n, v) = (v, IntTerm.int_of n) in
         List.map
           (cor (List.map formatter correspondenceCoeffs))
           argumentVariables
       in
       (coefficients, IntTerm.int_of const_part))
    linear_templates

let inferCoeffsAndExparams argumentVariables linear_templates constraints =
  (* reduce to non-linear constraint solving *)
  (** solve constraint and obtain coefficients **)
  let correspondenceVars =
    constraints
    |> PolyConstrSolver.gen_coeff_constr ~pos:false ~linear:true
    |> PolyConstrSolver.solve_dyn
  in
  if correspondenceVars = [] then begin
    Format.printf "Invalid ordered.@."; raise PolyConstrSolver.Unknown
  end;
  Logger.printf
    "Inferred coefficients:@.  %a@." PolyConstrSolver.pr correspondenceVars;
  List.map
    (fun linTemp ->
       let correspondenceCoeffs, const_part =
         LinTermIntExp.of_term (Term.subst correspondenceVars linTemp)
       in
       (** extract coefficients **)
       let coefficients =
         let cor dict x = try List.assoc x dict with Not_found -> 0 in
         let formatter (n, v) = (v, IntTerm.int_of n) in
         List.map
           (cor (List.map formatter correspondenceCoeffs))
           argumentVariables
       in
       (coefficients, IntTerm.int_of const_part))
    linear_templates,
  List.map
    (fun (v, t) -> Idnt.string_of v, IntTerm.int_of t)
    correspondenceVars


let lrf exparam spc spcWithExparam arg_vars prev_vars =
  let arg_env = List.map (fun a -> (a, Type.mk_int)) arg_vars in
  (* make templates *)
  let linear_template = Template.mk_linexp arg_env in
  let linear_template_prev =
    Term.subst
      (List.combine arg_vars (List.map Term.mk_var prev_vars))
      linear_template
  in
  Logger.printf "Linear template:@.  %a@." Term.pr linear_template;
  (* make a constraint: spc => R(x_prev) > R(x) && R(x) >= 0 *)
  let constraints =
    Formula.imply
      spc
      (Formula.band
         [ IntFormula.gt linear_template_prev linear_template;
           IntFormula.geq linear_template IntTerm.zero])
  in
  Logger.printf "Constraint:@.  %a@." Formula.pr constraints;
  (* solve constraints and obtain coefficients of a ranking function *)
  try inferCoeffs arg_vars [linear_template] constraints, []
  with
  | PolyConstrSolver.NoSolution
  | PolyConstrSolver.Unknown ->
    if exparam then begin
      Logger.printf0 "Try to update extra parameters...@.@.";
      try
        (* make a constraint: spc => R(x_prev) > R(x) && R(x) >= 0 *)
        let constraints =
          Formula.imply
            spcWithExparam
            (Formula.band
               [ IntFormula.gt linear_template_prev linear_template;
                 IntFormula.geq linear_template IntTerm.zero])
        in
        Logger.printf "Constraint:@.  %a@." Formula.pr constraints;
        (* solve constraints and obtain coefficients of a ranking function *)
        inferCoeffsAndExparams arg_vars [linear_template] constraints
      with
      | PolyConstrSolver.NoSolution
      | PolyConstrSolver.Unknown ->
        Logger.printf0 "Failed to find LRF...@.";
        raise LRFNotFound
      | e ->
        Logger.printf "error: %a@." String.pr (Printexc.to_string e);
        raise LRFNotFound
    end else begin
      Logger.printf0 "Failed to solve the constraints...@.@.";
      raise LRFNotFound
    end
  | e ->
    Logger.printf "error: %a@." String.pr (Printexc.to_string e);
    raise LRFNotFound

let lrf exparam spcs spcWithExparams arg_vars prev_vars =
  if not !rank_widen then
    let spc = List.hd spcs in
    let spcWithExparam = List.hd spcWithExparams in
    lrf exparam spc spcWithExparam arg_vars prev_vars
  else
    try
      let spcWithExparam = List.hd spcWithExparams in
      let spcs, _ =
        List.mapLar
          (fun _ a x _ ->
           let x' = Formula.mk_or a x in
           x', x')
          Formula.mk_false (List.rev spcs)
      in
      let spc = Polyhedron.widen_list_dyn spcs in
      Format.printf "spcs: %a@,spcWiden: %a@," (List.pr Formula.pr ":") spcs Formula.pr spc;
      lrf exparam spc spcWithExparam arg_vars prev_vars
    with LRFNotFound ->
      let spc = List.hd spcs in
      let spcWithExparam = List.hd spcWithExparams in
      lrf exparam spc spcWithExparam arg_vars prev_vars

let makeLexicographicConstraints variables linearTemplates prevLinearTemplates failedSpc =
  (** make a constraint:
         [spc1 => R1(x_prev) > R1(x) /\ R1(x) >= 0]
      /\ [spc2 => R1(x_prev) >= R1(x)
               /\ R2(x_prev) > R2(x) /\ R2(x) >= 0]
      /\ [spc3 => R1(x_prev) >= R1(x)
               /\ R2(x_prev) >= R2(x)
               /\ R3(x_prev) > R3(x) /\ R3(x) >= 0]
      ...
   **)
  let lenSpcSequence = List.length failedSpc in
  let subst_ith i =
    Formula.subst
      (List.map
         (fun v ->
            (v,
             Term.mk_var
               (Idnt.rename_base
                  (fun v -> v ^ "_IN_" ^ string_of_int i ^ "TH_ERRORPATH")
                  v)))
         variables)
  in
  let nth_constraints n =
    let rec go i =
      let ith_ltp, ith_lt =
        List.nth prevLinearTemplates i, List.nth linearTemplates i
      in
      if i < n
      then IntFormula.geq ith_ltp ith_lt :: go (i+1)
      else [IntFormula.gt ith_ltp ith_lt; IntFormula.geq ith_lt IntTerm.zero]
    in
    let nth_spc = List.nth failedSpc n in
    subst_ith n (Formula.imply nth_spc (Formula.band (go 0)))
  in
  Formula.band
    (List.unfold
       (fun i ->
          if i < lenSpcSequence then Some (nth_constraints i, i+1) else None)
       0)

let llrf
    exparam
    spcSequence
    spcSequenceWithExparam
    allVars
    arg_vars
    prev_vars =
  let arg_env = List.map (fun a -> (a, Type.mk_int)) arg_vars in
  (* make templates (for arguments and previous arguments) *)
  let linearTemplates =
    List.unfold
      (fun i ->
         if i < List.length spcSequence then
           Some (Template.mk_linexp arg_env, i+1)
         else None)
      0
  in
  let prevLinearTemplates =
    List.map
      (Term.subst
         (List.combine arg_vars (List.map Term.mk_var prev_vars)))
      linearTemplates
  in
  List.iteri
    (fun i lt ->
       Logger.printf2 "Linear template(%a):@.  %a@." Integer.pr i Term.pr lt)
    linearTemplates;
  (* make a constraint *)
  let constraints =
    makeLexicographicConstraints
      allVars
      linearTemplates
      prevLinearTemplates
      spcSequence
  in
  Logger.printf "Constraint:@.  %a@." Formula.pr constraints;
  (* solve constraint and obtain coefficients *)
  try inferCoeffs arg_vars linearTemplates constraints, []
  with
  | PolyConstrSolver.NoSolution
  | PolyConstrSolver.Unknown ->
    if exparam then begin
      Logger.printf0 "Try to update extra parameters...@.@.";
      try
        (* make a constraint *)
        let constraints =
          makeLexicographicConstraints
            allVars
            linearTemplates
            prevLinearTemplates
            spcSequenceWithExparam
        in
        Logger.printf "Constraint:@.  %a@." Formula.pr constraints;
        (* solve constraint and obtain coefficients *)
        inferCoeffsAndExparams arg_vars linearTemplates constraints
      with
      | PolyConstrSolver.NoSolution
      | PolyConstrSolver.Unknown ->
        Logger.printf0 "Failed to find LLRF...@.";
        raise LLRFNotFound
      | e ->
        Logger.printf "error: %a@." String.pr (Printexc.to_string e);
        raise LLRFNotFound
    end else begin
      Logger.printf0 "Failed to find LLRF...@.";
      raise LLRFNotFound
    end
  | e ->
    Logger.printf "error: %a@." String.pr (Printexc.to_string e);
    raise LLRFNotFound
