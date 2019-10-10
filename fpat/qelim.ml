open Util
open Combinator

(** Quantifier elimination for formulas *)

(* external functions *)

let ext_integer_qelim = ref (fun _ -> assert false : Formula.t -> Formula.t)
let ext_real_qelim = ref (fun _ -> assert false : Formula.t -> Formula.t)
let integer_qelim_dyn phi = try !ext_integer_qelim phi with _ -> phi
let real_qelim_dyn phi = try !ext_real_qelim phi with _ -> phi

(** [elim_bool_vars bvs phi] eliminates all the boolean variables
    [bvs] (which are implicitly existentially quantified) *)
let elim_bool_vars bvs phi =
  if bvs = [] then  phi
  else
    bvs
    |> TypTermSubst.bool_valuations
    |> (List.map
          (fun venv ->
             phi
             |> Formula.subst (TypTermSubst.tsub_of venv)
             |> FormulaSimplifier.simplify))
    |> Formula.bor

let iqelim tenv phi =
  try
    phi
    |> (if_ CunFormula.is_linear (Formula.exists tenv >> integer_qelim_dyn) id)
    |> FormulaSimplifier.simplify
    |> (if_ CunFormula.is_disjunctive (const phi) id)
  with Global.NotImplemented _ -> phi

(** [elim_int_vars bvs phi] eliminates as many integer variables in
    [phi] (which are implicitly existentially quantified) as possible

    @ensure variables in [bvs] are not eliminated *)
let elim_int_vars bvs phi =
  let tenv =
    Set_.diff (Formula.fvs_int phi) bvs |> List.map (flip Pair.make Type.mk_int)
  in
  if tenv = [] || Formula.coeffs phi <> [] then phi
  else begin
    Logger.printf2
      "input:@,  @[<v>phi: %a@,tenv: %a@]@,"
      Formula.pr phi
      TypEnv.pr tenv;
    CunFormula.case_analysis_boolean
      FormulaSimplifier.simplify
      (fun [phi] -> iqelim tenv phi)
      [phi]
  end
let elim_int_vars =
  Logger.log_block2 "Qelim.elim_int_vars" elim_int_vars
(** [elim_int_vars_opt bvs phi] eliminates as many integer variables in
    [phi] (which are implicitly existentially quantified) as possible

    [phi] represents a formula with integer and boolean variables
    @ensure variables in [bvs] are not eliminated *)
(* val elim_int_vars_opt : Idnt.t list -> Formula.t -> Formula.t *)
let elim_int_vars_opt bvs phi =
  let rec rel phi1 phi2 =
    Set_.intersects
      (Set_.diff (Formula.fvs phi1) bvs)
      (Set_.diff (Formula.fvs phi2) bvs)
  in
  phi
  |> Formula.conjuncts_of
  |> Set_.equiv_classes rel
  |> List.map (Formula.band >> elim_int_vars bvs)
  |> Formula.band
let elim_int_vars_opt =
  Logger.log_block2 "Qelim.elim_int_vars_opt"
    ~before:(fun bvs phi ->
        Logger.printf2
          "input:@,  @[<v>phi: %a@,bvs: %a@]@,"
          Formula.pr phi
          Idnt.pr_list bvs)
    elim_int_vars_opt

let elim_int_vars_smt ?(tenv=[]) bvs phi =
  if Formula.coeffs phi = [] &&
     Set_.intersects (Formula.fvs phi) bvs |> not then
    try
      if SMTProver.is_sat_dyn ~tenv phi then Formula.mk_true else Formula.mk_false
    with SMTProver.Unknown -> elim_int_vars_opt bvs phi
  else elim_int_vars_opt bvs phi

let elim_int_vars_full bvs =
  Formula.conjuncts_of
  >> List.maplr
    (fun ls phi rs ->
       if Formula.coeffs phi = [] then phi
       else
         let elim_vars =
           List.filter
             (fun x -> not (List.mem x bvs || Idnt.is_coeff x))
             (Set_.diff
                (Formula.fvs_int phi)
                (List.concat_map Formula.fvs_int (ls @ rs)))
         in
         if elim_vars = [] then phi
         else
           try
             let tenv = List.map (fun x -> x, Type.mk_int) elim_vars in
             [phi]
             |> (CunFormula.case_analysis_boolean
                   FormulaSimplifier.simplify
                   (List.elem_of_singleton
                    >> Formula.exists tenv
                    >> integer_qelim_dyn))
           with Global.NotImplemented _ -> phi)
  >> Formula.band

let post_process phi =
  if Formula.fvs_bool phi <> [] then FormulaSimplifier.simplify phi
  else
    let phi' =
      phi
      |> Formula.map_atom (CunAtom.elim_beq_bneq ~no_iff:false) (* eliminate =b and <>b *)
      |> Formula.elim_imply_iff
      |> FormulaSimplifier.simplify
    in
    if phi = phi' then phi
    else phi' |> DNF.of_formula |> DNF.formula_of |> FormulaSimplifier.simplify
(* constant propagation *)
let propagate bvs phi =
  let is_const (x, (t, ty)) =
    List.mem x bvs (* this is correct *)&&
    (ty = Type.mk_bool &&
     (Formula.of_term t = Formula.mk_true ||
      Formula.of_term t = Formula.mk_false) ||
     false && ty = Type.mk_int && IntTerm.is_const t)
  in
  let tsub =
    phi
    |> Formula.conjuncts_of
    |> List.filter_map
      (fun phi ->
         try
           phi
           |> LinTermIntRel.elem_of_formula is_const
           |> Option.some
         with Not_found -> None)
    |> TypTermSubst.tsub_of
  in
  tsub
  |> List.map
    (fun (x, t) ->
       if Formula.is_true @@ Formula.of_term t
       then Formula.of_term (Term.mk_var x)
       else if Formula.is_false @@ Formula.of_term t
       then Formula.bnot (Formula.of_term (Term.mk_var x))
       else if IntTerm.is_const t then begin
         assert false; (* @todo *)
         Atom.eq Type.mk_int (Term.mk_var x) t
         |> Formula.of_atom
       end else assert false)
  |> List.cons (Formula.subst tsub phi)
  |> Formula.band
  |> post_process
