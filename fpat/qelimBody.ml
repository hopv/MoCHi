open Util
open Combinator

(** Quantifier elimination for bodies *)

let lift f (atms, phi) =
  let tsub, phi' = f phi in
  List.map (Pva.subst tsub) atms, phi'
let lift3 f (atms, phi) =
  let ttsub, phi' = f phi in
  atms, Formula.mk_and phi' (Formula.of_ttsub ttsub)
let lift2 f (atms, phi) = atms, f (List.concat_map Pva.fvs atms) phi

(** [elim_int_vars_quick p (atms, phi)] eliminates as many integer
    variables in [(atms, phi)] (which are implicitly existentially
    quantified) as possible

    @param phi a formula with integer and boolean variables
    @ensure variables in [{x | p x}] are not eliminated *)
let rec elim_int_vars_quick p (atms, phi) =
  if false (*Term.coeffs phi <> []*) then
    (** @todo unsound for linear expressions with unknown coefficients? *)
    atms, phi
  else
    let env, phi =
      let pred =
        let xs = List.concat_map Pva.fvs atms in
        let nlfvs = CunTerm.nlfvs (Formula.term_of phi) in
        fun (x, (t, ty)) ->
          not (p x) &&
          (not (List.mem x xs) || (Term.coeffs t = [] && not (Term.is_app t))) &&
          (** avoid substituting a non-linear integer expression to other one
              raising the order of parameters for parametric linear expressions sometimes
              causes a failure of the bit-vector-based non-linear constraint solving *)
          (if List.mem x nlfvs then CunTerm.is_linear t else true)
      in
      phi
      |> Formula.conjuncts_of
      |> LinTermIntRel.of_formulas pred
      |> Pair.map_fst TypTermSubst.tsub_of
    in
    if env = [] then atms, phi
    else
      (atms |> List.map (Pva.subst_fixed env),
       (* @todo may not terminate *)
       Formula.subst_fixed ~simplify:FormulaSimplifier.simplify env phi)
      |> elim_int_vars_quick p
let elim_int_vars_quick =
  Logger.log_block2 "QelimBody.elim_int_vars_quick"
    ~before:(fun _ -> snd >> Logger.printf "input: %a@," Formula.pr)
    ~after:(snd >> Logger.printf "output: %a" Formula.pr)
    elim_int_vars_quick

let elim_int_vars_formula bvs phi =
  ([], phi)
  |> elim_int_vars_quick (fun x -> List.mem x bvs || Idnt.is_coeff x)
  |> snd

(** [xs] a former member has a higher priority in the parameter
    selection

    @ensure variables in [bvs] are not eliminated *)
(* val elim_int_vars_full : Idnt.t list -> Formula.t -> Formula.t *)
let elim_int_vars_full bvs phi =
  ([], Formula.to_rename_tsub FormulaSimplifier.simplify bvs phi |> snd)
  |> elim_int_vars_quick (fun x -> List.mem x bvs || Idnt.is_coeff x)
  |> snd

(** [elim_int_vars bvs (atms, phi)] eliminates as many integer
    variables in [(atms, phi)] (which are implicitly existentially
    quantified) as possible

    @param phi a formula with integer and boolean variables
    @ensure variables in [bvs] are not eliminated *)
let elim_int_vars tenv bvs (atms, phi) =
  (atms, phi)
  |> lift (Formula.to_rename_tsub FormulaSimplifier.simplify bvs)
  |> lift2 (fun bvs' -> elim_int_vars_formula ((bvs @ bvs') |> List.unique))
  |> lift2 (fun bvs' -> Qelim.elim_int_vars_smt ~tenv ((bvs @ bvs') |> List.unique))
  |> (if true then id else lift2 (fun bvs' -> Qelim.elim_int_vars_full ((bvs @ bvs') |> List.unique)))
  |> (if true then id
      else Pair.map_snd (Formula.conjuncts_of >> FormulaSimplifier.minimize tenv))
  |> lift2 (fun _ -> Qelim.propagate bvs)
  |> elim_int_vars_quick (fun x -> List.mem x bvs || Idnt.is_coeff x)
  |> Pair.map_fst (List.map Pva.simplify >> List.unique)
let elim_int_vars ?(tenv=[]) =
  Logger.log_block2 "QelimBody.elim_int_vars"
    ~before:(fun _ -> snd >> Logger.printf "input:@,  %a@," Formula.pr)
    ~after:(snd >> Logger.printf "output:@,  %a" Formula.pr)
    (elim_int_vars tenv)


(** @ensure [vs] are not eliminated *)
let eqelim_term_bds vs =
  List.map
    (fun bd ->
       if PvaCube.atoms_of_body bd = [] then
         try
           let phi = bd |> PvaCube.terms_of_body |> Formula.band in
           let tenv =
             SimTypJudge.env_of (Formula.term_of phi) Type.mk_bool
             |> TypEnv.filter_ty Type.mk_int
             |> flip Set_.diff vs
             |> List.unique
             |> List.map (flip Pair.make Type.mk_int)
           in
           (* phi may contain unit or booleans *)
           phi
           |> Formula.exists tenv
           |> Qelim.integer_qelim_dyn
           |> Formula.conjuncts_of
           |> PvaCube.body_of_terms
         with _(*Global.NotImplemented _*) -> bd
       else bd)
let eqelim_term_bds vs bd =
  Logger.log_block2 "QelimBody.eqelim_term_bds" eqelim_term_bds vs bd


(** @param [vs] variables that must not be eliminated *)
let elim_light vs =
  lift (Formula.to_rename_tsub FormulaSimplifier.simplify vs)
  >> lift (Formula.to_const_tsub vs)
  >> Pair.map_snd
    ((*FormulaSimplifier.reduce_same_decl >>*)FormulaSimplifier.simplify)
  >> lift3 Formula.to_simple_ttsub


(** @param [vs] variables that must not be eliminated *)
let elim_full tenv vs =
  elim_int_vars ~tenv vs
  >> (PvaCube.simplify_psym
        FormulaSimplifier.simplify eqelim_term_bds ~tenv vs)
