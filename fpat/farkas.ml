open Util
open Combinator
open Term

(** Formula translation based on Farkas lemma *)

(** @todo Should we compute minimal unsat core before farkas?  It
          seems difficult to do so if constraints are non-linear *)

let lin_term_int_rel_of lit =
  try lit |> LinTermIntRel.of_literal |> LinTermIntRel.normalize
  with
  | Invalid_argument _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () ->
          Format.printf "Farkas.farkas_cube: %a@." Literal.pr lit)
      ()
  | e -> Format.printf "%s@." (Printexc.to_string e);
    assert false

(** @require [cube] has no Eq atom if [pos = true] *)
let farkas_cube pos linear (*coeffs*) cube =
  if cube = [] then Formula.mk_false
  else if cube |> Cube.formula_of |> Formula.fvs |> (=) [] then
    cube |> Cube.formula_of |> Formula.bnot
  else
    let lits =
      cube
      |> List.map lin_term_int_rel_of
      |> (@) (if true then [] else [LinTermIntRel.make
                                      (Const.Geq Type.mk_int)
                                      (LinTermIntExp.of_int 1)])
      |> (Logger.pprintf
            "unsatisfiable constraints:@,  %a@," LinTermIntRel.pr_list)
    in
    let coeffs =
      let vars =
        lits
        |> List.concat_map LinTermIntRel.fvs
        |> List.unique
        |> Logger.pprintf "variables to be eliminated: %a@," Idnt.pr_list
      in
      lits |> List.map (LinTermIntRel.coeffs_of vars)
    in
    let lambdas =
      coeffs
      |> (List.map
            (fun (cs, _) ->
               (* fix lambdas to 1 to avoid nonlinear constraint
                  @note if List.concat_map Term.coeffs cs = [] then
                  multiplication by lambda never causes a nonlinear
                  formula *)
               if linear &&
                  List.concat_map Term.coeffs cs <> [] (* @todo *)
               then IntTerm.one
               else Term.new_var ()))
    in
    coeffs
    |> List.unzip
    |> Pair.map
      (List.map2 (IntTerm.mul >> List.map) lambdas
       >> Matrix.transpose
       >> (function
           | cs :: css ->
             IntFormula.lt (IntTerm.sum cs) IntTerm.zero
             :: List.map (IntTerm.sum >> flip IntFormula.eq IntTerm.zero) css
           | _ -> assert false))
      (List.map2
         (fun l c ->
            if pos then None
            else
              (*@note adding [when Type.is_int ty] rejects the
                equality with a polymorphic type*)
              match c with
              | Const.Eq(ty) -> None
              | Const.Geq(ty) -> Some(IntFormula.geq l IntTerm.zero)
              | _ -> assert false)
         lambdas
       >> List.concat_opt
       >> Logger.pprintf "constraints on new variables: %a@," Formula.pr_list)
    |> uncurry2 (@)
    |> Formula.band
    |> FormulaSimplifier.simplify
let farkas_cube = Logger.log_block3 "Farkas.farkas_cube" farkas_cube

let farkas_int pos linear =
  let_ (Formula.coeffs >> List.unique) (fun coeffs ->
      Formula.map_atom (if pos then CunAtom.elim_eq_neq else CunAtom.elim_neq)
      >> Formula.elim_imply_iff >> DNF.of_formula >> DNF.cubes_of
      >> List.map (farkas_cube pos linear (*coeffs*))
      >> Formula.band)
let farkas_int = Logger.log_block3 "Farkas.farkas_int" farkas_int

(** [farkas pos linear phi] returns a constraint [psi] over
    coefficients [cs] and fresh variables [ls], where [phi] is a
    formula with coefficients [cs] and variables [xs]

    @ensure [exists cs. forall xs. phi => bot] iff [exists cs, ls. psi]
    (for reals)

    @ensure if [pos = true], [ls] are non-negative but [cs] remains
    to be of the int type *)
let farkas pos linear =
  CunFormula.lift_int FormulaSimplifier.simplify (farkas_int pos linear)
let farkas ?(pos = false) ?(linear = false) =
  Logger.log_block1 "Farkas.farkas"
    ~before:(Logger.printf "input: %a@," Formula.pr)
    ~after:(Logger.printf "output: %a" Formula.pr)
    (farkas pos linear)
