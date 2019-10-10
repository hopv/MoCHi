open Util
open Combinator
open InterpProver

(** An interpolating prover combinator for extending a given prover to
    support unit and booleans *)

let sub_of_ps_ns ps ns =
  List.map (flip Pair.make (Formula.term_of Formula.mk_true)) ps
  @ List.map (flip Pair.make (Formula.term_of Formula.mk_false)) ns

let phis_of_ps_ns ps ns =
  List.map (Term.mk_var >> Formula.of_term) ps
  @ List.map (Term.mk_var >> Formula.of_term >> Formula.bnot) ns

let interpolate ip phi1 phi2 =
  let bs =
    Set_.inter (Formula.fvs_bool phi1) (Formula.fvs_bool phi2)
    |> List.unique
  in
  (phi1, phi2)
  |> Pair.lift
    (CunFormula.elim_unit
     >> (fun phi -> Qelim.elim_bool_vars (Set_.diff (Formula.fvs_bool phi) bs) phi)
     >> Formula.conjuncts_of
     >> List.map Formula.term_of
     >> List.partition3_map
       (function
         | Term.Var(b) -> `L(b)
         | Term.App(Term.Const(Const.Not), Term.Var(b)) -> `C(b)
         | t -> `R(Formula.of_term t)))
  |> (fun ((ps1, ns1, phis1), (ps2, ns2, phis2)) ->
      if Set_.intersects ps1 ns1 then Formula.mk_false
      else if Set_.intersects ps2 ns2 then Formula.mk_true
      else
        let ps = Set_.inter ps1 ps2 in
        let ns = Set_.inter ns1 ns2 in
        let ps1 = Set_.diff ps1 ps in
        let ns1 = Set_.diff ns1 ns in
        let ps2 = Set_.diff ps2 ps in
        let ns2 = Set_.diff ns2 ns in
        let phis = Set_.inter phis1 phis2 in
        (phis1, phis2)
        (**)|> Pair.lift (flip Set_.diff phis)(**)
        (*phis1 |> Formula.band |> Formula.subst (sub_of_ps_ns ps ns)*)
        (*phis2 |> Formula.band |> Formula.subst (sub_of_ps_ns ps ns)*)
        |> Pair.map
          Formula.band
          (flip (@) (phis_of_ps_ns ps2 ns2)
           >> Formula.band
           >> Formula.subst (sub_of_ps_ns ps1 ns1)
           >> FormulaSimplifier.simplify)
        |> Pair.list_of
        |> CunFormula.case_analysis_boolean FormulaSimplifier.simplify
          (Pair.of_list >> Pair.fold ip)
        |> flip List.cons (phis_of_ps_ns ps1 ns1)
        |> Formula.band)
let interpolate =
  Logger.log_block3 "UnitBoolInterpProver.interpolate" interpolate
