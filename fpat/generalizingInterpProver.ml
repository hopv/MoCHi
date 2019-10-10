open Util
open Combinator
open InterpProver

(** An interpolating prover combinator for extending a given prover to
    use a syntactic predicate generalization heuristics

    @todo why verification of file.ml becomes too slow? *)

(* val gen_pivot : Idnt.t ref *)
let gen_pivot = ref (Idnt.make "")

let interpolate (ip : InterpProver.t) phi1 phi2 =
  if SMTProver.is_valid_dyn (Formula.bnot phi1) then Formula.mk_false(**@todo*)
  else
    let xns, phis1 =
      phi1
      |> Formula.conjuncts_of
      |> List.partition_map
        (fun t ->
           try
             match LinIntRel.of_formula t with
             | Const.Eq(ty), ([1, x], n) when Type.is_int ty -> `L(x, -n)
             | Const.Eq(ty), ([-1, x], n) when Type.is_int ty -> `L(x, n)
             | la -> `R(LinIntRel.formula_of la)
           with Invalid_argument _ -> `R(t))
    in
    match xns with
    | [] -> ip phi1 phi2
    | _ ->
      (* find a pivot (x, n) *)
      let (x, n) :: xns =
        try
          let xns1, (x, n), xns2 =
            List.pick (fun (x, _) -> !gen_pivot = x) xns
          in
          (x, n) :: xns1 @ xns2
        with Not_found -> List.sort (fun (_, n1) (_, n2) -> n1 - n2) xns
      in
      let phis2 =
        List.map
          (fun (x', n') ->
             IntFormula.eq
               (Term.mk_var x')
               (IntTerm.add (Term.mk_var x) (IntTerm.make (n' - n))))
          xns
      in
      try
        ip (Formula.band (phis1 @ phis2)) phi2
      with
      | NoInterpolant
      | Fail
      | Unknown ->
        ip
          (IntFormula.eq (Term.mk_var x) (IntTerm.make n) :: phis1 @ phis2
           |> Formula.band)
          phi2
let interpolate =
  Logger.log_block3 "GeneralizingInterpProver.interpolate" interpolate
