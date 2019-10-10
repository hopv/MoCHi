open Util
open Combinator

(** Integer/Real/Bool conjunctions *)

let factor_out_disjuncts simplify_formula simplify_conjuncts phis =
  if List.length phis <= 1 then phis
  else
    let phiss = List.map Formula.disjuncts_of phis in
    let shared = List.fold_left Set_.inter (List.hd phiss) (List.tl phiss) in
    if shared <> [] then begin
      Logger.printf "shared: %a@," (List.pr Formula.pr ", ") shared;
      let phi' =
        phiss
        |> List.map (flip Set_.diff shared >> Formula.bor >> simplify_formula)
        |> simplify_conjuncts simplify_formula
        |> Formula.band
      in
      [Formula.bor [simplify_formula (Formula.bor shared); phi']]
    end else phis
(** @param t a formula
    @require t does not contain Const.Imply and Const.Iff
    @ensure the return value does not contain a subexpression of the type unit
    @todo ensure that for any t, simplify_formula (simplify_formula t) = simplify_formula t *)
let factor_out_disjuncts =
  Logger.log_block3 "ExtConjunction.factor_out_disjuncts"
    ~before:(fun _ _ -> Formula.band >> Logger.printf "input: %a@," Formula.pr)
    ~after:(Formula.band >> Logger.printf "output: %a" Formula.pr)
    factor_out_disjuncts

(** @require List.for_all (fun t -> simplify_formula t = t) ts *)
let rec simplify simplify_formula phis =
  phis
  |> Conjunction.simplify
  |> List.map Literal.of_formula
  |> BoolCube.simplify
  |> IntCube.simplify simplify_formula
  |> List.map Literal.formula_of
  |> Conjunction.simplify
  |> factor_out_disjuncts simplify_formula simplify
let simplify =
  Logger.log_block2 "ExtConjunction.simplify"
    ~before:(fun _ -> Formula.band >> Logger.printf "input: %a@," Formula.pr)
    ~after:(Formula.band >> Logger.printf "output: %a" Formula.pr)
    simplify
