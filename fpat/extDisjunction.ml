open Util
open Combinator

(** Integer/Real/Bool disjunctions *)

(*
let elim_subsumed_disjuncts phis =
  phis
  |> List.map (Formula.conjuncts_of)
  |> List.filter_maplac
    (fun phiss1 phis phiss2 ->
       if List.exists
           (fun phis' -> Set_.subset phis' phis)
           (phiss1 @ phiss2) then
         None
       else Some(phis))
  |> List.map Formula.band
*)

let factor_out_conjuncts simplify_formula simplify_disjuncts phis =
  if List.length phis <= 1 then phis
  else
    let phiss = List.map Formula.conjuncts_of phis in
    let shared = List.fold_left Set_.inter (List.hd phiss) (List.tl phiss) in
    if shared <> [] then begin
      Logger.printf "shared: %a@," (List.pr Formula.pr ", ") shared;
      let phi' =
        phiss
        |> List.map (flip Set_.diff shared >> Formula.band >> simplify_formula)
        |> simplify_disjuncts simplify_formula
        |> Formula.bor
      in
      [Formula.band [simplify_formula (Formula.band shared); phi']]
    end else phis
let factor_out_conjuncts =
  Logger.log_block3 "ExtDisjunction.factor_out_conjuncts"
    ~before:(fun _ _ -> Formula.bor >> Logger.printf "inxput: %a@," Formula.pr)
    ~after:(Formula.bor >> Logger.printf "output: %a" Formula.pr)
    factor_out_conjuncts

(** @require [idempotent simplify_formula] *)
let rec simplify simplify_formula phis =
  phis
  |> Disjunction.simplify
  |> List.map Literal.of_formula
  |> BoolClause.simplify
  |> IntClause.simplify
  |> List.map Literal.formula_of
  |> Disjunction.simplify
  |> factor_out_conjuncts simplify_formula simplify
let simplify =
  Logger.log_block2 "ExtDisjunction.simplify"
    ~before:(fun _ -> Formula.bor >> Logger.printf "input: %a@," Formula.pr)
    ~after:(Formula.bor >> Logger.printf "output: %a" Formula.pr)
    simplify
