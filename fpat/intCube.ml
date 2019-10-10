open Util
open Combinator
open Term

(** Cubes of integer atoms *)

include Cube

let classify = 
  List.partition_map
    (fun lit ->
       try `L(lit |> LinIntRel.of_literal) with Invalid_argument _ -> `R(lit))

(** @todo refactoring *)
let simplify_ts simplify_formula las phis =
  let xts, phis' =
    List.partition_map
      (function
        | (Const.Eq(ty), ([1, x], n)) (*when Type.is_int ty*) ->
          `L(x, IntTerm.make (-n))
        | (Const.Eq(ty), ([-1, x], n)) (*when Type.is_int ty*) ->
          `L(x, IntTerm.make n)
        | la -> `R(LinIntRel.formula_of la))
      las
  in
  let phis_ret = phis' @ phis in
  if xts = [] then phis_ret
  else
    List.map (fun (x, t) -> IntFormula.eq (Term.mk_var x) t) xts
    @ List.map
      (fun phi ->
         let phi' = simplify_formula (Formula.subst xts phi) in
         if Formula.is_true phi' || Formula.is_false phi' then phi' else phi)
      phis_ret
let simplify_ts =
  Logger.log_block3 "IntCube.simplify_ts"
    ~before:(fun _ las phis ->
        List.map LinIntRel.formula_of las @ phis
        |> Formula.band
        |> Logger.printf "input: %a@," Formula.pr)
    ~after:(Formula.band >> Logger.printf "output: %a" Formula.pr)
    simplify_ts

let simplify simplify_formula lits =
  let las, lits' = classify lits in
  let las = las |> LinIntRel.simplify_cube in
  if true
  then simplify_ts simplify_formula las (List.map Literal.formula_of lits')
       |> List.map Literal.of_formula
  else (List.map LinIntRel.literal_of las) @ lits'
