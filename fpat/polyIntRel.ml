open Util
open Combinator
open Term

(** Polynomial relations with integer coefficients *)

type t = Const.t * PolyIntExp.t

let pr ppf (c, pol) =
  Format.fprintf ppf "%a %s 0 " PolyIntExp.pr pol (Const.string_of_infix c)

let make c pol = c, pol

let of_formula = Formula.term_of >> fun_args >> function
  | Const(c), [t1; t2] when Const.is_ibrel c ->
    c, PolyIntExp.div_gcd (CunTerm.to_poly_int_exp (IntTerm.sub t1 t2))
  | _ -> invalid_arg "PolyIntRel.of_formula"
let of_formula = Logger.log_block1 "PolyIntRel.of_formula" of_formula

let formula_of (c, pol) =
  match pol with
  | [(n, [])] ->
    if Const.lift_brel c n 0 then Formula.mk_true else Formula.mk_false
  | _ ->
    let pol1, pol2 =
      List.partition
        (fun (n, _) -> Logger.debug_assert (fun () -> n <> 0); n > 0)
        pol
    in
    let tp = IntTerm.of_poly_exp pol1 in
    let tm = IntTerm.of_poly_exp (PolyIntExp.neg pol2) in
    Formula.of_term (mk_app (mk_const c) [tp; tm])
let formula_of = Logger.log_block1 "PolyIntRel.formula_of" formula_of

let simplify_formula phi =
  try phi |> of_formula |> formula_of with Invalid_argument _ -> phi
(*
    Logger.debug_assert_false
      ~on_failure:(fun () ->
          Format.printf
            "error in PolyIntRel.simplify_formula: %a@,"
            Formula.pr phi)*)
