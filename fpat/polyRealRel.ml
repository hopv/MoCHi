open Util
open Combinator
open Term

(** Polynomial relations with real coefficients *)

type t = Const.t * PolyRealExp.t

let pr ppf (c, pol) =
  Format.fprintf ppf "%a %s 0. " PolyRealExp.pr pol (Const.string_of_infix c)

let make c pol = c, pol

let of_formula = Formula.term_of >> fun_args >> function
  | Const(c), [t1; t2] when Const.is_rbrel c ->
    c, CunTerm.to_poly_real_exp (RealTerm.sub t1 t2)
  | _ -> invalid_arg "PolyRealRel.of_formula"
let of_formula = Logger.log_block1 "PolyRealRel.of_formula" of_formula

let formula_of (c, pol) =
  match pol with
  | [(n, [])] ->
    if Const.lift_brel c n 0. then Formula.mk_true else Formula.mk_false
  | _ ->
    let pol1, pol2 =
      List.partition
        (fun (n, _) -> Logger.debug_assert (fun () -> n <> 0.); n > 0.)
        pol
    in
    let tp = RealTerm.of_poly_exp pol1 in
    let tm = RealTerm.of_poly_exp (PolyRealExp.neg pol2) in
    Formula.of_term (mk_app (mk_const c) [tp; tm])
let formula_of = Logger.log_block1 "PolyRealRel.formula_of" formula_of

let simplify_formula phi =
  try phi |> of_formula |> formula_of with Invalid_argument _ -> phi
