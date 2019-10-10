open Util
open Combinator
open Term

(** Linear relations with real coefficients *)

include LinRel.Make(Coeff.CoeffReal)

(** {6 Auxiliary constructors} *)

(* val of_formula : Formula.t -> t *)
let of_formula = Formula.term_of >> fun_args >> function
  | Const(c), [t1; t2] when (* Const.is_ibrel c *) Const.is_brel c ->
    c, RealTerm.sub t1 t2 |> CunTerm.to_lin_real_exp
  | _ -> invalid_arg "LinRealRel.of_formula"

let of_literal = Literal.formula_of >> of_formula

(** {6 Inspectors} *)

let is_linear phi =
  try ignore (of_formula phi); true with Invalid_argument _ -> false

(* @todo move to LinRel *)
(** @ensure the result does not contain Const.Neg, Const.Sub,
            and negative float constants *)
(* val formula_of : t -> Formula.t *)
let formula_of (c, (nxs, n)) =
  if c = Const.BinTrue Type.mk_real then Formula.mk_true
  else if c = Const.BinFalse Type.mk_real then Formula.mk_false
  else begin
    (*Logger.debug_assert
      ~on_failure:(fun () ->
          Format.printf
            "%a of the type %a is not an integer relation@,"
            pr (c, (nxs, n))
            Type.pr (Const.type_of c))
      (fun () -> Const.is_ibrel c);*)
    if nxs = [] then
      if Const.lift_brel c n 0.0 then Formula.mk_true else Formula.mk_false
    else
      let nxs1, nxs2 =
        List.partition
          (fun (n, _) ->
             Logger.debug_assert (fun () -> n <> 0.0)
               ~on_failure:(fun () -> Format.printf "%a@," pr (c, (nxs, n)));
             n > 0.0)
          nxs
      in
      let n1, n2 =
        if n > 0.0 then n, 0.0 else if n < 0.0 then 0.0, n else 0.0, 0.0
      in
      let tp = RealTerm.of_lin_exp (nxs1, n1) in
      let tm = RealTerm.of_lin_exp (LinRealExp.neg (nxs2, n2)) in
      Formula.of_term (mk_app (mk_const c) [tp; tm])
  end

(*
let formula_of (c, nxs, n) =
  match c with
    Const.Eq(intty) ->
      eq (RealTerm.of_lin_exp (nxs, n)) (RealTerm.zero)
  | Const.Neq(intty) ->
      neq (RealTerm.of_lin_exp (nxs, n)) (RealTerm.zero)
  | Const.Lt(intty) ->
      lt (RealTerm.of_lin_exp (nxs, n)) (RealTerm.zero)
  | Const.Gt(intty) ->
      gt (RealTerm.of_lin_exp (nxs, n)) (RealTerm.zero)
  | Const.Leq(intty) ->
      leq (RealTerm.of_lin_exp (nxs, n)) (RealTerm.zero)
  | Const.Geq(intty) ->
      geq (RealTerm.of_lin_exp (nxs, n)) (RealTerm.zero)
*)

(** @ensure simplify_cube is idenmpotent
    @todo check whether the function in fact satisfies the above spec. *)
(* val simplify_cube : t list -> t list *)
let simplify_cube =
  List.classify
    (fun (_, (nxs1, n1)) (_, (nxs2, n2)) ->
       LinRealExp.equiv (nxs1, 0.0) (nxs2, 0.0) ||
       LinRealExp.equiv (nxs1, 0.0) (LinRealExp.neg (nxs2, 0.0)))
  >> List.concat_map
    (fun ((c1, (nxs1, n1)) :: las) ->
       (c1, -.n1) ::
       List.map
         (fun (c2, (nxs2, n2)) ->
            if LinRealExp.equiv (nxs1, 0.0) (nxs2, 0.0) then c2, -.n2
            else Const.neg c2, n2)
         las
       |> List.map (fun (c, n) -> c, (nxs1, -.n)))

(** @ensure simplify_clause is idempotent
    @todo check whether the function in fact satisfies the above spec. *)
(* val simplify_clause : t list -> t list *)
let simplify_clause =
  List.classify
    (fun (_, (nxs1, n1)) (_, (nxs2, n2)) ->
       LinRealExp.equiv (nxs1, 0.0) (nxs2, 0.0) ||
       LinRealExp.equiv (nxs1, 0.0) (LinRealExp.neg (nxs2, 0.0)))
  >> List.concat_map
    (fun ((c1, (nxs1, n1)) :: las) ->
       (c1, -.n1) ::
       List.map
         (fun (c2, (nxs2, n2)) ->
            if LinRealExp.equiv (nxs1, 0.0) (nxs2, 0.0) then
              c2, -.n2
            else
              Const.neg c2, n2)
         las
       |> List.map (fun (c, n) -> c, (nxs1, -.n)))

let simplify_formula = of_formula >> formula_of

let lin_rat_rel_of (c, (nxs, n)) =
  (c, (List.map (Pair.map_fst Float.rat_of_float) nxs, Float.rat_of_float n))
