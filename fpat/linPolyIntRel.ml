open Util
open Combinator
open Term

(** Linear relations with integer polynomial coefficients *)

include LinRel.Make(LinPolyIntExp.Coeff)

let of_formula = fun_args >> function
  | Const(c), [t1; t2] when Const.is_ibrel c ->
    c,
    IntTerm.sub t1 t2
    |> CunTerm.lin_poly_exp_of
    |> LinPolyIntExp.factorize
    |> snd
  | _ ->
    (*Format.printf "%a@," Term.pr t;*)
    invalid_arg "LinPolyIntRel.of_formula"

(* @todo move to LinRel *)
let formula_of (c, (nxs, n)) =
  if c = Const.BinTrue(Type.mk_int) then Const Const.True
  else if c = Const.BinFalse(Type.mk_int) then Const Const.False
  else
    begin
      Logger.debug_assert (fun () -> Const.is_ibrel c);
      if nxs = [] then
        if assert false(*Const.lift_brel c n 0*) then Const Const.True
        else Const Const.False
      else
        let nxs1, nxs2 =
          List.partition
            (fun (n, _) ->
               Logger.debug_assert
                 (fun () -> not (PolyIntExp.equiv n (PolyIntExp.of_int 0)))
                 ~on_failure:(fun () -> Format.printf "%a@," pr (c, (nxs, n)));
               PolyIntExp.(>) n (PolyIntExp.of_int 0))
            nxs
        in
        let n1, n2 =
          if PolyIntExp.(>) n (PolyIntExp.of_int 0) then
            n, PolyIntExp.of_int 0
          else if PolyIntExp.(<) n (PolyIntExp.of_int 0) then
            PolyIntExp.of_int 0, n
          else
            PolyIntExp.of_int 0, PolyIntExp.of_int 0
        in
        let tp = IntTerm.of_lin_poly_exp (nxs1, n1) in
        let tm = IntTerm.of_lin_poly_exp (LinPolyIntExp.neg (nxs2, n2)) in
        mk_app (mk_const c) [tp; tm]
    end
