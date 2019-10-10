open Util
open Combinator
open Term

(** linear relations with integer term coefficients *)

include LinRel.Make(LinTermIntExp.Coeff)

(** {6 Auxiliary constructors} *)

(* val of_formula : Formula.t -> t *)
let of_formula phi =
  match phi |> Formula.term_of |> fun_args with
  | Const(c), [t1; t2] when Const.is_brel c(*@todo[Const.is_ibrel c] rejects the equality with a polymorphic type*) ->
    c, IntTerm.sub t1 t2 |> LinTermIntExp.of_term
  | _ ->
    Logger.printf "LinTermIntRel.of_formula: %a@," Formula.pr phi;
    invalid_arg "LinTermIntRel.of_formula"
let of_formula = Logger.log_block1 "LinTermIntRel.of_formula" of_formula
let of_literal = Literal.formula_of >> of_formula

(** @require c is not <>
    @ensure the result only uses geq and eq *)
(* val normalize : t -> t *)
let normalize (c, (nxs, n)) =
  match c with
  | Const.Eq(ty) (*@todo [when Type.is_int ty] rejects the equality with a polymorphic type*) ->
    c, (nxs, n)
  | Const.Neq(ty) (*@todo [when Type.is_int ty] rejects the equality with a polymorphic type*) ->
    assert false
  | Const.Lt(ty) (*@todo [when Type.is_int ty] rejects the equality with a polymorphic type*) ->
    Logger.printf0 "elim_lt!!@,";
    Const.Geq(Type.mk_int),
    LinTermIntExp.neg (nxs, IntTerm.add n (IntTerm.one))
  | Const.Gt(ty) (*@todo [when Type.is_int ty] rejects the equality with a polymorphic type*) ->
    Logger.printf0 "elim_gt!!@,";
    Const.Geq(Type.mk_int),
    (nxs, CunTerm.poly_simplify (IntTerm.sub n (IntTerm.one)))
  | Const.Leq(ty) (*@todo [when Type.is_int ty] rejects the equality with a polymorphic type*) ->
    Const.Geq(Type.mk_int),
    LinTermIntExp.neg (nxs, n)
  | Const.Geq(ty) (*@todo [when Type.is_int ty] rejects the equality with a polymorphic type*) ->
    c, (nxs, n)
  | _ -> Format.printf "Uncaught const: %s@," (Const.string_of c); assert false
let normalize = Logger.log_block1 "LinTermIntRel.normalize" normalize

(** {6 Inspectors} *)

let is_linear phi =
  try ignore (of_formula phi); true with Invalid_argument _ -> false

(* @todo move to LinRel *)
(** @ensure the result does not contain Const.Neg, Const.Sub,
            and negative integer constants *)
(* val formula_of : t -> Formula.t *)
let formula_of (c, (nxs, n)) =
  if nxs = [] && IntTerm.is_const n then
    if Const.lift_brel c (IntTerm.int_of n) 0 then Formula.mk_true
    else Formula.mk_false
  else
    let nxs =
      List.filter_map
        (fun (n, x) ->
           if IntTerm.equiv n (IntTerm.zero) then None else Some(n, x))
        nxs
    in
    let nxs1, nxs2 =
      List.partition
        (fun (n, _) -> not (IntTerm.is_const n) || IntTerm.(>) n IntTerm.zero)
        nxs
    in
    let n1, n2 =
      if not (IntTerm.is_const n) || IntTerm.(>) n IntTerm.zero then
        n, IntTerm.zero
      else if IntTerm.(<) n IntTerm.zero then
        IntTerm.zero, n
      else
        IntTerm.zero, IntTerm.zero in
    let tp = LinTermIntExp.term_of (nxs1, n1) in
    let tm = LinTermIntExp.term_of (LinTermIntExp.neg (nxs2, n2)) in
    Formula.of_term (mk_app (mk_const c) [tp; tm])

let simplify_formula = of_formula >> formula_of

(** @ensure pred res *)
(* val elem_of : (elem -> bool) -> LinTermIntRel.t -> elem *)
let elem_of pred (c, (nxs, n)) =
  if c = Const.Eq(Type.mk_int) then
    List.find_maplr
      (fun nxs1 (n', x) nxs2 ->
         if IntTerm.equiv n' IntTerm.one ||
            IntTerm.equiv n' (IntTerm.make (-1)) then
           let t =
             if IntTerm.equiv n' IntTerm.one then
               LinTermIntExp.term_of (LinTermIntExp.neg (nxs1 @ nxs2, n))
             else if IntTerm.equiv n' (IntTerm.make (-1)) then
               LinTermIntExp.term_of (nxs1 @ nxs2, n)
             else
               assert false
           in
           let ty = Type.mk_int in
           if pred (x, (t, ty)) then Some(x, (t, ty)) else None
         else None)
      nxs
  else raise Not_found


let tttrue = Formula.term_of Formula.mk_true, Type.mk_bool
let ttfalse = Formula.term_of Formula.mk_false, Type.mk_bool
(** @ensure if [r] is returned, [pred r] holds *)
(* val elem_of_formula : (TypTermSubst.elem -> bool) -> Formula.t -> TypTermSubst.elem *)
let elem_of_formula pred phi =
  try
    phi |> of_formula |> elem_of pred
  with
  | Invalid_argument _ ->
    match phi |> Formula.term_of |> Term.fun_args with
    | Const(Const.Eq(ty)), [Var(x); t] when pred (x, (t, ty)) -> x, (t, ty)
    | Const(Const.Eq(ty)), [t; Var(x)] when pred (x, (t, ty)) -> x, (t, ty)
    | Var(x), [] when pred (x, tttrue) ->
      x, (Formula.term_of Formula.mk_true, Type.mk_bool)
    | Const(Const.Not), [Var(x)] when pred (x, ttfalse) ->
      x, (Formula.term_of Formula.mk_false, Type.mk_bool)
    | _ -> raise Not_found

(** possibly return a substitution of the form
    {x -> y, y -> z}
    @param pred do not require that
           mem x (fvs t) implies not (pred (x, (t, ty)))
    @todo is this also sound for non-linear expressions?
    @ensure if [(ttsub, phis)] is retuned
            not (cyclic ttsub) &&
            List.for_all pred ttsub *)
(* val of_formulas :
   (TypTermSubst.elem -> bool) -> Formula.t list -> t * Formula.t *)
let of_formulas pred =
  List.fold_left
    (fun (ttsub0, phis0) phi ->
       try
         let xtty =
           let pred =
             let dom = TypTermSubst.dom ttsub0 in
             fun (x, (t, ty)) ->
               pred (x, (t, ty)) &&
               (* @todo check whether substitution is acyclic instead *)
               Set_.inter (x :: dom) (Term.fvs t) = []
           in
           phi
           |> elem_of_formula pred
           |> Logger.pprintf "xtty: %a@," TypTermSubst.pr_elem
         in
         xtty :: ttsub0, phis0
       with Not_found ->
         ttsub0, phi :: phis0)
    ([], [])
  >> Pair.map_fst Formula.resolve_duplicates_in_ttsub
  >> fun ((ttsub, phis0), phis1) -> ttsub, phis0 @ phis1 |> Formula.band
let of_formulas = Logger.log_block2 "LinTermIntRel.of_formulas" of_formulas
