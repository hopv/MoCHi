open Util
open Combinator

(** Abstraction types *)

let split_equalities = ref false
let extract_atomic_predicates = ref false

type t =
  | Base of TypConst.t * Idnt.t * Formula.t list
  | Fun of t * t

let is_base = function
  | Base(_, _, _) -> true
  | Fun(_, _) -> false

let mk_base c x ps = Base(c, x, ps)
let mk_fun aty1 ary2 = Fun(aty1, ary2)

let rec pr ppf aty =
  match aty with
  | Base(c, x, ts) ->
    begin
      match ts with
      | [] ->
        String.pr ppf (TypConst.string_of c)
      | _ ->
        let pr_aux ppf t =
          Format.fprintf ppf "%a -> %a" Idnt.pr x Formula.pr t
        in
        Format.fprintf ppf
          "%s[@[<hov>%a@]]"
          (TypConst.string_of c)
          (List.pr pr_aux ",@,") ts
    end
  | Fun(aty1, aty2) ->
    Format.fprintf ppf "@[<hov>";
    (if is_base aty1 then
       Format.fprintf ppf "%a:" Idnt.pr (bv_of aty1));
    (if is_base aty1 then
       Format.fprintf ppf "%a" pr aty1 else Format.fprintf ppf "(%a)" pr aty1);
    Format.fprintf ppf "@ ->@ %a@]" pr aty2
and bv_of aty =
  match aty with
  | Base(_, bv, _) -> bv
  | Fun(_, _) ->
    Format.printf "%a@," pr aty;
    assert false

let pr_bind ppf (f, sty) =
  Format.fprintf ppf "%a: %a" Idnt.pr f pr sty
let pr_env ppf env =
  Format.fprintf ppf "%a" (List.pr pr_bind "@ ") env

let rec subst xts aty =
  match aty with
  | Base(c, x, ts) ->
    mk_base c x (List.map (Formula.subst (Map_.diff xts [x])) ts)
  | Fun(aty1, aty2) ->
    let xts' = if is_base aty1 then Map_.diff xts [bv_of aty1] else xts in
    mk_fun (subst xts aty1) (subst xts' aty2)

let rec merge2 aty1 aty2 =
  match aty1, aty2 with
  | Base(c1, x1, ts1), Base(c2, x2, ts2) ->
    assert (c1 = c2);
    let x = Idnt.new_var () in
    mk_base c1 x
      (List.map (Formula.rename [x1, x]) ts1
       @ List.map (Formula.rename [x2, x]) ts2
       |> List.unique)
  | Fun(aty11, aty12), Fun(aty21, aty22) ->
    let aty1 = merge2 aty11 aty21 in
    let xts1 =
      if is_base aty11 then [bv_of aty11, Term.mk_var (bv_of aty1)] else []
    in
    let xts2 =
      if is_base aty21 then [bv_of aty21, Term.mk_var (bv_of aty1)] else []
    in
    mk_fun aty1 (merge2 (subst xts1 aty12) (subst xts2 aty22))
  | _ -> assert false

let merge = function
  | [] -> assert false
  | aty :: atys -> List.fold_left merge2 aty atys

let rec of_refinement_type = function
  | RefType.Base(x, c, phi) ->
    mk_base c x
      (let phi =
         if !split_equalities
         then Formula.map_atom CunAtom.elim_eq_neq phi
         else phi
       in
       if !extract_atomic_predicates then
         phi
         |> Formula.atoms
         |> (* @todo should not contain mk_true and mk_false *)
         List.map Formula.of_atom
       else if Formula.is_true phi || Formula.is_false phi then []
       else [phi])
  | RefType.Fun(xs) ->
    assert (xs <> []);
    xs
    |> List.map (Pair.lift of_refinement_type >> uncurry2 mk_fun)
    |> merge
  | _ -> assert false
