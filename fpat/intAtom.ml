open Util
open Combinator

(** Atoms on integers *)

let simplify atm =
  atm
  |> Formula.of_atom
  |> (try_ LinIntRel.simplify_formula
        (function
          | Invalid_argument _ ->
            try_ LinTermIntRel.simplify_formula
              (function
                | Invalid_argument _ ->
                  try_ PolyIntRel.simplify_formula
                    (function
                      | Invalid_argument _ ->
                        Atom.pr Format.std_formatter atm;
                        assert false
                      | e -> raise e)
                | e -> raise e)
          | e -> raise e))
  |> Formula.atom_of

let eq t1 t2 = Atom.eq Type.mk_int t1 t2
let neq t1 t2 = Atom.neq Type.mk_int t1 t2
let gt t1 t2 = NumAtom.gt Type.mk_int t1 t2
let lt t1 t2 = NumAtom.lt Type.mk_int t1 t2
let geq t1 t2 = NumAtom.geq Type.mk_int t1 t2
let leq t1 t2 = NumAtom.leq Type.mk_int t1 t2

let eq0 t = eq t IntTerm.zero |> Formula.of_atom
let neq0 t = neq t IntTerm.zero |> Formula.of_atom
let gt0 t = gt t IntTerm.zero |> Formula.of_atom
let lt0 t = lt t IntTerm.zero |> Formula.of_atom
let geq0 t = geq t IntTerm.zero |> Formula.of_atom
let leq0 t = leq t IntTerm.zero |> Formula.of_atom

let divides n t = Atom.mk_urel (Const.Divides(n)) t

let rec linearize_linprod c ts =
  match ts with
  | [] -> assert false
  | [t] -> Formula.mk_brel c t (IntTerm.zero)
  | t :: ts ->
    (match c with
     | Const.Eq(intty) ->
       t :: ts
       |> List.map eq0
       |> Formula.bor
     | Const.Neq(intty) ->
       t :: ts
       |> List.map neq0
       |> Formula.band
     | Const.Lt(intty)
     | Const.Gt(intty) ->
       [Formula.band [gt0 t; linearize_linprod c ts];
        Formula.band [lt0 t; linearize_linprod (Const.neg c) ts]]
       |> Formula.bor
     | Const.Leq(intty)
     | Const.Geq(intty) ->
       [Formula.band [geq0 t; linearize_linprod c ts];
        Formula.band [leq0 t; linearize_linprod (Const.neg c) ts]]
       |> Formula.bor
     | _ -> assert false)

let linearize =
  Formula.of_atom
  >> if_ LinIntRel.is_linear
    id
    (if_ LinTermIntRel.is_linear
       (fun phi ->
          let c, la = LinTermIntRel.of_formula phi in
          let ts =
            if LinTermIntExp.is_zero la then [IntTerm.zero]
            else LinTermIntExp.factorize2 la
          in
          if List.for_all (Formula.of_term >> LinIntRel.is_linear) ts then
            (*mk_app (mk_const c) (prod ts) (IntTerm.zero)*)
            linearize_linprod c ts
          else invalid_arg "IntAtom.linearize")
       (fun phi ->
          let c, pol = PolyIntRel.of_formula phi in
          let ts =
            if PolyIntExp.is_zero pol then [IntTerm.zero]
            else IntTerm.factorize pol
          in
          if List.for_all (Formula.of_term >> LinIntRel.is_linear) ts then
            (*mk_app (mk_const c) (prod ts) (IntTerm.zero)*)
            linearize_linprod c ts
          else
            invalid_arg "IntAtom.linearize"))
