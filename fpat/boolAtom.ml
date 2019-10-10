open Util
open Combinator

(** Atoms on booleans *)

include Atom

let simplify_formula = id
let simplify c t1 t2 =
  let phi1 = t1 |> Formula.of_term |> simplify_formula in
  let phi2 = t2 |> Formula.of_term |> simplify_formula in
  match c with
  | Const.Eq(ty) when Type.is_bool ty ->
    if Formula.equiv phi1 phi2 then Atom.mk_true
    else if Formula.is_true phi1 then phi2 |> Formula.atom_of
    else if Formula.is_false phi1 then
      phi2 |> Formula.bnot |> simplify_formula |> Formula.atom_of
    else if Formula.is_true phi2 then phi1 |> Formula.atom_of
    else if Formula.is_false phi2 then
      phi1 |> Formula.bnot |> simplify_formula |> Formula.atom_of
    else eq Type.mk_bool (Formula.term_of phi1) (Formula.term_of phi2)
  | Const.Neq(ty) when Type.is_bool ty ->
    if Formula.equiv phi1 phi2 then Atom.mk_false
    else if Formula.is_true phi1 then
      (*eq Type.Bool phi2 Formula.mk_false*)
      phi2 |>  Formula.bnot |> simplify_formula |> Formula.atom_of
    else if Formula.is_false phi1 then
      (*eq Type.Bool phi2 Formula.mk_true*)
      phi2 |> Formula.atom_of
    else if Formula.is_true phi2 then
      (*eq Type.Bool phi1 Formula.mk_false*)
      phi1 |> Formula.bnot |> simplify_formula |> Formula.atom_of
    else if Formula.is_false phi2 then
      (*eq Type.Bool phi1 mk_true*)
      phi1 |> Formula.atom_of
    else neq Type.mk_bool (Formula.term_of phi1) (Formula.term_of phi2)
  | _ -> Atom.make c [t1; t2]
