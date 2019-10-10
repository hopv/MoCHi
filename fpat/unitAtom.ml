open Util
open Combinator

(** Atoms on unit *)

let simplify c t1 t2 =
  let t1 = UnitTerm.simplify t1 in
  let t2 = UnitTerm.simplify t2 in
  if Const.is_eq c then Atom.mk_true
  else if Const.is_neq c then Atom.mk_false
  else assert false
