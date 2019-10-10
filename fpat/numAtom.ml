open Util
open Combinator

(** Atoms on numbers *)

(*
val lt : ?ty:Type.t -> Term.t -> Term.t -> Atom.t
val gt : ?ty:Type.t -> Term.t -> Term.t -> Atom.t
val leq : ?ty:Type.t -> Term.t -> Term.t -> Atom.t
val geq : ?ty:Type.t -> Term.t -> Term.t -> Atom.t
val within : ?ty:Type.t -> Term.t -> Term.t -> Term.t -> Atom.t
*)

let lt ty t1 t2 = Atom.mk_brel (Const.Lt ty) t1 t2
let gt ty t1 t2 = Atom.mk_brel (Const.Gt ty) t1 t2
(*let gt ?(ty = Type.mk_int) t1 t2 = Atom.mk_brel (Const.Lt ty) t2 t1*)
let leq ty t1 t2 = Atom.mk_brel (Const.Leq ty) t1 t2
(*let leq ?(ty = Type.mk_int) t1 t2 =
  Term.mk_app (Term.mk_const Const.Or) [lt ty t1 t2; Atom.eq ty t1 t2]*)
let geq ty t1 t2 = Atom.mk_brel (Const.Geq ty) t1 t2
(*let geq ?(ty = Type.mk_int) t1 t2 =
  Term.mk_app (Term.mk_const Const.Or) [gt ty t1 t2; Atom.eq ty t1 t2]*)

let within ty l t h =
  Formula.band [leq ty l t |> Formula.of_atom; leq ty t h |> Formula.of_atom]
