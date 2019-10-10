(** Number term expressions *)

val mk_uop : Const.t -> Term.t -> Term.t
val mk_bop : Const.t -> Term.t -> Term.t -> Term.t
val neg : Type.t -> Term.t -> Term.t
val add : Type.t -> Term.t -> Term.t -> Term.t
val sub : Type.t -> Term.t -> Term.t -> Term.t
val mul : Type.t -> Term.t -> Term.t -> Term.t
val div : Type.t -> Term.t -> Term.t -> Term.t
val max : Type.t -> Term.t -> Term.t -> Term.t
val min : Type.t -> Term.t -> Term.t -> Term.t
val mod_ : Type.t -> Term.t -> Term.t -> Term.t
