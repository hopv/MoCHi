
(** Encoding for lists *)

val trans : Problem.t -> Problem.t * ((Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t)
val trans_typ : Syntax.typ -> Syntax.typ
