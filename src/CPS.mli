(** CPS-transformation for source language *)

val trans : Problem.t -> Problem.t * ((Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t)
val trans_as_direct : Syntax.term -> Syntax.term * ((Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t)
val trans_ref_typ : Ref_type.t -> Ref_type.t
val trans_ref_typ_as_direct : Ref_type.t -> Ref_type.t
