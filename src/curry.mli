val remove_pair : ?check:bool -> Problem.t -> Problem.t * ((Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t)
val remove_pair_direct : Syntax.term -> Syntax.term * ((Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t)
