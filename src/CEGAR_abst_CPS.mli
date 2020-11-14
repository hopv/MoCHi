
val beta_reduce_term : CEGAR_syntax.t -> CEGAR_syntax.t
val eta_reduce_term : CEGAR_syntax.t -> CEGAR_syntax.t
val abstract : ?preprocessed:CEGAR_syntax.prog -> CEGAR_syntax.prog -> CEGAR_syntax.var list * CEGAR_syntax.prog * CEGAR_syntax.prog
