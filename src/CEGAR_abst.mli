(** Predicate abstraction *)

exception NotRefined

val abstract : CEGAR_syntax.var list -> ?preprocessed:CEGAR_syntax.prog -> CEGAR_syntax.prog -> CEGAR_syntax.var list * CEGAR_syntax.prog * CEGAR_syntax.prog

val incr_wp_max : bool ref
