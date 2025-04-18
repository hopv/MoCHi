open CEGAR_syntax

(** Predicate abstraction *)

exception NotRefined

val abstract : ?preprocessed:prog -> prog -> var list * prog * prog * (var * var) list
val incr_wp_max : bool ref
