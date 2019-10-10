(** Conjunctions *)

type t = Formula.t list

val formula_of : t -> Formula.t

(** simple syntactic simplification *)
val simplify : t -> t
