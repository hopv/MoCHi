(** Clauses *)

type t = Literal.t list

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit

(** {6 Auxiliary destructors} *)

val disjunction_of : t -> Disjunction.t
val formula_of : t -> Formula.t
