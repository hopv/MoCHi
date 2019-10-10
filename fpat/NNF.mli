(** Logical formulas in negation normal form *)

type t

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit

(** {6 Auxiliary destructors} *)

val formula_of : t -> Formula.t

(** {6 Auxiliary constructors} *)

val of_formula : Formula.t -> t

(** {6 Morphisms} *)

(** @param t is in negation normal form *)
val map_literal : (Literal.t -> Literal.t) -> t -> t
