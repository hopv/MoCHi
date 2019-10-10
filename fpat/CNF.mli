(** Logical formulas in conjunctive normal form *)

type t

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit

(** {6 Auxiliary constructors} *)

val of_formula : Formula.t -> t
val of_formula_loose : Formula.t -> t

(** {6 Auxiliary destructors} *)

val to_formula : t -> Formula.t
val to_clauses : t -> Clause.t list
val to_conjunction : t -> Conjunction.t

(** {6 Morphisms} *)

val map_literal : (Literal.t -> Literal.t) -> t -> t
val map_clause : (Clause.t -> Clause.t) -> t -> t
