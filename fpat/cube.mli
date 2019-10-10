(** Cubes *)

type t = Literal.t list

exception NonCube

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit

(** {6 Auxiliary constructors} *)

val of_formula : Formula.t -> t

(** {6 Auxiliary destructors} *)

val conjunction_of : t -> Conjunction.t
val formula_of : t -> Formula.t
