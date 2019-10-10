(** Logical formulas in disjunctive normal form *)

type t

(* @todo implement efficient dnf transformation *)

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit

(** {6 Auxiliary destructors} *)

val formula_of : t -> Formula.t
val cubes_of : t -> Cube.t list
val disjunction_of : t -> Disjunction.t

(** {6 Auxiliary constructors} *)

(** @todo deal with t1 <> t2
    [[lt ty t1 t2]; [gt ty t1 t2]] *)
val of_formula : Formula.t -> t

(** {6 Morphisms} *)

val map_literal : (Literal.t -> Literal.t) -> t -> t
val map_cube : (Cube.t -> Cube.t) -> t -> t
