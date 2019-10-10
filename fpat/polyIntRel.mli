(** Polynomial relations with integer coefficients *)

type t = Const.t * PolyIntExp.t

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit

(** {6 Auxiliary constructors} *)

val make : Const.t -> PolyIntExp.t -> t

val of_formula : Formula.t -> t

(** {6 Inspectors} *)

(** @ensure the result does not contain Const.Neg, Const.Sub,
            and negative integer constants *)
val formula_of : t -> Formula.t

val simplify_formula : Formula.t -> Formula.t
