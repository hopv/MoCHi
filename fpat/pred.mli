(** Predicates *)

type t = TypEnv.t * Formula.t

val pr : Format.formatter -> t -> unit

(** {6 Auxiliary constructors} *)

val make : TypEnv.t -> Formula.t -> t
val mk_bot : Type.t -> t
val mk_top : Type.t -> t

(** {6 Inspectors} *)

val type_of : t -> Type.t
val fvs : t -> Idnt.t list
val coeffs : t -> Idnt.t list

(** {6 Operators} *)

val apply : t -> TypTerm.t list -> Formula.t

val fresh : t -> t

val normalize : t -> t

val band : t list -> t
val bor : t list -> t
val bnot : t -> t

val is_true : t -> bool
val is_false : t -> bool
