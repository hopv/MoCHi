(** Real term expressions *)

type t = Term.t

(** {6 Auxiliary constructors} *)

val make : float -> t
val zero : t
val one : t
val of_int : int -> t
val of_lin_exp : (float * Idnt.t) list * float -> t
val of_mono_exp : MonoRealExp.t -> t
val of_poly_exp : PolyRealExp.t -> t
val of_sexp : Sexp.t -> t

(** {6 Operators} *)

val neg : t -> t
val rsq : t -> t
val rcp : t -> t
val log2 : t -> t
val exp2 : t -> t
val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val div : t -> t -> t
val max : t -> t -> t
val min : t -> t -> t
val sum : t list -> t
val prod : t list -> t

(** {6 Inspectors} *)

val sum_of : t -> t list
val prod_of : t -> t list

val float_of : t -> float
