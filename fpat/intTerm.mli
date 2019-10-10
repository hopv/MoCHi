(** Integer term expressions *)

type t = Term.t

(** {6 Auxiliary constructors} *)

val make : int -> t
val of_big_int : Big_int_Z.big_int -> t
val zero : t
val one : t

val of_sexp : Sexp.t -> t
val of_lin_exp : LinIntExp.t -> t
val of_mono_exp : MonoIntExp.t -> t
val of_poly_exp : PolyIntExp.t -> t
val of_lin_poly_exp : LinPolyIntExp.t -> t

(** {6 Operators} *)

val neg : t -> t
val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val div : t -> t -> t
val max : t -> t -> t
val min : t -> t -> t
val mk_mod : t -> t -> t

val sum : t list -> t
val prod : t list -> t

(** {6 Inspectors} *)

val int_of : t -> int

val is_zero : t -> bool
val is_one : t -> bool
val is_const : t -> bool

val equiv : t -> t -> bool
val (>) : t -> t -> bool
val (<) : t -> t -> bool

(** {6 Operators} *)

val factorize : PolyIntExp.t -> t list
