(** Typed term substitutions *)

type elem = (Idnt.t, TypTerm.t) Map_._elem
type t = (Idnt.t, TypTerm.t) Map_._t

(** {6 Printers} *)

val pr_elem : Format.formatter -> elem -> unit
val pr : Format.formatter -> t -> unit

(** {6 Morphisms} *)

val map_elem : (elem -> elem) -> t -> t

(** {6 Auxiliary constructors} *)

val mk_elem : Idnt.t -> Term.t -> Type.t -> elem
val of_tts : TypTerm.t list -> t
(** [pat_match tenv1 tenv2] matches [tenv2] with [tenv1] *)
val pat_match : TypEnv.t -> TypEnv.t -> t
val bool_valuations : Idnt.t list -> t list

(** {6 Auxiliary destructors} *)

val tenv_of : t -> TypEnv.t
val tsub_of : t -> TermSubst.t

(** {6 Inspectors} *)

val fvs_elem : elem -> Idnt.t list
val fvs : t -> Idnt.t list

val dom : t -> Idnt.t list

val cyclic : t -> bool

val lookup : Idnt.t -> t -> TypTerm.t

(** {6 Operators} *)

val diff : t -> Idnt.t list -> t
