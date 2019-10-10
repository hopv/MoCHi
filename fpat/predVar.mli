(** Predicate variables *)

(** @invariant for any P(x1,...,xn),
    xi are are different from each other *)
type t

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit
val pr_tex : Format.formatter -> t -> unit
(** {6 Auxiliary constructors} *)

val make : Idnt.t -> TypEnv.t -> t
val of_type : Idnt.t -> Type.t -> t

(** {6 Auxiliary destructors} *)

val to_formula : t -> Formula.t

(** {6 Morphisms} *)

val fold : (Idnt.t -> TypEnv.t -> 'a) -> t -> 'a
val map_type : (Type.t -> Type.t) -> t -> t

(** {6 Operators} *)

val alpha : t -> t * (Idnt.t * Idnt.t) list

val rename_vars : (Idnt.t * Idnt.t) list -> t -> t
val rename : (Idnt.t * Idnt.t) list -> t -> t
val rename_fail : (Idnt.t * Idnt.t) list -> t -> t

val reset_uid : t -> t
val normalize_args : t -> t
val linearlize : t -> t *  Formula.t
val subst_tvars : TypEnv.t -> t -> t

(** {6 Inspectors} *)

val eq_idnt : t -> t -> bool
val cong : t -> t -> bool
val idnt_of : t -> Idnt.t
val args_of : t -> TypEnv.t
val fvs : t -> Idnt.t list
val fvs_bool : t -> Idnt.t list
val fvs_ty : t -> TypEnv.t
(** [pat_match pv1 pv2] matches pv2 with pv1 *)
val pat_match : t -> t -> TermSubst.t

val int_to_real : t -> t
