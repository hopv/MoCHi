(** Predicate variable applications *)

type t

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit
val pr_tex : Format.formatter -> t -> unit

(** {6 Auxiliary constructors} *)

val make : Idnt.t -> TypTerm.t list -> t
val of_tenv : Idnt.t -> TypEnv.t -> t
val of_pvar : PredVar.t -> t
val of_formula : Formula.t -> t

(** {6 Auxiliary destructors} *)

val to_formula : t -> Formula.t

(** {6 Morphisms} *)

val fold : (Idnt.t -> TypTerm.t list -> 'a) -> t -> 'a
(** @require [f t] has the type [ty] *)
val map_term : (Term.t -> Term.t) -> t -> t
val map_type : (Type.t -> Type.t) -> t -> t

(** {6 Inspectors} *)

val idnt_of : t -> Idnt.t
val args_of : t -> TypTerm.t list
val type_of : t -> Type.t
val tenv_of : t -> TypEnv.t

val eq_idnt : t -> t -> bool

val fvs_ty : t -> (Idnt.t *Type.t) list
val fvs : t -> Idnt.t list
val fvs_bool: t -> Idnt.t list
val coeffs : t -> Idnt.t list
val ufuns_of : (Formula.t -> Idnt.t list) -> t -> Idnt.t list

(** @return the number of duplicate predicate variables in [atms] *)
val num_dup : t list -> int

val pvar_of : t -> PredVar.t * Formula.t
(** [pat_match pv pva] matches pva with pv *)
val pat_match : PredVar.t -> t -> TermSubst.t

val equiv :
  (Formula.t list -> Formula.t list -> bool) ->
  (Formula.t -> Formula.t) ->
  Formula.t list -> t -> t -> bool

(** @return whether there is a substitution sub for variables {x | p x} s.t.
            equiv env (subst sub (pid2, ttys2)) (pid1, ttys1) *)
val matches :
  (Formula.t list -> Formula.t list -> bool) ->
  (Formula.t -> Formula.t) ->
  (Idnt.t -> bool) -> Formula.t list -> t -> t -> bool

(** {6 Operators} *)

val rename_vars : (Idnt.t * Idnt.t) list -> t -> t
val rename : (Idnt.t * Idnt.t) list -> t -> t
val rename_fail : (Idnt.t * Idnt.t) list -> t -> t
val fresh : t -> t
val simplify : t -> t
val subst : TermSubst.t -> t -> t
val subst_fixed : TermSubst.t -> t -> t
val subst_tvars : TypEnv.t -> t -> t

val int_to_real : t -> t
