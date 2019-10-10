(** Atoms *)

type t

(** {6 Printers} *)

val ext_pr : (Format.formatter -> t -> unit) ref
val pr : Format.formatter -> t -> unit
val pr_list : Format.formatter -> t list -> unit
val ext_pr_tex : (Format.formatter -> t -> unit) ref
val pr_tex : Format.formatter -> t -> unit
(** {6 Auxiliary constructors} *)

val make : Const.t -> Term.t list -> t
val of_term : Term.t -> t
(** tautology *)
val mk_true : t
(** contradiction *)
val mk_false : t
val mk_var : Idnt.t -> Term.t list -> t
val mk_urel : Const.t -> Term.t -> t
val mk_brel : Const.t -> Term.t -> Term.t -> t

val eq : Type.t -> Term.t -> Term.t -> t
val neq : Type.t -> Term.t -> Term.t -> t
(** ignore equalities on functions *)
val eq_tt : TypTerm.t -> TypTerm.t -> t

(** {6 Auxiliary destructors} *)

val term_of : t -> Term.t

(** {6 Inspectors} *)

val fpvs : t -> Idnt.t list
val fpvs_strict : t -> Idnt.t list
val is_pva : Idnt.t list -> t -> bool
val is_eq : t -> bool
val is_neq : t -> bool

(** {6 Operators} *)

val subst : TermSubst.t -> t -> t
val remove_annot : t -> t
