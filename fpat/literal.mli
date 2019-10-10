(** Literals *)

type t = private Formula.t

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit
val pr_list : Format.formatter -> t list -> unit

(** {6 Auxiliary destructors} *)

val term_of : t -> Term.t
val formula_of : t -> Formula.t
val atom_of : t -> Atom.t

(** {6 Auxiliary constructors} *)

val mk_atom : Const.t -> Term.t list -> t
val of_term : Term.t -> t
val of_formula : Formula.t -> t
val of_atom : Atom.t -> t

val mk_true : t
val mk_false : t
val bnot : t -> t
val mk_var : Idnt.t -> Term.t list -> t
val mk_brel : Const.t -> Term.t -> Term.t -> t

val eq : Type.t -> Term.t -> Term.t -> t
val neq : Type.t -> Term.t -> Term.t -> t
val eq_tt : TypTerm.t -> TypTerm.t -> t

(** {6 Morphisms} *)

val fold : (Atom.t -> 'a) -> (Atom.t -> 'a) -> t -> 'a

(** {6 Inspectors} *)

val is_true : t -> bool
val is_false : t -> bool

(** @todo support predicate variables *)
val is_pos : t -> bool
val is_exists : t -> bool
val is_pva : Idnt.t list -> t -> bool
