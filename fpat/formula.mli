(** Logical formulas *)

type t

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit
val pr_list : Format.formatter -> t list -> unit
val pr_tex  : Format.formatter -> t -> unit

(** {6 Auxiliary destructors} *)

(** @return a term of the type bool *)
val term_of : t -> Term.t
val atom_of : t -> Atom.t

val is_true : t -> bool
val is_false : t -> bool
val is_and : t -> bool
val is_or : t -> bool
val is_pva : Idnt.t list -> t -> bool
val is_binder : t -> bool
val is_forall : t -> bool
val is_exists : t -> bool
val is_mu : t -> bool
val is_nu : t -> bool
val is_box : t -> bool
val is_diamond : t -> bool
val contain_binder : t -> bool

val let_not : t -> (t -> 'a) -> 'a
val let_and : t -> (t -> t -> 'a) -> 'a
val let_or : t -> (t -> t -> 'a) -> 'a
val let_imply : t -> (t -> t -> 'a) -> 'a
val let_iff : t -> (t -> t -> 'a) -> 'a
val let_forall : t -> (Idnt.t -> Type.t -> t -> 'a) -> 'a
val let_exists : t -> (Idnt.t -> Type.t -> t -> 'a) -> 'a
val let_mu : t -> (Idnt.t -> t -> 'a) -> 'a
val let_nu : t -> (Idnt.t -> t -> 'a) -> 'a
val let_pva : t -> (Idnt.t -> TypTerm.t list -> 'a) -> 'a

(** {6 Auxiliary constructors} *)

val mk_atom : Const.t -> Term.t list -> t
(** @todo check whether t is a well-formed formula *)
val of_term : Term.t -> t
val of_atom : Atom.t -> t

val mk_true : t
val mk_false : t
val mk_var : Idnt.t -> Term.t list -> t
val mk_brel : Const.t -> Term.t -> Term.t -> t

val eq : Type.t -> Term.t -> Term.t -> t
val neq : Type.t -> Term.t -> Term.t -> t
val eq_tt : TypTerm.t -> TypTerm.t -> t

(** @todo rename this to mk_and *)
val band : t list -> t
val mk_and : t -> t -> t
(** @todo rename this to mk_or *)
val bor : t list -> t
val mk_or : t -> t -> t
(** @todo rename this to mk_not *)
val bnot : t -> t
(** @todo rename this to mk_imply *)
val imply : t -> t -> t
(** @todo rename this to mk_forall *)
val forall : (Idnt.t * Type.t) list -> t -> t
(** @todo rename this to mk_exists *)
val exists : (Idnt.t * Type.t) list -> t -> t

val box : string -> t -> t
val diamond : string -> t -> t
val mu : Idnt.t -> t -> t
val nu : Idnt.t -> t -> t

val mk_iff : t -> t -> t
val mk_iff_disj : t -> t -> t
val mk_iff_conj : t -> t -> t
val mk_not_iff_disj : t -> t -> t
val mk_not_iff_conj : t -> t -> t

(** {6 Morphisms} *)

val para :
  < fatom : Atom.t -> 'a;
    ftrue : unit -> 'a;
    ffalse : unit -> 'a;
    fnot : t -> 'a -> 'a;
    fand : t -> 'a -> t -> 'a -> 'a;
    for_ : t -> 'a -> t -> 'a -> 'a;
    fiff : t -> 'a -> t -> 'a -> 'a;
    fimply : t -> 'a -> t -> 'a -> 'a;
    fforall : TypEnv.elem -> t -> 'a -> 'a;
    fexists : TypEnv.elem -> t -> 'a -> 'a; .. > ->
  t -> 'a
val lazy_para :
  < fatom : Atom.t -> 'a;
    ftrue : unit -> 'a;
    ffalse : unit -> 'a;
    fnot : t -> 'a lazy_t -> 'a;
    fand : t -> 'a lazy_t -> t -> 'a lazy_t -> 'a;
    for_ : t -> 'a lazy_t -> t -> 'a lazy_t -> 'a;
    fiff : t -> 'a lazy_t -> t -> 'a lazy_t -> 'a;
    fimply : t -> 'a lazy_t -> t -> 'a lazy_t -> 'a;
    fforall : TypEnv.elem -> t -> 'a lazy_t -> 'a;
    fexists : TypEnv.elem -> t -> 'a lazy_t -> 'a; .. > ->
  t -> 'a
val fold :
  < fatom : Atom.t -> 'a;
    ftrue : unit -> 'a;
    ffalse : unit -> 'a;
    fnot : 'a -> 'a;
    fand : 'a -> 'a -> 'a;
    for_ : 'a -> 'a -> 'a;
    fiff : 'a -> 'a -> 'a;
    fimply : 'a -> 'a -> 'a;
    fforall : TypEnv.elem -> 'a -> 'a;
    fexists : TypEnv.elem -> 'a -> 'a; .. > ->
  t -> 'a
val fold_pos :
  < fatom : bool -> Atom.t -> 'a;
    ftrue : unit -> 'a;
    ffalse : unit -> 'a;
    fnot : 'a -> 'a;
    fand : 'a -> 'a -> 'a;
    for_ : 'a -> 'a -> 'a;
    fiff : 'a -> 'a -> 'a;
    fimply : 'a -> 'a -> 'a;
    fforall : TypEnv.elem -> 'a -> 'a;
    fexists : TypEnv.elem -> 'a -> 'a; .. > ->
  t -> 'a
val visit :
  < fatom : Atom.t -> 'a;
    ftrue : unit -> 'a;
    ffalse : unit -> 'a;
    fnot : t -> 'a;
    fand : t -> t -> 'a;
    for_ : t -> t -> 'a;
    fiff : t -> t -> 'a;
    fimply : t -> t -> 'a;
    fforall : TypEnv.elem -> t -> 'a;
    fexists : TypEnv.elem -> t -> 'a; .. > ->
  t -> 'a

val map_var : (Idnt.t -> Idnt.t) -> t -> t
val map_atom : (Atom.t -> t) -> t -> t

val fold_band : (Atom.t -> bool) -> t -> bool
val fold_bor : (Atom.t -> bool) -> t -> bool
val fold_set : (Atom.t -> 'a Set_.t) -> t -> 'a Set_.t

(** {6 Inspectors} *)

val fvs : t -> Idnt.t list
val coeffs : t -> Idnt.t list
val constants : t -> Const.t list
val equiv : t -> t -> bool

val fvs_unit : t -> Idnt.t list
val fvs_bool : t -> Idnt.t list
val fvs_int : t -> Idnt.t list
val fvs_ty : t -> TypEnv.t

(** @require no second order quantification *)
val fpvs : t -> Idnt.t list
val fpvs_strict : t -> Idnt.t list

val args_of_binder : t -> (TypEnv.t * t)
val string_of : t -> string
val atoms : t -> Atom.t list
val conjuncts_of : t -> t list
val disjuncts_of : t -> t list

(** {6 Operators} *)

val subst : TermSubst.t -> t -> t
val subst_fixed : ?simplify:(t -> t) -> TermSubst.t -> t -> t
val fresh : Idnt.t list -> t -> t
val rename : (Idnt.t * Idnt.t) list -> t -> t

val subst_tvars : TypEnv.t -> t -> t
val elim_imply_iff : t -> t
(** extract equivalence classes *)
val eqcls_of : t -> (Idnt.t list * Type.t) list * t list
(** remove type annotation *)
val remove_annot : t -> t
val unfold : t -> t

(** @require [is_valid phi] iff [phi] is valid *)
val non_dup_ttsub : ?is_valid:(t -> bool) -> TypTermSubst.t -> bool
val resolve_duplicates_in_ttsub : TypTermSubst.t -> TypTermSubst.t * t list
val resolve_duplicates_in_tsub : TermSubst.t -> TermSubst.t * t list

(** {6 Auxiliary constructors} *)

(** ignore equalities on functions *)
val of_ttsub_elem : TypTermSubst.elem -> t
val of_ttsub : TypTermSubst.t -> t
val of_tsub : TermSubst.t -> t

(** {6 Auxiliary destructors} *)

val to_simple_ttsub : t -> TypTermSubst.t * t
val to_rename_tsub : (t -> t) -> Idnt.t list -> t -> TermSubst.t * t
val to_const_tsub : Idnt.t list -> t -> TermSubst.t * t
