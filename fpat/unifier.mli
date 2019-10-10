(** Unification and pattern matching *)

(** higher-order unification
    e.g., given [f (d x)] and [a b (c (d e))] with unknown variable [f] and [x],
          return [f y = a b (c y)] and [x = e] *)
val hounify : Idnt.t list -> Term.t -> Term.t -> TermSubst.t

exception NeverMatch
exception MayNotMatch

(** [match_linpat xs t le] matches [t] with [le]
    @require [Set_.inter (Term.fvs t) xs = []]
    @ensure [Term.subst (TypTermSubst.tsub_of ret) (term_of le) = t]
    @ensure [Set_.subset (TypTermSubst.dom ret) (fvs le)]
    @ensure [Set_.subset (TypTermSubst.dom ret) xs] *)
val match_linpat : Idnt.t list -> Term.t -> LinIntExp.t -> TypTermSubst.t

(** [matche_tt xs tt1 tt2] matches [tt1] with [tt2]
    @require [Set_.inter (Term.fvs t1) xs = []]
    @require if [valid t], then [t] is valid but if [not (valid t)], [t] may be valid
    @ensure [Term.subst (TypTermSubst.tsub_of ret) t2 = t1]
    @ensure [Set_.subset (TypTermSubst.dom ret) (fvs t2)]
    @ensure [Set_.subset (TypTermSubst.dom ret) xs] *)
val match_tt :
  ?valid:(Formula.t -> bool) ->
  Idnt.t list -> TypTerm.t -> TypTerm.t -> TypTermSubst.t
