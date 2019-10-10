(** Typed predicate substitutions *)

type elem = Idnt.t * Pred.t
type t = elem list

(** {6 Printers} *)

val pr_elem : Format.formatter -> elem -> unit
val pr : Format.formatter -> t -> unit

(** {6 Inspectors} *)

val args_of : Idnt.t -> t -> TypEnv.t

(** @ensure not (List.duplicate ret) *)
val fvs_elem : elem -> Idnt.t list
val fvs : t -> Idnt.t list

(** @ensure not (List.duplicate ret) *)
val coeffs_elem : elem -> Idnt.t list
val coeffs : t -> Idnt.t list

val pvs : t -> Idnt.t list

(** @require fvs psub = []
    returns the tautology if pv is not in the domain of psub *)
val lookup : t -> Pva.t -> Formula.t
val lookup_and : t -> Pva.t -> Formula.t

(** may not be (Map.is_map psub)
    @raise Not_found if pv is not in the domain of psub *)
val lookup_fresh : t -> Pva.t -> Formula.t

(** @require pv is in the domain of psub *)
val lookup_node : t -> PredVar.t option -> Formula.t

val wo_fvs : t -> bool

(** {6 Auxiliary constructors} *)

val bot_of_tenv : TypEnv.t -> t
val top_of_tenv : TypEnv.t -> t

val mk_elem : Idnt.t -> TypEnv.t -> Formula.t -> elem
val elem_of_pvar : PredVar.t -> Formula.t -> elem

(** {6 Operators} *)

(** @require fvs psub = [] *)
val merge : t -> t
val merge_and : t -> t

val join : Formula.t list -> t list -> t

val restrict : t -> Idnt.t list -> t

val normalize : t -> t

val size : t -> int
