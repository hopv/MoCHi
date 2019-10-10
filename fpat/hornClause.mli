(** Horn clauses *)

(** {6 Constructors} *)

(** @invariant for any [pva] in the body,
    [Pva.coeffs pva = []] *)

type head
type body
type t

val disable_conj : bool ref

(** {6 Printers} *)

val pr_head : Format.formatter -> head -> unit
val pr_body : Format.formatter -> body -> unit
val pr_head_tex : Format.formatter -> head -> unit
val pr_body_tex : Format.formatter -> body -> unit
val pr : Format.formatter -> t -> unit
val pr_tex : Format.formatter -> t -> unit
(** {6 Auxiliary constructors} *)

val mk_head : ?tenv:TypEnv.t -> ?phi:Formula.t -> PredVar.t option -> head
val mk_body : Pva.t list -> Formula.t -> body
val make : head -> body -> t
val mk_def :
  ?tenv:TypEnv.t -> ?hphi:Formula.t -> PredVar.t ->
  Pva.t list -> Formula.t -> t
val mk_goal : Pva.t list -> Formula.t -> t

val body_of_formulas : Formula.t list -> body
val of_formulas : Idnt.t list -> Formula.t -> Formula.t list -> t
val of_clause : Idnt.t list -> Clause.t -> t

(** {6 Morphisms} *)

val head_map :
  (TypEnv.t -> TypEnv.t) ->
  (PredVar.t option -> PredVar.t option) ->
  (Formula.t -> Formula.t) ->
  head -> head
val body_map :
  (Pva.t list -> Pva.t list) ->
  (Formula.t -> Formula.t) ->
  body -> body

val ae_fold :
  (TypEnv.t -> PredVar.t option -> Formula.t ->
   Pva.t list -> Formula.t -> 'a) ->
  t -> 'a
val fold :
  (Pva.t list -> Formula.t -> 'a) ->
  (PredVar.t -> Pva.t list -> Formula.t -> 'a) ->
  t -> 'a

val map : (head -> head) -> (body -> body) -> t -> t
val map_head : (head -> head) -> t -> t
val map_body : (body -> body) -> t -> t
val map_bpvas : (Pva.t list -> Pva.t list) -> t -> t
val map_phi : (Formula.t -> Formula.t) -> t -> t

(** {6 Inspectors} *)

val pat_match_head : PredVar.t option -> PredVar.t option -> TermSubst.t

val pv_of_head : head -> PredVar.t option
val tenv_of_head : head -> TypEnv.t
val phi_of_head : head -> Formula.t
val pvas_of_body : body -> Pva.t list
val phi_of_body : body -> Formula.t

val head_of : t -> head
val body_of : t -> body
val htenv_of : t -> TypEnv.t
val hpv_of : t -> PredVar.t option
val hphi_of : t -> Formula.t
val bpvas_of : t -> Pva.t list
val bphi_of : t -> Formula.t

val nodesB : t -> Idnt.t option list
val nodeH : t -> Idnt.t option
val nodes : t -> Idnt.t option list

val eq_shapeB : t -> t -> bool
val eq_shapeH : t -> t -> bool
val eq_shape : t -> t -> bool
val cong : t -> t -> bool

(** @return a multi set *)
val pvsB : t -> Idnt.t list
(** @return a multi set *)
val pvsH : t -> Idnt.t list
(** @return a multi set *)
val pvs : t -> Idnt.t list

val is_goal : t -> bool
val is_root : t -> bool
val is_coeff : t -> bool

val is_cyclic : t -> bool
val is_trivial : t -> bool

val use : t -> Idnt.t -> bool
val def : t -> Idnt.t -> bool

(**)

val is_solution : t -> PredSubst.t -> bool
val find_point_cex :
  ?retint:bool -> ?extremal:bool -> ?refute_all:bool ->
  t -> PredSubst.t -> Polyhedron.optmodel option

(**)

val fvsH : t -> Idnt.t list
val fvsH_bool : t -> Idnt.t list
val fvsH_ty : t -> TypEnv.t
val fvsB : t -> Idnt.t list
val fvsB_bool : t -> Idnt.t list
val fvsB_ty : t -> TypEnv.t
(** @return free variables *)
val fvs : t -> Idnt.t list
val fvs_ty : t -> TypEnv.t

val coeffs : t -> Idnt.t list
val ufuns : t -> Idnt.t list

(** @ensure not (Set.duplicate res) *)
val tenvB : t -> TypEnv.t
(** @ensure not (Set.duplicate res) *)
val tenvH : t -> TypEnv.t
(** @ensure not (Set.duplicate res) *)
val tenv : t -> TypEnv.t

(**)

val formula_of_body : body -> Formula.t
val formula_of : t -> Formula.t
(* @ensure lbs is a solution for hc iff
           [|= formula_of_forward lbs hc => bot] *)
val formula_of_forward : PredSubst.t -> t -> Formula.t

(**)

(** {6 Operators} *)

(** @require not (Set.intersects (Map.dom sub) (fvs popt)) *)
val subst_varsB : TermSubst.t -> t -> t
val subst_tvars : TypEnv.t -> t -> t
(** @require Map.is_map psub *)
val substB : ?fresh:bool -> ?simplify:(t -> t) -> PredSubst.t -> t -> t
(** @require Map.is_map psub *)
val substH : ?fresh:bool -> ?simplify:(t -> t) -> PredSubst.t -> t -> t
(** @require Map.is_map psub *)
val subst : ?fresh:bool -> ?simplify:(t -> t) -> PredSubst.t -> t -> t

(** rename free variables to fresh ones *)
val fresh : t -> t
val alpha : t -> t

val simplify : t -> t
(** @ensure variables in [vs] are not eliminated
    try to eliminate term variables *)
val simplify_light : Idnt.t list -> t -> t
(** @ensure variables in [vs] are not eliminated
    try to eliminate predicate variables *)
val simplify_full : ?tenv:TypEnv.t -> Idnt.t list -> t -> t

val elim_disj : t -> t list

(** returns conjunctive Horn clauses *)
val conj_hcs_of : t -> t list

(** replace the arguments of [pvas] with fresh vars
    @todo a predicate of the form P(x,x) may occur in the body? *)
val normalize2 : ?force:bool -> t -> t

(** @require each argument of each predicate variable must be a variable *)
val split_bool_non_bool : t -> t * t

val simplified_form_of : (Idnt.t * TypEnv.t) list -> t -> t

val and_body : body list -> body
val simplify_bodies : body list -> body list

val lookup : t -> Pva.t -> body
val lookup_eq : t -> Pva.t -> body * (Idnt.t * Type.t) list

val rename : (Idnt.t * Idnt.t) list -> t -> t
val normalize : t -> t

val int_to_real : t -> t
val elim_ufuns : t -> t

val defmatch : t list -> Pva.t * 'a -> ((Pva.t * 'a) list * Formula.t) list
