(** Horn clause constraint sets *)

type t = HornClause.t list
type node = Idnt.t option

(** {6 Options} *)

val resolve_inc : bool ref

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit
val pr_tex : Format.formatter -> t -> unit
val pr_verbose : Format.formatter -> t -> unit

(** {6 Auxiliary constructors} *)

val of_psub : PredSubst.t -> t
(** @todo this may split a Horn clause into Horn clauses
          use of_formula instead to keep the constraints compact *)
val of_formula0 : Idnt.t list -> Formula.t -> t
val of_formula : Formula.t list -> Formula.t -> t
val of_smtlib1 : Sexp.t -> t
val of_smtlib2 : Sexp.t list -> t

(** {6 Morphisms} *)

val map_phi : (Formula.t -> Formula.t) -> t -> t
val map_pred : (t -> 'a) -> t -> 'a list

(** {6 Inspectors} *)

val fvs : t -> Idnt.t list
val coeffs : t -> Idnt.t list
val ufuns : t -> Idnt.t list
(** @return the predicate variables in the body *)
val pvsB : t -> Idnt.t Bag.t
(** @return the predicate variables in the body *)
val pvsH : t -> Idnt.t Bag.t
(** @return the predicate variables *)
val pvs : t -> Idnt.t Bag.t
val used_pvs : t -> Idnt.t Bag.t
val defined_pvs : t -> Idnt.t Bag.t
val undefined_pvs : t -> Idnt.t Bag.t
val unused_pvs : t -> Idnt.t Bag.t
(** @return the set of the merging predicate variables *)
val mpvs : t -> Idnt.t list
(** @return the set of the branching predicate variables *)
val bpvs : t ->Idnt.t list
val num_pvs : t -> int

(** @ensure [not (Set.duplicate (tenvB hcs))] *)
val tenvB : t -> TypEnv.t
(** @ensure [not (Set.duplicate (tenvH hcs))] *)
val tenvH : t -> TypEnv.t
(** @ensure [not (Set.duplicate (tenv hcs))] *)
val tenv : t -> TypEnv.t

val defs_of : t -> t
val goals_of : t -> t

val nodesH : t -> node list
val find : node -> t -> HornClause.t
val find_all : node -> t -> t
(** returns predecessor nodes *)
val preds_of : node -> t -> node Bag.t

(* @todo check whether forall hcs.
   psub_of (substB (lbs_of hcs) hcs)
   = lbs_of hcs *)
val psub_of : t -> PredSubst.t

val lookup : t -> Pva.t -> HornClause.body list
val lookup_eq : t -> Pva.t -> (HornClause.body * (Idnt.t * Type.t) list) list
val formula_of_bodies : HornClause.body list -> Formula.t
val formula_of_bodies_eq : (HornClause.body * (Idnt.t * Type.t) list) list -> Formula.t
(** @require is_non_disjunctive hcs *)
val det_lookup : t -> Pva.t -> HornClause.body
val det_lookupF : t -> Pva.t -> HornClause.body
val det_lookupD : t -> Pva.t -> HornClause.body

val forward_data_flow_analysis :
  (node -> 'a) ->
  (node -> (node * 'a) list -> 'a) ->
  ('a -> 'a -> bool) -> t ->
  (node * 'a) list

val reachable : t -> (node * node list) list

(** {5 Predicates} *)

(** @return if body-disjoint *)
val is_tree : t -> bool
(** @return if head-disjoint *)
val is_non_disjunctive : t -> bool
val is_linear_def : t -> Idnt.t -> bool
val is_affine_def : t -> Idnt.t -> bool
val is_linear_use : t -> Idnt.t -> bool
val is_affine_use : t -> Idnt.t -> bool
val is_well_defined : t -> bool
val is_non_redundant : t -> bool

val defined : t -> Idnt.t -> bool
val not_defined : t -> Idnt.t -> bool
val used : t -> Idnt.t -> bool
val not_used : t -> Idnt.t -> bool

(** {6 Operators} *)

val rename : (Idnt.t * Idnt.t) list -> t -> t
val normalize : t -> t
val fresh_pvars : t -> t

val simplify : t -> t
val simplify_lv1 : t -> t
val simplify_lv2 : ?tenv:TypEnv.t -> t -> t
val simplify_light : Idnt.t list -> t -> t
val simplify_full : ?tenv:TypEnv.t -> Idnt.t list -> t -> t
val simplify_trivial : ?no_inline:(Idnt.t -> bool) -> t -> t
val goal_flattening : t -> t

(** @require [not (Set.intersects (Map.dom sub) (fvs popt))] *)
val subst_varsB : TermSubst.t -> t -> t
val subst_tvars : TypEnv.t -> t -> t
(** @require Map.is_map psub *)
val substB :
  ?simplify_hc:(HornClause.t -> HornClause.t) ->
  PredSubst.t -> t -> t
(** @require Map.is_map psub *)
val substH :
  ?simplify_hc:(HornClause.t -> HornClause.t) ->
  PredSubst.t -> t -> t
(** @require Map.is_map psub *)
val subst :
  ?simplify_hc:(HornClause.t -> HornClause.t) ->
  PredSubst.t -> t -> t

val fresh : t -> t
val fresh_label : (string * HornClause.t) list -> (string * HornClause.t) list
val alpha : t -> t

val elim_non_defined : ?tenv:TypEnv.t -> t -> t
val complement : t -> t

val resolve_hc : ?tenv:TypEnv.t -> t -> HornClause.t -> t
val resolve_hc_fixed : t -> HornClause.t -> t
val resolve : ?tenv:TypEnv.t -> t -> t -> t
val resolve_fixed : t -> t -> t
(** @deprecated ??
    @todo correct? *)
val fixpoint : t -> t

(** [depend pvs hcs] extracts Horn clauses that depend on the
    predicate variables in [pvs] from [hcs] *)
val depend : Idnt.t list -> t -> t

(** [backward_depend nds hcs] extract Horn clauses that depend
    backward on the predicate variables in [nds] or the root nodes *)
val backward_depend :
  ?mask:node list ->
  node list -> t -> t

(** note: boolean atoms and non-boolean atoms have no dependency
    @require [hcs] is conjunctive
    @todo support disjunction *)
val split_bool_non_bool : t -> t * t
val split_bool_non_bool_label : (string * HornClause.t) list -> (string * HornClause.t) list * (string * HornClause.t) list

val normalize2 : ?force:bool -> t -> t
val elim_disj : t -> t
(** returns a conjunctive HCCS *)
val conj_hccs_of : t -> t
(** @todo expand pred vars near leaves first *)
val expand_dag : t -> t * (Idnt.t * Idnt.t) list
(** clustering and topological sorting
    @ensure the i < j th HCCS in the returned sequence does not refer to a non-root pred. vars. in the j-th HCCS *)
val tree_partition_of : t -> (node * t) list

val merge : t -> t

(** reduce predicate variables
    @todo what is a difference from
          HCCSSolver.solve_inline
    @require a predicate variable [p]
              s.t. [is_exc p] is not reduced *)
val reduce : ?tenv:TypEnv.t -> (Idnt.t -> bool) -> t -> t

(** only the satisfiability of head- and body-disjoint HCCSs is preserved unless we use the alpha conversion
    @require P(x) /\ P(x) => ... is not allowed *)

val simplified_form_of : t -> (Idnt.t * TypEnv.t) list * t

(** {6 Inspectors} *)

(** [is_solution hcs sol] returns whether
    [sol] is a solution for [hcs]
    @require [fvs sol = [] &&
              Map.is_map sol &&
              Set.subset (pvs hcs) (Map.dom sol)] *)
val is_solution : t -> PredSubst.t -> bool

(** {6 Operators} *)

val int_to_real : t -> t

val elim_ufuns : t -> t

(** {6 Exporters} *)

val save_graphviz : string -> t -> unit
val save_smtlib : string -> t -> unit
val save_smtlib2 : string -> t -> unit
