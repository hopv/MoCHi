(** Interpolating provers *)

type t = Formula.t -> Formula.t -> Formula.t

(** {6 Exceptions} *)

exception NoInterpolant
exception Fail
exception Unknown

(** {6 Options} *)

val interp_simplify : bool ref

(** {6 CSIsat options} *)

val csisat_use_integer_heuristic : bool ref
val csisat_use_theory : bool ref
val csisat_int_mode : bool ref
val degree : int ref

(** {6 Interpolating prover combinators} *)

(** @todo check whether this is useful *)
val interpolate_quick : t -> t
val interpolate_simplify :
  ?qelim:(Idnt.t list -> Formula.t -> Formula.t) -> t -> t
val interpolate_log : t -> t
(** rename variables except those {x | p x} shared by t1 and t2 *)
val interpolate_fresh : (Idnt.t -> bool) -> t -> t

(** {6 Dynamically linked solvers} *)

val ext_interpolate_csisat0 : t ref
val interpolate_csisat0_dyn : t
val ext_interpolate_csisat : ((Idnt.t -> bool) -> t) ref
val interpolate_csisat_dyn : (Idnt.t -> bool) -> t
val ext_interpolate_csisat_gen : ((Idnt.t -> bool) -> t) ref
val interpolate_csisat_gen_dyn : (Idnt.t -> bool) -> t
val ext_interpolate_aisat : ((Idnt.t -> bool) -> t) ref
val interpolate_aisat_dyn : (Idnt.t -> bool) -> t
val ext_interpolate_z3 : ((Idnt.t -> bool) -> t) ref
val interpolate_z3_dyn : (Idnt.t -> bool) -> t

val link_dyn : ((Idnt.t -> bool) -> t) -> unit
val get_dyn : unit -> ((Idnt.t -> bool) -> t)
val interpolate_dyn : (Idnt.t -> bool) -> t
