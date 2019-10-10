(** Refinement type checking *)

val init : unit -> unit
val rev_consts : (Fdef.t * Formula.t) list ref
val nondet_pvars : Idnt.t list ref
val game_solving : bool ref
val ho_ufuns : bool ref

val wf_pvars : Idnt.t list ref
val is_wf_pvar : Idnt.t -> bool
val sync_wf_pvars : HCCS.t -> unit

val valid : RefTypEnv.t -> Formula.t -> bool
val subty : RefTypEnv.t -> RefTyp.t -> RefTyp.t -> bool
val tcheck : Prog.t -> string -> ?wf:bool -> PredSubst.t -> TypEnv.t -> RefTypEnv.t -> Term.t -> RefTyp.t -> bool
val tcheck_fdef : ?wf:bool -> PredSubst.t -> Prog.t -> TypEnv.t -> RefTypEnv.t -> Fdef.t -> bool
