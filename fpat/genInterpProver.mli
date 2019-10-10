(** Generalizing interpolating prover *)

type t =
    Idnt.t list ->
    TypEnv.t ->
    Formula.t list ->
    Formula.t list ->
    PredSubst.t

exception NoInterpolant
exception Fail (* @todo Unknown? *)
