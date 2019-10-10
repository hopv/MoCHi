(** Interface to CSIsat *)
(* CSIsat does not fully support interpolation of QFLIA formulas *)

val interpolate0 : ?generalize:bool -> InterpProver.t
val interpolate : ?generalize:bool -> (Idnt.t -> bool) -> InterpProver.t
