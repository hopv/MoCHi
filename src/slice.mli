open Syntax

val slice : ?respect_div:bool -> term -> term
val slice_problem : Problem.t -> Problem.t * Preprocess_common.trans_cex
