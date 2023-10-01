open Syntax

val slice : ?respect_div:bool -> term -> term

val slice_problem : Problem.t -> Problem.t Util.LazyList.t
