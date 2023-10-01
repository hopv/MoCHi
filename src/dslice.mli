open Syntax

(*
val slice_sub : bool -> term -> float -> term

(** `slice_subs t p` returns `[slice_sub t 0.; slice_sub t p; ...; slice_sub t 1.]` *)
val slice_subs : bool -> term -> float -> term list
 *)

val slice_top_fun : id list -> term -> float -> term
