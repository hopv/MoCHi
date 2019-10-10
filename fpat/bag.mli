(** Bags (aka lists modulo permutation) *)

type 'a t = 'a list

(** {6 Inspectors} *)

val subset : 'a t -> 'a t -> bool
val equiv : 'a t -> 'a t -> bool

val non_duplicated : ?eq:('a -> 'a -> bool) -> 'a t -> bool
val duplicated : ?eq:('a -> 'a -> bool) -> 'a t -> bool
val num_occurrences : 'a -> 'a t -> int

(** {6 Operators} *)

val inter : 'a t -> 'a t -> 'a t
val diff : 'a t -> 'a t -> 'a t

(** @todo verify that this always returns a set *)
val get_dup_elems : ?cmp:('a -> 'a -> bool) -> 'a t -> 'a Set_.t
