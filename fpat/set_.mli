open Util
open Combinator

(** Sets (aka lists modulo permutation and contraction) *)

type 'a t = 'a list

(** {6 Inspectors} *)

val subset : ?cmp:('a -> 'a -> bool) -> 'a t -> 'a t -> bool
val equiv : ?cmp:('a -> 'a -> bool) -> 'a t -> 'a t -> bool
val intersects : ?cmp:('a -> 'a -> bool) -> 'a t -> 'a t -> bool
val disjoint : ?cmp:('a -> 'a -> bool) -> 'a t -> 'a t -> bool

(** {6 Operators} *)

val diff : ?cmp:('a -> 'a -> bool) -> 'a t -> 'a t -> 'a t
val inter : ?cmp:('a -> 'a -> bool) -> 'a t -> 'a t -> 'a t
val union : ?eq:('a -> 'a -> bool) -> 'a t -> 'a t -> 'a t

val power : 'a t -> 'a t t
(** [subsets_of_size n s] returns all the subsets of [s] with the size [n] *)
val subsets_of_size : int -> 'a t -> 'a t t
(** [equiv_classes rel s] divides [s] by the transitive closure of [rel] *)
val equiv_classes : ('a -> 'a -> bool) -> 'a t -> 'a t t
val representatives : ('a -> 'a -> bool) -> 'a t -> 'a t

(** [minimal p s] returns a minimal subset of [s] that satisfy [p]
    @require [p s] *)
val minimal : ('a t -> bool) -> 'a t -> 'a t
(** @todo rename *)
val cover : 'a t t -> 'a t t


val reachable : 'a list -> ('a -> 'a list) -> 'a list
