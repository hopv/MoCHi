(** Maps *)

type ('a, 'b) _elem = 'a * 'b
type ('a, 'b) _t = ('a, 'b) _elem list

(** {6 Printers} *)

val pr_elem :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter -> ('a, 'b) _elem -> unit
val pr :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter -> ('a, 'b) _t -> unit

(** {6 Morphisms} *)

val map_dom : ('a -> 'c) -> ('a, 'b) _t -> ('c, 'b) _t
val map_codom : ('b -> 'c) -> ('a, 'b) _t -> ('a, 'c) _t

(** {6 Inspectors} *)

(** @raise Not_found if [x] is not in [dom f] *)
val apply : ('a, 'b) _t -> 'a -> 'b
val apply_default : 'b -> ('a, 'b) _t -> 'a -> 'b
val applyD : 'b -> ('a, 'b) _t -> 'a -> 'b
val apply_fail : ('a, 'b) _t -> 'a -> 'b
val applyF : ('a, 'b) _t -> 'a -> 'b
val apply_inverse : ('a, 'b) _t -> 'b -> 'a
val apply_inverse_fail : ('a, 'b) _t -> 'b -> 'a

val non_dup : ('a, 'b) _t -> bool
val is_map : ('a, 'b) _t -> bool
val in_dom : 'a -> ('a, 'b) _t -> bool

val dom : ('a, 'b) _t -> 'a list
val codom : ('a, 'b) _t -> 'b list

(** {6 Operators} *)

val diff : ('a, 'b) _t -> 'a list -> ('a, 'b) _t
val restrict : ('a, 'b) _t -> 'a list -> ('a, 'b) _t
val update : ('a, 'b) _t -> 'a -> 'b -> ('a, 'b) _t

val merge : ('a, 'b list) _t -> ('a, 'b list) _t
val merge2 : ('a, 'b list) _t -> ('a, 'b list) _t -> ('a, 'b list) _t
