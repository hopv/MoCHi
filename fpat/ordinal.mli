(** Ordinals *)

type t

val make : int -> t

val pr : Format.formatter -> t -> unit
val string_of : t -> string
