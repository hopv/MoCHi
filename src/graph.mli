type t

val from_edges : (int * int) list -> t
val from_directed_edges : (int * int) list -> t
val save_as_dot : string -> ?name_of:(int -> string) -> ?attribute_of_node:(int -> string) -> ?attribute_of_edge:(int * int -> string) -> t -> unit
val hops_to : t -> int list -> int array
val fold_node : (int -> 'a -> 'a) -> t -> 'a -> 'a
val fold_edge : (int -> int -> 'a -> 'a) -> t -> 'a -> 'a
