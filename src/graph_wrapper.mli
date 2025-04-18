type t

val from_edges : (int * int) list -> t
val from_directed_edges : (int * int) list -> t

val save_as_dot :
  string ->
  ?name_of:(int -> string) ->
  ?attribute_of_node:(int -> string) ->
  ?attribute_of_edge:(int * int -> string) ->
  ?layout:string ->
  t ->
  unit

val hops_to : t -> int list -> int array
val fold_node : (int -> 'a -> 'a) -> t -> 'a -> 'a
val fold_edge : (int -> int -> 'a -> 'a) -> t -> 'a -> 'a
val scc : (int * int) list -> int list list

val topological_sort :
  eq:('b -> 'b -> bool) -> key_of:('a -> 'b) -> edges:('b * 'b) list -> 'a list -> 'a list list

val topological_sort_flatten :
  eq:('b -> 'b -> bool) -> key_of:('a -> 'b) -> edges:('b * 'b) list -> 'a list -> 'a list
