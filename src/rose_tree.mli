type 'a t = Node of 'a * 'a t list
type path = int list

val leaf : 'a -> 'a t
val decomp : 'a t -> 'a * 'a t list
val label : 'a t -> 'a
val children : 'a t -> 'a t list
val root : 'a t -> 'a
val flatten : 'a t -> 'a list
val map : (path -> 'a -> 'b) -> 'a t -> 'b t
val fold : ('a -> 'b list -> 'b) -> 'a t -> 'b
val for_all : ('a -> bool) -> 'a t -> bool
val exists : ('a -> bool) -> 'a t -> bool
val proj : path -> 'a t -> 'a t
val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
val update : path -> 'a t -> 'a t -> 'a t
val zip : 'a t -> 'b t -> ('a * 'b) t
val find_all_subtree : ('a t -> bool) -> 'a t -> 'a t list
val find_all_label : ('a -> bool) -> 'a t -> 'a list
val filter_map_subtree : ('a t -> 'b option) -> 'a t -> 'b list
val filter_map_label : ('a -> 'b option) -> 'a t -> 'b list
val is_leaf : 'a t -> bool
