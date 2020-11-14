type 'a t = Leaf of 'a | Node of 'a t * 'a t
type path = int list

val root : 'a t -> 'a
val flatten : 'a t -> 'a list
val map : (path -> 'a -> 'b) -> 'a t -> 'b t
val fold : ('a -> 'a -> 'a) -> ('b -> 'a) -> 'b t -> 'a
val proj : path -> 'a t -> 'a t
val update : path -> 'a t -> 'a t -> 'a t
val for_all : ('a -> bool) -> 'a t -> bool
val exists : ('a -> bool) -> 'a t -> bool
val zip : 'a t -> 'b t -> ('a * 'b) t

val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
