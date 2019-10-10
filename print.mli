open Syntax

type config =
    {ty : bool; (** print types of arguments *)
     as_ocaml : bool; (** print terms in OCaml syntax *)
     for_dmochi : bool; (** print terms for dmochi when as_ocaml=true *)
     top : bool; (** print let/type as in top-level *)
     unused : bool; (** print unused arguments *)
     depth : int} (** max depth of printing terms *)

val config_default : config ref

val set_as_ocaml : unit -> unit
val set_unused : unit -> unit
val set_depth : int -> unit

val typ : Format.formatter -> typ -> unit
val id : Format.formatter -> id -> unit
val id_typ : Format.formatter -> id -> unit
val pattern : Format.formatter -> pattern -> unit
val const : Format.formatter -> const -> unit
val desc : Format.formatter -> desc -> unit
val term : Format.formatter -> term -> unit
val term_top : Format.formatter -> term -> unit
val term' : Format.formatter -> term -> unit
val term_typ : Format.formatter -> term -> unit
val term_typ_top : Format.formatter -> term -> unit
val defs : Format.formatter -> (id * (id list * term)) list -> unit
val constr : Format.formatter -> term -> unit
val attr : Format.formatter -> attr list -> unit
val decls : Format.formatter -> declaration list -> unit
val as_ocaml : Format.formatter -> term -> unit
val as_ocaml_typ : Format.formatter -> term -> unit
val term_custom : config -> Format.formatter -> term -> unit

val int : Format.formatter -> int -> unit
val float : Format.formatter -> float -> unit
val char : Format.formatter -> char -> unit
val bool : Format.formatter -> bool -> unit
val string : Format.formatter -> string -> unit
val option : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit
val pair : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'b -> unit) -> Format.formatter -> ('a * 'b) -> unit
val ( * ) : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'b -> unit) -> Format.formatter -> ('a * 'b) -> unit
val triple : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'b -> unit) -> (Format.formatter -> 'c -> unit) -> Format.formatter -> ('a * 'b * 'c) -> unit
val list : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val ignore : string -> Format.formatter -> 'a -> unit
val __ : Format.formatter -> 'a -> unit

val string_of_const : const -> string
val string_of_binop : binop -> string
val string_of_typ : typ -> string
