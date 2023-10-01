open Syntax

type config =
    {ty : bool;         (** print types of arguments *)
     as_ocaml : bool;   (** print terms in OCaml syntax *)
     for_dmochi : bool; (** print terms for dmochi when as_ocaml=true *)
     top : bool;        (** print let/type as in top-level *)
     unused : bool;     (** print unused arguments *)
     depth : int;       (** max depth of printing terms *)
     length : int;      (** max depth of printing terms *)
     omit_id : id list} (** variables whose names are unique *)

val config_default : config ref

(** {1 Printer settings} *)
val set_as_ocaml : unit -> unit
val set_unused : unit -> unit
val set_depth : int -> unit
val set_length : int -> unit

(** {1 Printers of types/terms} *)
val location : Format.formatter -> Location.t -> unit
val typ : Format.formatter -> typ -> unit
val lid : Format.formatter -> lid -> unit
val lid_typ : Format.formatter -> lid -> unit
val id : Format.formatter -> id -> unit
val id_typ : Format.formatter -> id -> unit
val pattern : Format.formatter -> pattern -> unit
val pattern' : Format.formatter -> pattern -> unit
val const : Format.formatter -> const -> unit
val desc : Format.formatter -> desc -> unit
val term : Format.formatter -> term -> unit
val term_top : Format.formatter -> term -> unit
val term' : Format.formatter -> term -> unit
val term_typ : Format.formatter -> term -> unit
val term_typ_top : Format.formatter -> term -> unit
val defs : Format.formatter -> (id * (id list * term)) list -> unit
val desc_constr : Format.formatter -> desc -> unit
val constr : Format.formatter -> Type.constr -> unit
val attr : Format.formatter -> attr list -> unit
val type_decls : Format.formatter -> type_decls -> unit
val decls : Format.formatter -> declaration list -> unit
val as_ocaml : Format.formatter -> term -> unit
val as_ocaml_typ : Format.formatter -> term -> unit
val term_custom : config -> Format.formatter -> term -> unit
val params : Format.formatter -> params -> unit
val env : Format.formatter -> env -> unit
val label : Format.formatter -> Type.label -> unit
val constr : Format.formatter -> Type.constr -> unit
val tconstr : Format.formatter -> Type.tconstr -> unit
val path : Format.formatter -> Type.path -> unit

(** {1 General printers} *)
val int : Format.formatter -> int -> unit
val float : Format.formatter -> float -> unit
val char : Format.formatter -> char -> unit
val bool : Format.formatter -> bool -> unit
val string : Format.formatter -> string -> unit
val option : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit
val pair : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'b -> unit) -> Format.formatter -> ('a * 'b) -> unit
val ( * ) : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'b -> unit) -> Format.formatter -> ('a * 'b) -> unit
val triple : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'b -> unit) -> (Format.formatter -> 'c -> unit) -> Format.formatter -> ('a * 'b * 'c) -> unit
val list : ?limit:int -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val ignore : ?str:string -> Format.formatter -> 'a -> unit
val __ : Format.formatter -> 'a -> unit
val (|>) : ('a -> 'b) -> (Format.formatter -> 'b -> unit) -> Format.formatter -> 'a -> unit
val (<|) : (Format.formatter -> 'b -> unit) -> ('a -> 'b) -> Format.formatter -> 'a -> unit

(** {1 Translator for string} *)
val string_of_constr : desc -> string
val string_of_const : const -> string
val string_of_binop : binop -> string
val string_of_typ : typ -> string

module T : module type of Print_typ
