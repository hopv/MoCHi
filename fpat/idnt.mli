(** Identifiers *)

(** {6 Constructors} *)

type t =
  | V of string
  | C of string
  | T of t * int * int
  | N of int (** for De Bruijn index *)

(** {6 Printers} *)

val pr : Format.formatter -> t -> unit
val pr_tex : Format.formatter -> t -> unit
val pr_list : Format.formatter -> t list -> unit

(** {6 Auxiliary constructors} *)

val make : string -> t
val mk_coeff : string -> t
val new_var : unit -> t
val new_list : int -> t list
val new_vmap : t list -> (t * t) list
val new_coeff : ?header:string -> unit -> t
val new_tvar : unit -> t
val new_pvar : unit -> t
val nu : (t -> 'a) -> 'a

(** {6 Inspectors} *)

val equiv : t -> t -> bool
val cong : t -> t -> bool
val lt : t -> t -> bool

val is_top : t -> bool
val is_pos : t -> bool
val is_neg : t -> bool
val is_coeff : t -> bool

val base : t -> string
val string_of : t -> string

(** {6 Operators} *)

val rename : (t * t) list -> t -> t
val rename_base : (string -> string) -> t -> t
val reset_uid : t -> t

(** @return the structured variables for
    the return value and arguments *)
val ret_args : t -> int -> int -> t * t list

(** {6 Serialization/deserialization} *)

val serialize : t -> string
val deserialize : string -> t
