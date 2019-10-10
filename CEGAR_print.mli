
(** Pretty printer for CEGAR language *)

val const : Format.formatter -> CEGAR_syntax.const -> unit
val fun_def :
  Format.formatter ->
  CEGAR_syntax.var * CEGAR_syntax.var list * CEGAR_syntax.t *
  CEGAR_syntax.event list * CEGAR_syntax.t -> unit
val term : Format.formatter -> CEGAR_syntax.t -> unit
val term' : Format.formatter -> CEGAR_syntax.t -> unit
val var : Format.formatter -> CEGAR_syntax.var -> unit
val typ : Format.formatter -> CEGAR_syntax.typ -> unit
val typ_base : Format.formatter -> CEGAR_type.base -> unit
val ce : Format.formatter -> int list -> unit
val env : Format.formatter -> CEGAR_syntax.env -> unit
val attr : Format.formatter -> CEGAR_syntax.attr list -> unit
val prog : Format.formatter -> CEGAR_syntax.prog -> unit
val prog_typ : Format.formatter -> CEGAR_syntax.prog -> unit
val prog_ML : Format.formatter -> CEGAR_syntax.prog -> unit

val string_of_const : CEGAR_syntax.const -> string

val env_diff : Format.formatter -> CEGAR_syntax.env -> unit
