(** CPS-transformation for CEGAR-lang. *)

val trans : CEGAR_syntax.prog -> bool -> CEGAR_syntax.prog
(** [trans b t] Translates [t] into a CPS term．
    The original program is treated as a call-by-value term.
    If [t] does not have a simple type, it raises exception [Typing.CannotUnify].
*)
