(** [lift t] returns lambda-lifting of [t]
    unused variables also abstracted *)
val lift : CEGAR_syntax.prog -> CEGAR_syntax.prog

(** [lift2 t] returns lambda-lifting of [t]
    only used variables are abstracted *)
val lift2 : CEGAR_syntax.prog -> CEGAR_syntax.prog
