open Syntax

val trans : term -> term * ((Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t)
val make_fun_tuple : term -> term
