open Syntax

val trans : term -> term * ((Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t)
