exception Ref_type_not_found

val use_simplification : bool ref

val check : Ref_type.Env.t -> Syntax.term -> Ref_type.t -> bool
val print : out_channel -> Ref_type.Env.t -> Syntax.term -> Ref_type.t -> unit
