val lift :
  ?args:Syntax.id list ->
  Syntax.term ->
  ((Syntax.typ Id.t * (Syntax.id list * Syntax.term)) list * Syntax.term)
  * (Syntax.typ Id.t -> Ref_type.t -> Ref_type.t)
(** [lift t] returns lambda-lifting of [t].
    the definitions of let expressions must be side-effect free *)

val lift' :
  ?args:Syntax.id list ->
  Syntax.term ->
  ((Syntax.typ Id.t * (Syntax.id list * Syntax.term)) list * Syntax.term)
  * (Syntax.typ Id.t -> Ref_type.t -> Ref_type.t)
(** Lambda lifting for preprocess of termination mode *)
