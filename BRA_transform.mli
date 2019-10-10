(***** Constants *****)

val hole_term : Syntax.term

(***** Functions *****)

val everywhere_expr : (Syntax.term -> Syntax.term) -> Syntax.term -> Syntax.term

val remove_unit_wraping : Syntax.term -> Syntax.term
val lambda_lift : Syntax.term -> Syntax.term
val regularization : Syntax.term -> Syntax.term

val show_term : ?top:bool -> Syntax.term -> string
val retyping : Syntax.term -> Syntax.typ list -> (Parsetree.toplevel_phrase list * Syntax.term)

val extract_id : Syntax.term -> Syntax.id

val to_holed_programs : Syntax.term (* target program *) -> BRA_types.holed_program list (* holed transformed program *)

val callsite_split : BRA_types.holed_program -> BRA_types.holed_program list

(* construct linear lexicographic ranking function *)
val construct_LLRF : BRA_types.predicate_info -> Syntax.term
val separate_to_CNF : Syntax.term -> Syntax.term list

(* plug holed program with predicate *)
val pluging : BRA_types.holed_program -> Syntax.term -> Syntax.term
