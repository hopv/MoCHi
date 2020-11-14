open Ref_type

val generate_check :
  Syntax.typ option ->
  ?make_fail:(Syntax.typ -> Syntax.term) ->
  (t * (Syntax.id * Syntax.term)) list ->
  (t * (Syntax.id * Syntax.term)) list ->
  Syntax.id ->
  t ->
  (t * (Syntax.id * Syntax.term)) list *
  (t * (Syntax.id * Syntax.term)) list *
  Syntax.term

val generate :
  Syntax.typ option ->
  ?make_fail:(Syntax.typ -> Syntax.term) ->
  (t * (Syntax.id * Syntax.term)) list ->
  (t * (Syntax.id * Syntax.term)) list ->
  t ->
  (t * (Syntax.id * Syntax.term)) list *
  (t * (Syntax.id * Syntax.term)) list *
  Syntax.term
