open Syntax
open Ref_type

val generate_check :
  typ_exn:typ option ->
  ?make_fail:(typ -> term) ->
  genv:(t * (id * term)) list ->
  cenv:(t * (id * term)) list ->
  id ->
  t ->
  (t * (id * term)) list * (t * (id * term)) list * term

val generate :
  typ_exn:typ option ->
  ?make_fail:(typ -> term) ->
  genv:(t * (id * term)) list ->
  cenv:(t * (id * term)) list ->
  t ->
  (t * (id * term)) list * (t * (id * term)) list * term

val add_assert_assume : ?annot:(term -> term) -> bool -> term -> t -> term
