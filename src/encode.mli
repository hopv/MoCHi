open Syntax

val mutable_record : Problem.t -> Problem.t
(** Encode mutable record as record with references *)

val record : Problem.t -> Problem.t
(** Encode record as tuple *)

val enum_variant : Problem.t -> Problem.t
(** Encode simple variant as integer *)

val nonrec_variant : Problem.t -> Problem.t
(** Encode simple variant as integer *)

val list : Problem.t -> Problem.t * Trans.make_get_rtyp_single
(** Encode list as function *)

val recdata : Problem.t -> Problem.t
(** Encode recursive data as function *)

val array : Problem.t -> Problem.t
(** Encode recursive data as function with reference *)

val abst_ref : Problem.t -> Problem.t
(** Abstract away content of reference *)

val abst_obj : Problem.t -> Problem.t
(** Abstract away content of objects *)

val option : Problem.t -> Problem.t
(** Encode option types as pairs *)

val lazy_ : Problem.t -> Problem.t
(** Encode lazy as function *)

val all : Problem.t -> Problem.t
val typ_of : (Problem.t -> Problem.t) -> typ -> typ
val abst_rec_record : Problem.t -> Problem.t
val abst_poly_comp : Problem.t -> Problem.t
val ignore_data_arg : term -> term
val ignore_exn_arg : term -> term
val ignore_rec_exn_arg : term -> term
val ignore_exn_fun_arg : term -> term
val ignore_mutual_data_arg : term -> term
