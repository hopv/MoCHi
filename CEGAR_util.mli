open CEGAR_syntax

type ext_path_part = Positive | Negative | Do_not_Care
type ext_path = ext_path_part list

exception TypeBottom
exception Type_not_found of var

val type_not_found : var -> 'a

val map_body_def : (t -> t) -> fun_def -> fun_def
val map_body_prog : (t -> t) -> prog -> prog
val map_def_prog : (fun_def -> fun_def) -> prog -> prog

val const_of_bool : bool -> const
val subst : var -> t -> t -> t
val subst_var : var -> var -> t -> t
val subst_map : (var * t) list -> t -> t
val subst_typ : var -> t -> typ -> typ
val subst_typ_map : (var * t) list -> typ -> typ
val arg_num : typ -> int
val pop_main : prog -> prog
val get_arg_env : typ -> var list -> (var * typ) list
val put_arg_into_if : prog -> prog
val eta_expand_def : env -> fun_def -> fun_def
val eta_expand : prog -> prog
val get_const_typ : env -> const -> typ
val get_typ : env -> t -> typ
val get_arg_num : typ -> int
val has_bottom : t -> bool
val normalize_bool_term : ?imply:(t list -> t -> bool) -> t -> t
val get_non_rec : (t -> t) -> prog -> (var * t) list
val print_prog_typ' : var list -> Format.formatter -> prog -> unit
val eval_step_by_step : prog -> 'a
val initialize_env : prog -> prog
val has_no_effect : t -> bool
val get_renv : prog -> (int * env) list
val assoc_renv : int -> env -> typ
val mem_assoc_renv : int -> env -> bool
val assign_id_to_rand : prog -> prog
val decomp_rand_typ : ?xs:t list option -> typ -> typ list * (t -> t list)
val make_map_randint_to_preds : prog -> (int * (t -> t list)) list
val arrange_ext_preds_sequence : ('a * 'b) list -> ('a * 'b list) list
val conv_path : ('a * bool list list) list -> ('a * ext_path_part list list) list
val merge_similar_paths : ('a * 'b * 'c * ('d * ext_path_part list list) list) list -> ('a * 'b * 'c * ('d * ext_path_part list list) list) list
val group_by_same_branching : ('a * 'b * 'c * 'd) list -> ('a * 'b * 'c * 'd) list list
val inlined_functions : prog -> var list
val elim_same_arg : prog -> prog (* BUGGY *)
val rename_fun_arg : prog -> prog

module Term : sig
  val (@) : t -> t list -> t
  val (@@) : t -> t list -> t
  val unit : t
  val true_ : t
  val tt : t
  val false_ : t
  val ff : t
  val int : int -> t
  val var : var -> t
  val vars : var list -> t list
  val let_ : var -> t -> t -> t
  val fun_ : var -> ?typ:typ -> t -> t
  val br : t -> t -> t
  val if_ : t -> t -> t -> t
  val (<) : t -> t -> t
  val (>) : t -> t -> t
  val (<=) : t -> t -> t
  val (>=) : t -> t -> t
  val (&&) : t -> t -> t
  val (||) : t -> t -> t
  val (+) : t -> t -> t
  val (-) : t -> t -> t
  val ( * ) : t -> t -> t
  val (/) : t -> t -> t
  val (|->) : var -> t -> t -> t
end
