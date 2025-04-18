open Syntax

type get_rtyp = id -> Ref_type.t
type make_get_rtyp = get_rtyp list -> get_rtyp
type make_get_rtyp_single = get_rtyp -> get_rtyp
type attr_info += Removed of (id * term) list
type attr_info += Replaced of term
type attr_info += Inserted of string

(** {1 Transformation} *)

val flatten_tvar : term -> term
val flatten_tvar_typ : typ -> typ
val instansiate_tvar : typ -> term -> unit
val instansiate_tvar_typ : typ -> typ -> unit
val get_tvars : typ -> typ option ref list
val copy_poly_values : term -> (id * id) list * (id -> id -> bool) * term * make_get_rtyp_single

val define_rand :
  (typ * id) list * (id * term) list -> typ -> ((typ * id) list * (id * term) list) * term

val instansiate_randval : term -> term
val ref_to_assert : ?make_fail:(typ -> term) -> ?typ_exn:typ -> Ref_type.env -> term -> term
val replace_main : ?force:bool -> main:term -> term -> term
val map_main : (term -> term) -> term -> term
val set_main : term -> term * lid option
val set_main_for : ?force:bool -> lid list -> term -> term option * term
val part_eval : term -> term
val trans_let : term -> term
val propagate_typ_arg : term -> term
val replace_typ : (id * typ) list -> term -> term
val eval : term -> term
val elim_fun : term -> term
val make_ext_env : term -> (id * typ) list

val init_base_rand : term -> term
(** replace rand_int() with a fresh variable*)

val inlined_f : id list -> term -> term
val lift_fst_snd : term -> term
val expand_let_val : term -> term
val insert_param_funarg : term -> term
val rename_ext_funs : id list -> term -> id list * term
val rename_target_ext_funs : (id * (string * id)) list -> term -> term
val make_ext_funs : ?annot:bool -> ?fvs:id list -> (id * Ref_type.t) list -> term -> term
val assoc_typ : id -> term -> typ
val diff_terms : term -> term -> (desc * desc) list
val remove_label : ?label:string -> term -> term
val alpha_rename : ?whole:bool -> ?set_counter:bool -> term -> term
val alpha_rename_if : (id -> bool) -> term -> term
val replace_base_with_int : term -> term
val replace_list_with_int : term -> term
val replace_data_with_int : term -> term
val replace_data_with_int_but : typ list -> term -> term
val replace_exn_with_int : term -> term
val replace_complex_data_with_int : term -> term
val replace_abst_with_int : term -> term
val replace_poly_variant_with_int : term -> term
val replace_bottom_def : term -> term
val merge_bound_var_typ : (id * typ) list -> term -> term
val recover_const_attr : term -> term
val recover_const_attr_shallowly : term -> term
val subst_with_rename : ?check:bool -> id -> term -> term -> term
val ignore_non_termination : term -> term
val decomp_var_match_tuple : term -> term
val map_typ : (typ -> typ) -> term -> term
val map_attr : (attr list -> attr list) -> term -> term
val map_tattr : (tattr list -> tattr list) -> term -> term
val filter_attr : (attr -> bool) -> term -> term
val split_assert : term -> (term * Location.t option) list
val split_assert_and : term -> term
val add_id : term -> int * term
val add_id_if : (term -> bool) -> term -> int * term
val remove_id : term -> term
val remove_tid : string -> term -> term
val replace_fail : by:desc -> term -> term
val replace_fail_with_bot : ?except:int list -> term -> term
val remove_defs : id list -> term -> term
val subst_let_xy : term -> term
val remove_type_decl : term -> term

val lift_type_decl : term -> term
(** also remove type extension *)

val mark_free_as_external : term -> term
val map_var : (id -> id) -> term -> term
val split_mutual_rec : ?only_top:bool -> term -> term
val encode_bool_as_int : term -> term
val remove_unambiguous_id : term -> term
val replace_typ_result_with_unit : term -> term
val rename_for_ocaml : term -> term
val remove_tattr : term -> term
val reduce_rand : ?annot:bool -> term -> term
val reduce_ignore : term -> term
val reduce_branch : term -> term
val remove_obstacle_type_attribute_for_pred_share : term -> term
val add_occurence_param : term -> term
val add_def_of_free_types : term -> term
val add_ref_check : (id * Ref_type.t) list -> term -> term

(** {1 Abstractions} *)

val abst_magic : term -> term
(** Abstract functions that use Obj.magic *)

val abst_ext_recdata : term -> term
(** Abstract recursive data types defined externally into integers *)

val abstract_exn : term -> term
val abst_literal : term -> term
val abst_poly_variant : term -> term
val abst_menhir : term -> term

(** {1 Normalization} *)

val normalize_binop_exp : binop -> term -> term -> desc
val normalize_bool_exp : term -> term
val normalize_let : ?is_atom:(term -> bool) -> term -> term
val merge_geq_leq : term -> term
val null_tuple_to_unit : term -> term
val reconstruct : term -> term
val short_circuit_eval : term -> term
val flatten_let : term -> term
val tfuns_to_tfun : term -> term
val tfun_to_tfuns : term -> term
val flatten_tuple : term -> term
val decomp_pair_eq : term -> term
val eta_normal : term -> term
val direct_from_CPS : term -> term
val name_read_int : term -> term
val complete_precord : term -> term
val instansiate_weak_poly_types : term -> term
val instansiate_poly_types_with_env : (id * typ) list -> term -> term
val instansiate_matched_poly : term -> unit
val set_length_typ : term -> term
val top_def_to_funs : term -> term
val set_to_primitive : term -> term
val make_bind_for_PAlias : ?force:bool -> term -> term

(** {1 Simplification, Inlining, Reduction} *)

val simplify_if_cond : term -> term

val elim_unused_let :
  ?leave_last:bool ->
  (* If this is true, "main" in "let main ... = ... in ()" will not be deleted
     [Default: false] *)
  ?cbv:bool ->
  (* If this is false, terms with side-effects may also be removed
     [Default: true] *)
  ?elim_may_div:bool ->
  (* If this is true, may-divergent terms may also be removed
     [Default: true]*)
  ?annot:bool ->
  (* If this is true, annotations for generating counterexamples are added
     [Default: false]*)
  term ->
  term (* does not support modules *)

val elim_unused_branch : term -> term
val inline_no_effect : term -> term
val inline_var : term -> term
val inline_var_const : term -> term
val inline_simple_exp : term -> term
val inline_next_redex : term -> term
val inline_specified : id * id list * term -> term -> term
val beta_no_effect_tuple : term -> term
val beta_var_tuple : term -> term
val beta_reduce_trivial : term -> term
val beta_affine_fun : term -> term
val beta_size1 : term -> term
val beta_reduce : term -> term
val beta_no_effect : term -> term
val reduce_bottom : term -> term
val reduce_fail_unit : term -> term
val remove_no_effect_trywith : term -> term
val bool_eta_reduce : term -> term
val eta_tuple : term -> term
val eta_reduce : term -> term
val elim_redundant_arg : term -> term
val split_let : term -> term
val remove_effect_attribute : term -> term
val inline_record_type : term -> term
val inline_type_decl : term -> term
val inline_simple_types : term -> type_decl list * term
val inline_exn_type : term -> term
val remove_var_let : term -> term
val split_type_decls : term -> term
val insert_extra_param : term -> term
val unify_pure_fun_app : term -> term
val lift_assume : term -> term
val elim_singleton_tuple : term -> term
val lift_pwhen : term -> term
val variant_args_to_tuple : ?do_decomp:bool -> term -> term
val split_by_ref_type : (id * Ref_type.t) list -> term -> ((id * Ref_type.t) option * term) list

val set_assert_ref_typ :
  ?catch_all:(term -> term) -> id -> Ref_type.t -> term -> (id * Ref_type.t) list * term

val merge_deref : term -> term option
val abst_div : term -> term
val copy_poly_type : term -> term
val inline_type_alias : term -> term
val inline_ext_rebind : term -> term

val trans_match_with_recover_pat_bv :
  tr_desc_rec:(desc -> desc) -> tr_typ:(typ -> typ) -> term -> term

val remove_tpoly : term -> term
val inline_tvar : term -> term
val reduce_trivial_branch : term -> term
val remove_info_removed : term -> term
val remove_info_replaced : term -> term
val remove_info_inserted : term -> term
val remove_info_trans : term -> term
val remove_unused_exception : term -> term
val remove_unused_type_decl : term -> term
val reduce_external : id list -> term -> term
val merge_branch : term -> term

(** {1 Simplification, Inlining, Reduction for [match] expressions} *)

val remove_pnondet : term -> term
val remove_peval : term -> term
val simplify_match : term -> term
val remove_match : term -> term
val decompose_match : term -> term
val remove_unused_palias : term -> term
val remove_dummy : term -> term
val remove_por : term -> term

(** {1 Utilities} *)

val recover_pat_bv :
  tr_typ:(typ -> typ) -> before:pattern * 'a -> after:pattern * term -> pattern * term
