open Syntax

(** {6 Transformation} *)
val flatten_tvar : term -> term
val flatten_tvar_typ : typ -> typ
val inst_tvar : typ -> term -> term
val inst_tvar_typ : typ -> typ -> typ
val get_tvars : typ -> typ option ref list
val rename_poly_funs : id -> term -> (id * id) list * term
val copy_poly_funs : term -> term * ((Syntax.id -> Ref_type.t) -> Syntax.id -> Ref_type.t)
val define_rand : ((typ * id) list * (id * term) list) -> typ -> ((typ * id) list * (id * term) list) * term
val inst_randval : term -> term
val ref_to_assert : ?make_fail:(typ -> term) -> ?typ_exn:typ -> Ref_type.env -> term -> term
val replace_main : ?force:bool -> main:term -> term -> term
val map_main : (term -> term) -> term -> term
val set_main : term -> term
val part_eval : term -> term
val trans_let : term -> term
val propagate_typ_arg : term -> term
val replace_typ : (Syntax.id * Syntax.typ) list -> term -> term
val eval : term -> term
val elim_fun : term -> term
val make_ext_env : term -> env
val init_base_rand : term -> term (** replace rand_int() with a fresh variable*)
val inlined_f : id list -> term -> term
val lift_fst_snd : term -> term
val expand_let_val : term -> term
val insert_param_funarg : term -> term
val rename_ext_funs : id list -> term -> id list * term
val make_ext_funs : ?fvs:(id list) -> (id * Ref_type.t) list -> term -> term
val assoc_typ : id -> term -> typ
val diff_terms : term -> term -> (term * term) list
val remove_label : ?label:string -> term -> term
val alpha_rename : ?whole:bool -> ?set_counter:bool -> term -> term
val alpha_rename_if : (id -> bool) -> term -> term
val replace_base_with_int : term -> term
val replace_data_with_int : term -> term
val replace_complex_data_with_int : term -> term
val remove_top_por : term -> term
val replace_bottom_def : term -> term
val merge_bound_var_typ : (id * typ) list -> term -> term
val recover_const_attr : term -> term
val recover_const_attr_shallowly : term -> term
val subst_with_rename : ?check:bool -> id -> term -> term -> term
val ignore_non_termination : term -> term
val decomp_var_match_tuple : term -> term
val map_attr : (attr list -> attr list) -> term -> term
val map_tattr : (tattr list -> tattr list) -> term -> term
val filter_attr : (attr -> bool) -> term -> term
val split_assert : term -> (term * Location.t option) list
val split_assert_and : term -> term
val add_id : term -> int * term
val add_id_if : (term -> bool) -> term -> int * term
val remove_id : term -> term
val remove_tid : string -> term -> term
val replace_fail_with : desc -> term -> term
val remove_defs : id list -> term -> term
val subst_let_xy : term -> term
val ignore_exn_arg : term -> term
val abst_ext_recdata : term -> term
val col_type_decl : term -> (string * typ) list list
val remove_type_decl : term -> term
val lift_type_decl : term -> term
val mark_fv_as_external : term -> term
val map_id : (id -> id) -> term -> term
val split_mutual_rec : ?only_top:bool -> term -> term
val get_set_main : term -> id option
val abst_literal : term -> term
val encode_bool_as_int : term -> term
val remove_unambiguous_id : term -> term
val replace_typ_result_with_unit : term -> term
val rename_for_ocaml : term -> term
val remove_tattr : term -> term
val reduce_rand : term -> term
val reduce_ignore : term -> term
val reduce_branch : term -> term
val rename_module : id -> id -> term -> term
val remove_obstacle_type_attribute_for_pred_share : term -> term
val add_occurence_param : term -> term

(** {6 Normalization} *)
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
val instansiate_poly_types : term -> term
val set_length_typ : term -> term

(** {6 Simplification, Inlining, Reduction} *)
val simplify_match : term -> term
val simplify_if_cond : term -> term
val elim_unused_let : ?leave_last:bool -> ?cbv:bool -> term -> term
val elim_unused_branch : term -> term
val inline_no_effect : term -> term
val inline_var : term -> term
val inline_var_const : term -> term
val inline_simple_exp : term -> term
val inline_next_redex : term -> term
val inline_specified : (id * id list * term) -> term -> term
val inline_module_var : term -> term
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
val extract_module : term -> term
val inline_record_type : term -> term
val inline_type_decl : term -> term
val inline_simple_types : term -> term
val remove_id_let : term -> term
val split_type_decls : term -> term
val insert_extra_param : term -> term
val unify_pure_fun_app : term -> term
val lift_assume : term -> term
val elim_singleton_tuple : term -> term
val lift_pwhen : term -> term
val decompose_match : term -> term
val variant_args_to_tuple : ?do_decomp:bool -> term -> term
