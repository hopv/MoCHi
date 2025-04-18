open Syntax

type attr_info += String of string
type attr_info += Id of id
type attr_info += Term of term
type attr_info += Label of string * attr_info

val abst_var : id
val abst_var_int : id
val abst_var_bool : id
val make_attr : ?attrs:attr list -> term list -> attr list

val end_of_definitions : term
(** {1 Term constructor} *)

val unit_term : term
val true_term : term
val false_term : term
val cps_result : term
val fail_term : term
val fail_term_cps : term
val randint_term : term
val randbool_unit_term : term
val randint_unit_term : term
val make_fail_unit : Location.t option -> term
val make_bool : bool -> term
val make_bottom : typ -> term
val make_event : string -> term
val make_event_unit : string -> term
val make_event_cps : string -> term
val make_var : id -> term
val make_var_lid : ?typ:typ -> lid -> term
val make_int : int -> term
val make_string : string -> term
val make_use_var : id -> term -> term
val make_use_lid : lid -> term -> term
val make_use : term -> term -> term
val make_rand : typ -> term
val make_rand_unit : ?expand:bool -> ?use:bool -> typ -> term
val make_rand_cps : typ -> term
val make_randint_cps : bool -> term
val make_app : ?env:env -> term -> term list -> term
val make_app_raw : term -> term list -> term (* Does not merge arguments *)
val make_fail : ?loc:Location.t -> ?force:bool -> typ -> term
val make_local : declaration -> term -> term
val make_locals : declaration list -> term -> term
val make_let : (id * term) list -> term -> term
val make_let_s : (id * term) list -> term -> term
val make_lets : (id * term) list -> term -> term
val make_lets_s : (id * term) list -> term -> term
val make_let' : ?subst_if_var:bool -> term -> (lid -> term) -> term
val make_let_type : type_decls -> term -> term
val make_lets_type : type_decl list -> term -> term
val make_nonrec_let : (id * term) list -> term -> term
val make_nonrec_lets : (id * term) list -> term -> term
val make_nonrec_let_s : (id * term) list -> term -> term
val make_nonrec_lets_s : (id * term) list -> term -> term
val make_let_subst_if_var : id -> term -> term -> term
val make_fun : id -> term -> term
val make_pure_fun : id -> term -> term
val make_funs : id list -> term -> term

val make_function :
  partial:bool -> loc:Warnings.loc -> ?ty_arg:typ -> ty_ret:typ -> (pattern * term) list -> term

val make_not : term -> term
val make_and : term -> term -> term
val make_ands : term list -> term
val make_or : term -> term -> term
val make_ors : term list -> term
val make_add : term -> term -> term
val make_sub : term -> term -> term
val make_mul : term -> term -> term
val make_div : term -> term -> term
val make_safe_div : ?loc:Warnings.loc -> term -> term -> term
val make_neg : term -> term
val make_if : ?typ:typ -> term -> term -> term -> term
val make_br : term -> term -> term
val make_brs : term list -> term
val make_eq : term -> term -> term
val make_eq_dec : term -> term -> term
val make_neq : term -> term -> term
val make_lt : term -> term -> term
val make_gt : term -> term -> term
val make_leq : term -> term -> term
val make_geq : term -> term -> term
val make_binop : binop -> term -> term -> term
val make_fst : ?typ:typ -> term -> term
val make_snd : ?typ:typ -> term -> term
val make_pair : term -> term -> term
val make_tuple : term list -> term
val make_nil : elem_typ:typ -> term
val make_nil2 : list_typ:typ -> term
val make_cons : term -> term -> term
val make_list : ?typ:typ -> term list -> term
val make_match : ?typ:typ -> term -> (pattern * term) list -> term
val make_single_match : ?total:bool -> term -> pattern -> term -> term
val make_seq : term -> term -> term
val make_ignore : term -> term
val make_assert : ?loc:Location.t -> ?force:bool -> term -> term
val make_assume : term -> term -> term
val make_label : ?label:string -> attr_info -> term -> term
val make_pany : typ -> pattern
val make_pvar : id -> pattern
val make_pconst : term -> pattern
val make_pnondet : typ -> pattern
val make_ppair : pattern -> pattern -> pattern
val make_ptuple : pattern list -> pattern
val make_pnil : elem_typ:typ -> pattern
val make_pnil2 : list_typ:typ -> pattern
val make_pcons : pattern -> pattern -> pattern
val make_plazy : pattern -> pattern
val make_peval : id -> term -> pattern -> pattern
val make_psome : pattern -> pattern
val make_pwhen : pattern -> term -> pattern
val make_palias : pattern -> id -> pattern
val make_por : pattern -> pattern -> pattern
val make_imply : term -> term -> term
val none_flag : term
val some_flag : term
val make_lazy : term -> term
val make_forall : id -> term -> term
val make_exists : id -> term -> term
val make_none : elem_typ:typ -> term
val make_none2 : opt_typ:typ -> term
val make_some : term -> term
val make_none_enc : typ -> term
val make_some_enc : term -> term
val make_is_none_enc : term -> term
val make_is_some_enc : term -> term
val make_get_val : term -> term
val make_tuple : term list -> term
val make_proj : int -> term -> term
val make_ref : term -> term
val make_deref : ?typ:typ -> term -> term
val make_setref : term -> term -> term
val make_construct : ?poly:bool -> Type.path -> term list -> typ -> term
val make_record : (label * term) list -> typ -> term
val make_field : ?ty:typ -> term -> label -> term
val make_raise : typ:typ -> term -> term
val make_trywith : term -> id -> (pattern * term) list -> term
val make_trywith_handler : term -> term -> term
val make_length_var : typ -> id
val make_length : term -> term
val new_var_of_term : term -> id
val new_var_of_pattern : pattern -> id
val make_module : ?typ:typ -> ?env:(unit Id.t * Syntax.typ) list -> declaration list -> term
val make_pack : term -> typ -> term
val make_unpack : ?typ:typ -> term -> term
val make_mem : term -> term -> term
val make_addset : term -> term -> term
val make_subset : term -> term -> term
val make_left : term -> typ -> term
val make_right : typ -> term -> term
val make_is_left : term -> term
val make_get_left : term -> term
val make_get_right : term -> term
val make_either_ty : typ -> typ -> typ
val make_dummy : typ -> term

(** {1 Term destructor / Inspector} *)

val decomp_assert : term -> (term * Location.t option) option
val decomp_and : term -> term list
val decomp_or : term -> term list
val decomp_some_enc : term -> term option
val decomp_is_none_enc : term -> term option
val decomp_get_val : term -> term option
val decomp_lets : term -> (id * term) list list * term
val decomp_bexp : term -> term list
val decomp_prog : term -> (id * term) list list * term
val decomp_list : term -> term list option
val decomp_decls : term -> declaration list * term
val decomp_type_decls : term -> (Type.constr * (typ list * typ)) list list * term
val var_of_term : term -> id
val int_of_term : term -> int
val bool_of_term : term -> bool
val pair_of_term : term -> term * term
val tuple_of_term : term -> term list
val list_of_term : term -> term list
val effect_of : term -> Type.effect list
val decomp_label : ?label:string -> term -> attr_info list * term
val assoc_label : ?label:string -> term -> attr_info list
val remove_label : ?label:string -> term -> term
val is_base_var : id -> bool
val is_fun_var : id -> bool
val is_list_literal : term -> bool
val is_fail : term -> bool
val is_rand_unit : ?deep:bool -> term -> bool
val is_randint_unit : term -> bool
val is_randbool_unit : term -> bool
val is_none_enc : term -> bool
val is_fun : term -> bool
val is_value : term -> bool
val is_simple_aexp : term -> bool
val is_simple_bexp : term -> bool
val is_bottom_def : id -> term -> bool
val is_recursive_module_decl : declaration -> bool
val get_int : term -> int list
val get_top_funs : term -> id list
val get_id : term -> int
val get_id_option : term -> int option
val get_id_map : term -> (int, term) Hashtbl.t
val get_last_definition : term -> (lid * term) list
val get_main : term -> term
val get_max_var_id : term -> int
val get_fv_all : term -> id list

val split_type_decl_and_body :
  ?force:bool -> term -> (Type.constr * (typ list * typ)) list list * term

val col_same_term : term -> term -> term list
val col_info_id : term -> id list
val col_id : term -> int list
val col_tid : typ -> (string * int) list
val col_typ_var : term -> typ option ref list
val col_app_args : lid -> term -> term list list
val col_type_decl : term -> (Type.constr * (typ list * typ)) list list

(*val col_free_tconstr : term -> string list*)
val col_raise : term -> Type.path option list
val col_constr_path_in_term : term -> Type.path list
val col_constr_in_term : term -> Type.constr list
val col_poly_constr : term -> Type.constr list
val col_exn_constr : term -> (Type.path * [ `Used of typ list | `Rebind ]) list
val col_exn_decl : term -> (Type.path * [ `Decl of typ list | `Rebind of Type.path ]) list
val col_modules : term -> id list
val has_event : term -> bool
val has_raise : ?target:string list -> term -> bool
val has_pnondet : pattern -> bool
val has_pwhen : pattern -> bool
val has_safe_attr : term -> bool
val has_pure_attr : term -> bool
val has_deref : term -> bool
val use_try_raise : term -> bool
val has_fail : term -> bool
val has_fun : term -> bool
val assoc_info : term -> attr_info list

val subst : ?b_ty:bool -> id -> term -> term -> term
(** {1 Substitution} *)

val subst_map : (id * term) list -> term -> term
val subst_type : ?b_ty:bool -> id -> term -> typ -> typ
val subst_type_var : id -> id -> typ -> typ
val subst_decl : ?b_ty:bool -> id -> term -> declaration -> declaration
val subst_decl_map : (id * term) list -> declaration -> declaration
val subst_var : id -> id -> term -> term
val subst_var_map : (id * id) list -> term -> term
val subst_tconstr : Type.tconstr -> typ list * typ -> term -> term
val subst_tconstr_typ : Type.tconstr -> typ list * typ -> typ -> typ
val subst_tconstr_map : (Type.tconstr * (typ list * typ)) list -> term -> term
val subst_tconstr_map_typ : (Type.tconstr * (typ list * typ)) list -> typ -> typ
val subst_tconstr_label_map : (Type.tconstr * Type.tconstr) list -> term -> term
val subst_tconstr_label_map_typ : (Type.tconstr * Type.tconstr) list -> typ -> typ
val subst_tconstr_with_copy : Type.tconstr -> typ list * typ -> term -> term

val subst_var_without_typ :
  id -> lid -> term -> term (* does not change types except when the targets are modules *)

val subst_var_map_without_typ :
  lid IdMap.t -> term -> term (* does not change simple types except when the targets are modules *)

val subst_constr :
  Type.path -> Type.path -> term -> term (* does not substitute constructors in types *)

val subst_constr_map : (Type.path * Type.path) list -> term -> term
val subst_field : Type.label -> Type.label -> term -> term
val subst_field_map : (Type.label * Type.label) list -> term -> term
val subst_decls : id -> term -> declaration list -> declaration list
val subst_map_decls : (id * term) list -> declaration list -> declaration list
val subst_var_map_decls : (id * id) list -> declaration list -> declaration list

val subst_tconstr_map_decls :
  (Type.tconstr * (typ list * typ)) list -> declaration list -> declaration list

val subst_field_map_decls : (Type.label * Type.label) list -> declaration list -> declaration list
val subst_constr_map_decls : (Type.path * Type.path) list -> declaration list -> declaration list

(** {1 Utilities for Types} *)

val merge_typ : typ -> typ -> typ
val add_tapred : id -> term list -> typ -> typ
val arg_num : typ -> int
val is_poly_typ : typ -> bool
val is_weak_poly_typ : typ -> bool
val get_tconstr : term -> (Type.path * typ list) list
val get_tconstr_typ : typ -> (Type.path * typ list) list
val get_tapred : typ -> (id * term list) option
val get_args : typ -> id list
val get_argvars : typ -> id list
val get_argtyps : typ -> typ list
val get_opt_typ_enc : typ -> typ
val opt_typ_enc : typ -> typ
val effect_of_typ : typ -> Type.effect list
val copy_for_pred_share : bool -> typ -> typ * typ
val get_pred_share : typ -> (int list * int list list * int list) list
val get_fv_typ : typ -> unit Id.t list
val get_fv_typ' : typ -> id list

(** {1 Misc} *)

val subst_rev : ?check_capture:bool -> term -> id -> term -> term
val replace_term : term -> term -> term -> term
val max_pat_num : term -> int
val has_no_effect : term -> bool
val same_term : term -> term -> bool
val same_term' : term -> term -> bool
val var_name_of_term : term -> string
val var_name_of_pattern : pattern -> string
val var_of_term : term -> lid
val make_default_term : typ -> term
val occur_in : id -> term -> bool
val count_occurrence : id -> term -> int
val add_attrs : ?force:bool -> attr list -> term -> term
val merge_attrs : attr list -> term -> term
val add_comment : string -> term -> term
val add_id : int -> term -> term
val replace_id : int -> int -> term -> term
val filter_attr : (attr -> bool) -> term -> term
val filter_out_attr : (attr -> bool) -> term -> term
val remove_attr_if : (attr -> bool) -> term -> term
val remove_attr : attr -> term -> term
val from_fpat_term : Fpat.Term.t -> term
val from_fpat_formula : Fpat.Formula.t -> term
val find_exn_typ : term -> typ option
val find_fixed_args : lid -> lid list -> term -> lid list
val trans_if : (term -> term option) -> term -> term
val trans_if_desc : (desc -> desc option) -> term -> term
val rename : (id * id) list -> term -> term
val rename_pat : (id * id) list -> pattern -> pattern
val set_id_counter_to_max : term -> unit
val is_length_var : lid -> bool
val size : term -> int
val has_type_decl : term -> bool
val set_mark : term -> unit
val add_mark : term -> term
val can_unify : ?env:env -> ?sub:bool -> ?ignore_poly_variant:bool -> typ -> typ -> bool
val can_unify_multi : ?env:env -> typ list -> bool
val copy_tvar : ?env:(typ option ref * typ) list -> term -> (typ option ref * typ) list * term

val copy_tvar_list :
  ?env:(typ option ref * typ) list -> term list -> (typ option ref * typ) list * term list

val catch_all : typ -> term -> term
val make_catch_all : term -> term -> term
val trans_decl_as_term : (term -> term) -> declaration -> declaration
val trans_decls_as_term : (term -> term) -> declaration list -> declaration list
val trans_typ_as_term : (term -> term) -> typ -> typ
val has_module : term -> bool
val add_to_env : declaration -> env -> env
val make_decl_trans : (declaration -> declaration list) -> term -> term
val get_free_types : term -> (Type.path * int) list
val gen_fresh_name_var : ?postfix:string -> id list -> id -> id
val gen_fresh_name_var_int : 'a Id.t list -> 'a Id.t -> 'a Id.t
val is_exn_free : term -> bool
val sig_items_of_decl : ?env:term Type.mod_env -> Syntax.declaration -> term Type.signature

module Term : sig
  val unit : term
  val tt : term
  val true_ : term
  val ff : term
  val false_ : term
  val fail : term
  val randi : term
  val randb : term
  val rand : ?expand:bool -> ?use:bool -> typ -> term
  val bot : typ -> term
  val eod : term
  val var : id -> term
  val vars : id list -> term list
  val var_lid : ?typ:typ -> lid -> term
  val int : int -> term
  val bool : bool -> term
  val string : string -> term
  val ( @ ) : term -> term list -> term
  val ( @@ ) : term -> term list -> term
  val type_ : type_decls -> term -> term
  val let_ : (id * term) list -> term -> term
  val let_s : (id * term) list -> term -> term
  val lets : (id * term) list -> term -> term
  val lets_s : (id * term) list -> term -> term
  val let_nonrec : (id * term) list -> term -> term
  val fun_ : id -> term -> term
  val pfun : id -> term -> term
  val funs : id list -> term -> term
  val not : term -> term
  val ( && ) : term -> term -> term
  val ands : term list -> term
  val ( || ) : term -> term -> term
  val ors : term list -> term
  val ( => ) : term -> term -> term
  val ( + ) : term -> term -> term
  val ( - ) : term -> term -> term
  val ( * ) : term -> term -> term
  val ( / ) : term -> term -> term
  val ( ~- ) : term -> term
  val if_ : term -> term -> term -> term
  val br : term -> term -> term
  val ( |+| ) : term -> term -> term
  val brs : term list -> term
  val ( = ) : term -> term -> term
  val ( <> ) : term -> term -> term
  val ( < ) : term -> term -> term
  val ( > ) : term -> term -> term
  val ( <= ) : term -> term -> term
  val ( >= ) : term -> term -> term
  val ( <| ) : term -> binop -> term -> term
  val ( |> ) : (term -> term) -> term -> term
  val fst : ?typ:typ -> term -> term
  val snd : ?typ:typ -> term -> term
  val pair : term -> term -> term
  val tuple : term list -> term
  val proj : int -> term -> term
  val nil : elem_typ:term Type.t -> term
  val nil2 : list_typ:term Type.t -> term
  val cons : term -> term -> term
  val list : ?typ:typ -> term list -> term
  val seq : term -> term -> term
  val seqs : term list -> term -> term
  val ignore : term -> term
  val assert_ : ?loc:Location.t -> ?force:bool -> term -> term
  val assume : term -> term -> term
  val none : elem_typ:typ -> term
  val none2 : opt_typ:typ -> term
  val some : term -> term
  val left : term -> typ -> term
  val right : typ -> term -> term
  val is_left : term -> term
  val get_left : term -> term
  val get_right : term -> term
  val field : ?ty:typ -> term -> label -> term
  val ref : term -> term
  val deref : ?typ:typ -> term -> term
  val ( ! ) : ?typ:typ -> term -> term
  val ( := ) : term -> term -> term
  val constr : ?poly:bool -> Type.path -> term list -> typ -> term
  val match_ : ?typ:typ -> term -> (pattern * term) list -> term
  val local : declaration -> term -> term
  val locals : declaration list -> term -> term
  val type_ext : term Type.ext -> term -> term
  val module_ : ?typ:typ -> ?env:(unit Id.t * Syntax.typ) list -> declaration list -> term
  val pack : term -> typ -> term
  val unpack : ?typ:typ -> term -> term
  val length : term -> term
  val raise : typ:typ -> term -> term
  val try_ : term -> id -> (pattern * term) list -> term
  val trywith : term -> id -> (pattern * term) list -> term
  val trywith_h : term -> term -> term
  val ( |-> ) : id -> term -> term -> term
  val empty : typ -> term
  val mem : term -> term -> term
  val addset : term -> term -> term
  val subset : term -> term -> term
  val lazy_ : term -> term
  val forall : id list -> term -> term
  val exists : id list -> term -> term
  val dummy : typ -> term
  val record : (label * term) list -> typ -> term
end

module Pat : sig
  val __ : typ -> pattern
  val any : typ -> pattern
  val const : term -> pattern
  val nondet : typ -> pattern
  val unit : pattern
  val int : int -> pattern
  val bool : bool -> pattern
  val true_ : pattern
  val false_ : pattern
  val var : id -> pattern
  val pair : pattern -> pattern -> pattern
  val ( * ) : pattern -> pattern -> pattern
  val tuple : pattern list -> pattern
  val nil : elem_typ:typ -> pattern
  val nil2 : list_typ:typ -> pattern
  val cons : pattern -> pattern -> pattern
  val list : ?elem_typ:typ -> ?list_typ:typ -> pattern list -> pattern
  val when_ : pattern -> term -> pattern
  val lazy_ : pattern -> pattern
  val eval : id -> term -> pattern -> pattern
  val alias : pattern -> id -> pattern
  val some : pattern -> pattern
  val or_ : pattern -> pattern -> pattern
  val ( || ) : pattern -> pattern -> pattern
end

module PredVar : sig
  val pvar_name : string
  val is_pvar : id -> bool
  val new_pvar : ?name:string -> ?id:int -> typ list -> id
end

module Eq : sig
  include module type of Util.Eq

  val id : 'a Id.t -> 'a Id.t -> bool
  val typ : 'a Type.t -> 'a Type.t -> bool
  val path : Type.path -> Type.path -> bool
end

module Tenv : sig
  include module type of struct
    include Tenv
  end

  val add_decl : ?prefix:Type.path -> declaration -> term t -> term t
end
