open Syntax

val abst_var : id
val abst_var_int : id
val abst_var_bool : id

val typ_result : typ
val typ_event : typ
val typ_event' : typ
val typ_event_cps : typ
val typ_exn : typ

val make_attr : ?attrs:attr list -> term list -> attr list

(** {6 Term constructor} *)
val end_of_definitions : term
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
val make_int : int -> term
val make_string : string -> term
val make_rand : typ -> term
val make_rand_unit : typ -> term
val make_rand_cps : typ -> term
val make_randint_cps : bool -> term
val make_app : term -> term list -> term
val make_app_raw : term -> term list -> term (** Does not merge arguments *)
val make_fail : ?loc:Location.t -> ?force:bool -> typ -> term
val make_local : declaration -> term -> term
val make_let : (id * term) list -> term -> term
val make_let_s : (id * term) list -> term -> term
val make_lets : (id * term) list -> term -> term
val make_lets_s : (id * term) list -> term -> term
val make_let' : term -> (id -> term) -> term
val make_let_type : (string * typ) list -> term -> term
val make_lets_type : (string * typ) list -> term -> term
val make_nonrec_let_s : (id * term) list -> term -> term
val make_nonrec_lets_s : (id * term) list -> term -> term
val make_fun : id -> term -> term
val make_pure_fun : id -> term -> term
val make_funs : id list -> term -> term
val make_not : term -> term
val make_and : term -> term -> term
val make_ands : term list -> term
val make_or : term -> term -> term
val make_ors : term list -> term
val make_add : term -> term -> term
val make_sub : term -> term -> term
val make_mul : term -> term -> term
val make_div : term -> term -> term
val make_neg : term -> term
val make_if : term -> term -> term -> term
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
val make_fst : term -> term
val make_snd : term -> term
val make_pair : term -> term -> term
val make_tuple : term list -> term
val make_nil : typ -> term
val make_nil2 : typ -> term
val make_cons : term -> term -> term
val make_list : ?typ:typ -> term list -> term
val make_match : ?typ:typ -> term -> (pattern * term) list -> term
val make_single_match : ?total:bool -> term -> pattern -> term -> term
val make_seq : term -> term -> term
val make_ignore : term -> term
val make_assert : ?loc:Location.t -> ?force:bool -> term -> term
val make_assume : term -> term -> term
val make_label : ?label:string -> Syntax.info -> Syntax.term -> Syntax.term
val make_pany : typ -> pattern
val make_pvar : id -> pattern
val make_pconst : term -> pattern
val make_ppair : pattern -> pattern -> pattern
val make_ptuple : pattern list -> pattern
val make_pnil : typ -> pattern
val make_pnil2 : typ -> pattern
val make_pcons : pattern -> pattern -> pattern
val make_imply : term -> term -> term
val none_flag : term
val some_flag : term
val make_none : typ -> term
val make_some : term -> term
val make_is_none : term -> term
val make_is_some : term -> term
val make_get_val : term -> term
val make_tuple : term list -> term
val make_proj : int -> term -> term
val make_ref : term -> term
val make_deref : term -> term
val make_setref : term -> term -> term
val make_construct : string -> term list -> typ -> term
val make_record : (string * term) list -> typ -> term
val make_field : ?ty:typ -> term -> string -> term
val make_raise : term -> typ -> term
val make_trywith : term -> id -> (pattern * term) list -> term
val make_trywith_simple : term -> term -> term
val make_length_var : typ -> id
val make_length : term -> term
val new_var_of_term : term -> id
val new_var_of_pattern : pattern -> id
val make_module : declaration list -> term


(** {6 Term destructor / Inspector} *)
val decomp_assert : term -> (term * Location.t option) option
val decomp_and : term -> term list
val decomp_some : term -> term option
val decomp_is_none : term -> term option
val decomp_get_val : term -> term option
val decomp_lets : term -> (id * term) list list * term
val decomp_var : term -> id option
val decomp_bexp : term -> term list
val decomp_prog : term -> (id * term) list list * term
val decomp_list : term -> term list option
val decomp_decls : term -> declaration list * term
val decomp_type_decls : term -> ((string * typ) list) list * term
val var_of_term : term -> id
val int_of_term : term -> int
val bool_of_term : term -> bool
val pair_of_term : term -> term * term
val tuple_of_term : term -> term list
val list_of_term : term -> term list
val effect_of : term -> Type.effect list

val is_base_var : id -> bool
val is_fun_var : id -> bool
val is_list_literal : term -> bool
val is_var : term -> bool
val is_const : term -> bool
val is_fail : term -> bool
val is_randint_unit : term -> bool
val is_randbool_unit : term -> bool
val is_none : term -> bool
val is_fun : term -> bool
val is_app : term -> bool
val is_value : term -> bool
val is_simple_aexp : term -> bool
val is_simple_bexp : term -> bool
val is_id_unique : term -> bool
val is_bottom_def : id -> Syntax.term -> bool

val get_int : term -> int list
val get_top_funs : term -> id list
val get_top_rec_funs : term -> id list
val get_fv : ?eq:(id -> id -> bool) -> term -> id list
val get_id : term -> int
val get_id_option : term -> int option
val get_id_map : term -> (int, term) Hashtbl.t
val get_last_definition : term -> (id * term) list
val get_body : term -> term
val get_max_var_id : term -> int
val col_same_term : term -> term -> term list
val col_info_id : term -> id list
val col_id : term -> int list
val col_tid : typ -> (string * int) list
val col_typ_var : term -> typ option ref list
val col_app_args : id -> term -> term list list

val has_event : term -> bool
val has_pnondet : pattern -> bool
val has_safe_attr : term -> bool
val has_pure_attr : term -> bool

(** {6 Substitution} *)
val subst : ?rename_if_captured:bool -> ?fast:bool -> id -> term -> term -> term
val subst_int : int -> term -> term -> term
val subst_map : (id * term) list -> term -> term
val subst_type : ?fast:bool -> id -> term -> typ -> typ
val subst_type_var : id -> id -> typ -> typ
val subst_decl : ?fast:bool -> id -> term -> declaration -> declaration
val subst_decl_map : (id * term) list -> declaration -> declaration
val subst_var : ?fast:bool -> id -> id -> term -> term
val subst_var_map : (id * id) list -> term -> term
val subst_tdata : string -> typ -> term -> term
val subst_tdata_ca : string -> typ -> term -> term
val subst_tdata_typ : string -> typ -> typ -> typ
val subst_tdata_map : (string * typ) list -> term -> term
val subst_tdata_typ_map : (string * typ) list -> typ -> typ
val subst_tdata_with_copy : string -> typ -> term -> term
val subst_var_without_typ : id -> id -> term -> term
val subst_var_map_without_typ : (id * id) list -> term -> term

(** {6 Utilities for Types} *)
val merge_typ : typ -> typ -> typ
val add_tapred : id -> term list -> typ -> typ
val arg_num : typ -> int
val is_poly_typ : typ -> bool
val get_tdata : typ -> string list
val get_tapred : typ -> (id * term list) option
val get_args : typ -> id list
val get_argvars : typ -> id list
val get_argtyps : typ -> typ list
val get_opt_typ : typ -> typ
val opt_typ : typ -> typ
val effect_of_typ : typ -> Type.effect list
val copy_for_pred_share : bool -> typ -> typ * typ
val get_pred_share : typ -> (int list * int list list * int list) list

(** {6 Misc} *)
val subst_rev : ?check_capture:bool -> term -> id -> term -> term
val replace_term : term -> term -> term -> term
val max_pat_num : term -> int
val has_no_effect : term -> bool
val same_term : term -> term -> bool
val same_term' : term -> term -> bool
val var_name_of_term : term -> string
val var_name_of_pattern : pattern -> string
val var_of_term : term -> id
val make_term : typ -> term
val occur_in : id -> term -> bool
val count_occurrence : id -> term -> int
val add_attr : attr -> term -> term
val add_attrs : attr list -> term -> term
val add_comment : string -> term -> term
val add_id : int -> term -> term
val replace_id : int -> int -> term -> term
val remove_attr : attr -> term -> term
val from_fpat_term : Fpat.Term.t -> term
val from_fpat_formula : Fpat.Formula.t -> term
val find_exn_typ : term -> typ option
val find_fixed_args : id -> id list -> term -> id list
val trans_if : (term -> term option) -> term -> term
val rename : (id * id) list -> term -> term
val rename_pat : (id * id) list -> pattern -> pattern
val set_id_counter_to_max : term -> unit
val is_length_var : id -> bool
val size : term -> int

module Term : sig
  val unit : term
  val tt : term
  val true_ : term
  val ff : term
  val false_ : term
  val fail : term
  val randi : term
  val randb : term
  val rand : typ -> term
  val bot : typ -> term
  val eod : term
  val var : id -> term
  val vars : id list -> term list
  val int : int -> term
  val bool : bool -> term
  val string : string -> term
  val (@) : term -> term list -> term
  val (@@) : term -> term list -> term
  val let_ : (id * term) list -> term -> term
  val let_s : (id * term) list -> term -> term
  val lets : (id * term) list -> term -> term
  val fun_ : id -> term -> term
  val pfun : id -> term -> term
  val funs : id list -> term -> term
  val not : term -> term
  val (&&) : term -> term -> term
  val ands : term list -> term
  val (||) : term -> term -> term
  val ors : term list -> term
  val (+) : term -> term -> term
  val (-) : term -> term -> term
  val ( * ) : term -> term -> term
  val (/) : term -> term -> term
  val (~-) : term -> term
  val if_ : term -> term -> term -> term
  val br : term -> term -> term
  val brs : term list -> term
  val (=) : term -> term -> term
  val (<>) : term -> term -> term
  val (<) : term -> term -> term
  val (>) : term -> term -> term
  val (<=) : term -> term -> term
  val (>=) : term -> term -> term
  val (<|) : term -> binop -> term -> term
  val (|>) : (term -> term) -> term -> term
  val fst : term -> term
  val snd : term -> term
  val pair : term -> term -> term
  val tuple : term list -> term
  val proj : int -> term -> term
  val nil : term Type.t -> term
  val cons : term -> term -> term
  val list : ?typ:typ -> term list -> term
  val seq : term -> term -> term
  val seqs : term list -> term -> term
  val ignore : term -> term
  val assert_ : ?loc:Location.t -> ?force:bool -> term -> term
  val assume : term -> term -> term
  val none : typ -> term
  val some : term -> term
  val ref : term -> term
  val match_ : ?typ:typ -> term -> (pattern * term) list -> term
  val local : declaration -> term -> term
  val module_ : declaration list -> term
  val length : term -> term
  val (|->) : id -> term -> term -> term
end

module Pat : sig
  val __ : typ -> pattern
  val const : term -> pattern
  val unit : pattern
  val int : int -> pattern
  val bool : bool -> pattern
  val true_ : pattern
  val false_ : pattern
  val var : id -> pattern
  val pair : pattern -> pattern -> pattern
  val tuple : pattern list -> pattern
  val nil : typ -> pattern
  val nil2 : typ -> pattern
  val cons : pattern -> pattern -> pattern
  val when_ : pattern -> term -> pattern
end
