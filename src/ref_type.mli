
type t =
  | Base of Type.base * Syntax.id * Syntax.term
  | Fun of Syntax.id * t * t
  | Tuple of (Syntax.id * t) list
  | Inter of Syntax.typ * t list
  | Union of Syntax.typ * t list
  | ExtArg of Syntax.id * t * t
  | List of Syntax.id * Syntax.term * Syntax.id * Syntax.term * t
  | Constr of Type.path * t list * Syntax.id * Syntax.term
  | Variant of (Type.constr * t list) list
  | Record of (Type.label * (Type.mutable_flag * t)) list
  | Exn of t * t

module Env : Menv.ENV with type key := Syntax.id with type value := t
type env = Env.t
module NegEnv : Menv.ENV with type key := Syntax.id with type value := t
type neg_env = NegEnv.t


(** {1 Constructor} *)
val _Inter : Syntax.typ -> t list -> t
val _Union : Syntax.typ -> t list -> t
val _ExtArg : Syntax.id -> t -> t -> t
val typ_result : t
val inter : Syntax.typ -> t list -> t
val union : Syntax.typ -> t list -> t
val top : Syntax.typ -> t
val bottom : Syntax.typ -> t
val make_fun : t -> t -> t
val make_base : ?pred:Syntax.term -> Type.base -> t
val make_tuple : t list -> t
val make_ref : t -> t


(** {1 Destructor} *)
val decomp_base : t -> (Type.base * Syntax.id * Syntax.term) option
val decomp_fun : t -> (Syntax.id * t * t) option
val decomp_list : t -> (Syntax.id * Syntax.term * Syntax.id * Syntax.term * t) option
val decomp_inter : t -> t list
val decomp_funs : t -> (Syntax.id * t) list * t
val decomp_funs_n : int -> t -> (Syntax.id * t) list * (Syntax.id * t) list * t
val arg_num : t -> int

val is_base : t -> bool
val is_fun : t -> bool
val is_list : t -> bool
val is_top' : t -> bool
val is_bottom' : t -> bool
val has_inter_union : t -> bool


(** {1 Transformation} *)
val make_trans : ?tr:Syntax.Tr.t -> ((t -> t) -> t -> t option) -> t -> t
val simplify : t -> t
val remove_subtype : ?sub:(t -> t -> bool) -> t list -> t list
val remove_equiv : t list -> t list
val contract : t -> t
val map_pred : (Syntax.term -> Syntax.term) -> t -> t
val replace_base_with_int : t -> t
val replace_list_with_int : t -> t
val replace_constr_with_int : t -> t
val replace_constr_with_int_but_exn : Type.path list -> t -> t
val replace_abst_with_int : t -> t

(** {1 Translator} *)
val of_simple : Syntax.typ -> t
val to_simple : ?with_pred:bool -> t -> Syntax.typ
val to_abst_typ : ?decomp_pred:bool -> ?with_pred:bool -> t -> Syntax.typ


(** {1 Printer} *)
val print : Format.formatter -> t -> unit


(** {1 Generator} *)
val make_strongest : Syntax.typ -> t
val make_weakest : Syntax.typ -> t


(** {1 Substitution} *)
val subst : Syntax.id -> Syntax.term -> t -> t
val subst_map : (Syntax.id * Syntax.term) list -> t -> t
val subst_var : Syntax.id -> Syntax.id -> t -> t
val subst_rev : Syntax.term -> Syntax.id -> t -> t
val subst_constr : ?force:bool -> Type.path -> t -> t -> t


(** {1 Misc} *)
val flatten : t -> t
val occur : Syntax.id -> t -> bool
val replace_term : Syntax.term -> Syntax.term -> t -> t
val rename : ?full:bool -> t -> t
val set_base_var : Syntax.id -> t -> t
val copy_fun_arg_to_base : t -> t
val same : t -> t -> bool
val has_no_predicate : t -> bool
val subtype : t -> t -> bool
val suptype : t -> t -> bool
val equiv : t -> t -> bool
val split_inter : t -> t list
val is_safe_fun : t -> bool
val col_constr : t -> Type.path list

module Ty : sig
  val result : t
  val unit : ?pred:Syntax.term -> unit -> t
  val bool : ?pred:Syntax.term -> unit -> t
  val int : ?pred:Syntax.term -> unit -> t
  val base : ?pred:Syntax.term -> Type.base -> t
  val fun_ : t -> t -> t
  val tuple : t list -> t
  val ( * ) : t -> t -> t
  val ref : t -> t
end

(* ppx_deriving show *)
val pp : Format.formatter -> t -> unit
