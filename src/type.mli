type base =
  | TUnit
  | TBool
  | TInt
  | TPrim of string
and 'a t =
  | TBase of base
  | TVar of 'a t option ref * int
  | TFun of 'a t Id.t * 'a t
  | TFuns of 'a t Id.t list * 'a t (* Just for fair-termination *)
  | TTuple of 'a t Id.t list
  | TData of string
  | TVariant of bool * (string * 'a t list) list (** true means polymorphic variant *)
  | TRecord of (string * (mutable_flag * 'a t)) list
  | TApp of string * 'a t list
  | TAttr of 'a attr list * 'a t
  | TModule of 'a signature
and mutable_flag = Immutable | Mutable
and 'a attr =
  | TAPred of 'a t Id.t * 'a list (* TAPred occur at most ones *)
  | TAPredShare of int
  | TARefPred of 'a t Id.t * 'a (* TARefPred occur at most ones *)
  | TAPureFun
  | TAEffect of effect list
  | TAId of string * int
  | TARaise of 'a t
and effect = EVar of int | EEvent | ENonDet | EDiv | EExcep
and 'a signature =
  {sig_types: 'a declaration;
   sig_values: 'a t Id.t list}
and 'a declaration = (string * 'a t) list

exception CannotUnify

val new_tvar : unit -> 'a t

val label_pred_share : string

val prim_base_types : string list

val is_fun_typ : 'a t -> bool
val is_base_typ : 'a t -> bool
val is_tuple_typ : 'a t -> bool
val data_occurs : string -> 'a t -> bool
val eq : 'a t -> 'a t -> bool
val same_shape : 'a t -> 'a t -> bool
val is_instance_of : ?strict:bool -> 'a t -> 'a t -> bool
val has_pred : 'a t -> bool
val is_mutable_record : 'a t -> bool
val is_tvar : 'a t -> bool
val occurs : 'a t option ref -> 'a t -> bool
val set_print_as_ocaml : unit -> unit
val tmp_set_print_as_ocaml : (unit -> 'a) -> 'a
val is_raise_tfun : 'a t -> bool

val typ_unknown : 'a t
val elim_tattr : 'a t -> 'a t
val tfuns_to_tfun : 'a t -> 'a t
val elim_tattr_all : 'a t -> 'a t
val elim_tid : string -> 'a t -> 'a t
val flatten : 'a t -> 'a t
val unify : ?for_check:bool -> ?tenv:('a declaration) -> 'a t -> 'a t -> unit
val app_typ : 'a t -> 'b list -> 'a t
val to_id_string : 'a t -> string
val order : 'a t -> int
val arity : 'a t -> int
val var_name_of : 'a t -> string
val remove_arg_at : int -> 'a t -> 'a t
val filter_map_attr : ('a attr -> 'a attr option) -> 'a t -> 'a t
val map_attr : ('a attr -> 'a attr) -> 'a t -> 'a t

val types_in_signature : 'a signature -> 'a declaration
val types_in_module : ?add_prefix:bool -> 'a t Id.t -> 'a declaration
val fields_in_declaration : 'a declaration -> string list
val fields_in_signature : 'a signature -> string list
val fields_in_module : ?add_prefix:bool -> 'a t Id.t -> string list
val constrs_in_declaration : 'a declaration -> string list
val constrs_in_signature : 'a signature -> string list
val constrs_in_module : ?add_prefix:bool -> 'a t Id.t -> string list
val values_in_signature : ?extract_module:bool -> 'a signature -> 'a t Id.t list
val values_in_module : ?add_prefix:bool -> ?extract_module:bool -> 'a t Id.t -> 'a t Id.t list

(** {6 destructor} *)

val decomp_base : 'a t -> base option
val decomp_tfun : 'a t -> 'a t Id.t list * 'a t
val decomp_tfuns : 'a t -> 'a t Id.t list * 'a t
val tuple_num : 'a t -> int option
val proj_typ : int -> 'a t -> 'a t
val fst_typ : 'a t -> 'a t
val snd_typ : 'a t -> 'a t
val ref_typ : 'a t -> 'a t
val list_typ : 'a t -> 'a t
val option_typ : 'a t -> 'a t
val array_typ : 'a t -> 'a t
val set_typ : 'a t -> 'a t
val arg_var : 'a t -> 'a t Id.t
val result_typ : 'a t -> 'a t
val decomp_tvariant : 'a t -> bool * (string * 'a t list) list
val decomp_ttuple : 'a t -> 'a t list
val decomp_trecord : 'a t -> (string * (mutable_flag * 'a t)) list
val decomp_tattr : 'a t -> 'a attr list * 'a t
val decomp_tmodule : 'a t -> 'a signature
val decomp_tdata : 'a t -> string
val decomp_raise_tfun : 'a t -> ('a t * 'a t Id.t * 'a t) option

(** {6 Type constructor} *)

val _TFun : 'a t Id.t -> 'a t -> 'a t
val _TAttr : 'a attr list -> 'a t -> 'a t
val pureTFun : ('a t Id.t * 'a t) -> 'a t
val make_ttuple : 'a t list -> 'a t
val make_tpair : 'a t -> 'a t -> 'a t
val make_tfun : ?name:string -> 'a t -> 'a t -> 'a t
val make_ptfun : ?name:string -> 'a t -> 'a t -> 'a t
val make_tlist : 'a t -> 'a t
val make_tset : 'a t -> 'a t
val make_tref : 'a t -> 'a t
val make_toption : 'a t -> 'a t
val make_tarray : 'a t -> 'a t
val make_tconstr : string -> 'a t -> 'a t
val add_tattr: 'a attr -> 'a t -> 'a t


(** {6 Printers} *)

val print :
  ?occur:('a t Id.t -> 'a t -> bool) ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a t -> unit
val print_init : Format.formatter -> 'a t -> unit
val print_base : Format.formatter -> base -> unit
val print_effect : Format.formatter -> effect -> unit
val print_attr : Format.formatter -> 'a attr -> unit

(** ppx_deriving *)
val pp_base : Format.formatter -> base -> unit
val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
val pp_effect : Format.formatter -> effect -> unit
val pp_mutable_flag : Format.formatter -> mutable_flag -> unit


module Ty : sig
  val unit : 'a t
  val bool : 'a t
  val int : 'a t
  val prim : string -> 'a t
  val fun_ : ?name:string -> 'a t -> 'a t -> 'a t
  val funs : 'a t list -> 'a t -> 'a t
  val pfun : ?name:string -> 'a t -> 'a t -> 'a t
  val tuple : 'a t list -> 'a t
  val pair : 'a t -> 'a t -> 'a t
  val ( * ) : 'a t -> 'a t -> 'a t
  val list : 'a t -> 'a t
  val ref : 'a t -> 'a t
  val option : 'a t -> 'a t
  val array : 'a t -> 'a t
  val set : 'a t -> 'a t
end
