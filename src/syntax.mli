(** Syntax of intermediate language *)

type binop = Eq | Lt | Gt | Leq | Geq | And | Or | Add | Sub | Mult | Div
type typ = term Type.t
and tattr = term Type.attr
and id = typ Id.t
and lid =
  | LId of id
  | LDot of lid * string
  | LApp of lid * lid
and attr =
  | AAbst_under (** For disproving termination *)
  | ATerminate (** Terminating terms *)
  | ANotFail (** Safe terms *)
  | ADeterministic (** Deterministic terms *)
  | AComment of string (** Comments for test/debug *)
  | AId of int (** Unique id for specific transformations (This must be removed after a transformation) *)
  | ADoNotInline (** If this attribute is annotated to `Local ...`, the bindings should not be inlined *)
  | AEffect of Type.effect list (** The result of effect analysis *)
  | ALoc of Location.t (** Original location in the source code *)
  | AMark of bool ref (** Only for debugging *)
  | AInfo of info (** Temporal information for some transformations *)
  | AFV of id list (** Bag of free variables *)
and term = private {desc:desc; typ:typ; attr:attr list}
and const = (* only base type constants *)
  | Unit
  | True
  | False
  | Int of int
  | Char of char
  | String of string
  | Float of float
  | Int32 of int32
  | Int64 of int64
  | Nativeint of nativeint
  | CPS_result
  | Rand of typ * bool (** true denotes CPS-term *)
  | Empty
  | Dummy of typ
and desc =
  | End_of_definitions
  | Const of const
  | Var of lid
  | Fun of id * term
  | App of term * term list
  | If of term * term * term
  | Local of declaration * term
  | BinOp of binop * term * term
  | Not of term
  | Event of string * bool (** true denotes CPS-term *)
  | Record of (label * term) list
  | Field of term * label
  | SetField of term * label * term
  | Nil
  | Cons of term * term
  | Constr of bool * Type.path * term list (** true denotes polymorphic variant *)
  | Match of term * (pattern * term) list (** a term diverges if no patters are matched *)
  | Raise of term
  | TryWith of term * term
  | Tuple of term list
  | Proj of int * term
  | Bottom
  | Label of info * term (* TODO: move to attributes *)
  | Ref of term
  | Deref of term
  | SetRef of term * term
  | TNone
  | TSome of term
  | Lazy of term
  | Module of declaration list
  | Pack of term
  | Unpack of term
  | Forall of id * term
  | Exists of id * term
  | MemSet of term * term (** [MemSet(x,X)] means x \in X *)
  | AddSet of term * term (** [AddSet(x,X)] means {x} \cup X *)
  | Subset of term * term (** [Subset(X,Y)] means X \subseteq Y *)

and declaration =
  | Decl_let of (id * term) list   (** [let rec .. and ...] *)
  | Decl_type of type_decls        (** [type t = ... and ...] *)
  | Type_ext of extension          (** [type t += ...] and [exception A = B] *)
  | Include of term                (** [include t] *)
  | Decl_multi of declaration list (** Multiple declarations only for compositional transformation; implicitly removed by _Local *)

and label = Type.label

and extension = term Type.extension
and type_decls = term Type.declaration
and type_decl = term Type.decl_item

and params = typ list (* The type must be TVar *)

and info =
  | InfoInt of int
  | InfoString of string
  | InfoId of id
  | InfoTerm of term
  | InfoIdTerm of id * term


and type_kind =
  | KAbstract
  | KVariant of (string * typ list) list
  | KRecord of (string * (Type.mutable_flag * typ)) list
  | KOpen
and rec_flag = Nonrecursive | Recursive
and pattern = private {pat_desc:pat_desc; pat_typ:typ; pat_attr:pat_attr list}
and pat_desc =
  | PAny
  | PNondet (** match non-deterministically *)
  | PVar of id
  | PAlias of pattern * id
  | PConst of term
  | PConstr of bool * Type.path * pattern list (** true denotes polymorphic variant *)
  | PNil
  | PCons of pattern * pattern
  | PTuple of pattern list
  | PRecord of (label * pattern) list
  | PNone
  | PSome of pattern
  | POr of pattern * pattern
  | PWhen of pattern * term
  | PLazy of pattern
  | PEval of id * term * pattern
    (** (match v with PEval(x,t,p) -> t2) is reduced t2' if (match [v/x]t with p -> [v/x]t2) is reduced t2' *)
and pat_attr =
  | PAFV of id list
  | PABV of id list

and env = term Tenv.t

val _LId : id -> lid
val _LDot : lid -> string -> lid
val _LApp : lid -> lid -> lid

val _End_of_definitions : desc
val _Const : const -> desc
val _Var : lid -> desc
val _Fun : id -> term -> desc
val _App : term -> term list -> desc
val _If : term -> term -> term -> desc
val _Local : declaration -> term -> desc
val _BinOp : binop -> term -> term -> desc
val _Not : term -> desc
val _Event : string -> bool -> desc
val _Record : (label * term) list ->desc
val _Field : term -> label -> desc
val _SetField : term -> label -> term -> desc
val _Nil : desc
val _Cons : term -> term -> desc
val _Constr : bool -> Type.path -> term list -> desc
val _Match : term -> (pattern * term) list -> desc
val _Raise : term -> desc
val _TryWith : term -> term -> desc
val _Tuple : term list -> desc
val _Proj : int -> term -> desc
val _Bottom : desc
val _Label : info -> term -> desc
val _Ref : term -> desc
val _Deref : term -> desc
val _SetRef : term -> term -> desc
val _TNone : desc
val _TSome : term -> desc
val _Lazy : term -> desc
val _Module : declaration list ->desc
val _Pack : term -> desc
val _Unpack : term -> desc
val _MemSet : term -> term -> desc
val _AddSet : term -> term -> desc
val _Subset : term -> term -> desc
val _Forall : id -> term -> desc
val _Exists : id -> term -> desc

val _Decl_let : (id * term) list -> declaration
val _Decl_type : type_decls -> declaration
val _Type_ext : extension -> declaration

val _PAny : pat_desc
val _PNondet : pat_desc
val _PVar : id -> pat_desc
val _PAlias : pattern -> id -> pat_desc
val _PConst : term -> pat_desc
val _PConstr : bool -> Type.path -> pattern list -> pat_desc
val _PNil : pat_desc
val _PCons : pattern -> pattern -> pat_desc
val _PTuple : pattern list -> pat_desc
val _PRecord : (label * pattern) list ->pat_desc
val _PNone : pat_desc
val _PSome : pattern -> pat_desc
val _POr : pattern -> pattern -> pat_desc
val _PLazy : pattern -> pat_desc
val _PWhen : pattern -> term -> pat_desc
val _PEval : id -> term -> pattern -> pat_desc
val _PAFV : id list -> pat_attr
val _PABV : id list -> pat_attr

module Val : sig
  val _LId : lid -> id option
  val _Const : term -> const option
  val _Var : term -> lid option
  val _Fun : term -> (id * term) option
  val _App : term -> (term * term list) option
  val _If : term -> (term * term * term) option
  val _Local : term -> (declaration * term) option
  val _BinOp : term -> (binop * term * term) option
  val _Not : term -> term option
  val _Event : term -> (string * bool) option
  val _Record : term -> (label * term) list option
  val _Field : term -> (term * label) option
  val _SetField : term -> (term * label * term) option
  val _Cons : term -> (term * term) option
  val _Constr : term -> (bool * Type.path * term list) option
  val _Match : term -> (term * (pattern * term) list) option
  val _Raise : term -> term option
  val _TryWith : term -> (term * term) option
  val _Tuple : term -> term list option
  val _Proj : term -> (int * term) option
  val _Label : term -> (info * term) option
  val _Ref : term -> term option
  val _Deref : term -> term option
  val _SetRef : term -> (term * term) option
  val _TSome : term -> term option
  val _Lazy : term -> term option
  val _Module : term -> declaration list option
  val _Pack : term -> term option
  val _Unpack : term -> term option
  val _MemSet : term -> (term * term) option
  val _AddSet : term -> (term * term) option
  val _Subset : term -> (term * term) option
  val _Forall : term -> (id * term) option
  val _Exists : term -> (id * term) option

  val _Decl_let : declaration -> (id * term) list option
  val _Decl_type : declaration -> type_decls option
  val _Type_ext : declaration -> extension option

  val _PVar : pattern -> id option
  val _PAlias : pattern -> (pattern * id) option
  val _PConst : pattern -> term option
  val _PConstr : pattern -> (bool * Type.path * pattern list) option
  val _PCons : pattern -> (pattern * pattern) option
  val _PTuple : pattern -> pattern list option
  val _PRecord : pattern -> (label * pattern) list option
  val _PSome : pattern -> pattern option
  val _POr : pattern -> (pattern * pattern) option
  val _PWhen : pattern -> (pattern * term) option
  val _PEval : pattern -> (id * term * pattern) option
  val _PAFV : pat_attr -> id list option
  val _PABV : pat_attr -> id list option
end

module ValE : sig
  val _LId : lid -> id
  val _Const : term -> const
  val _Var : term -> lid
  val _Fun : term -> id * term
  val _App : term -> term * term list
  val _If : term -> term * term * term
  val _Local : term -> declaration * term
  val _BinOp : term -> binop * term * term
  val _Not : term -> term
  val _Event : term -> string * bool
  val _Record : term -> (label * term) list
  val _Field : term -> term * label
  val _SetField : term -> term * label * term
  val _Cons : term -> term * term
  val _Constr : term -> bool * Type.path * term list
  val _Match : term -> term * (pattern * term) list
  val _Raise : term -> term
  val _TryWith : term -> term * term
  val _Tuple : term -> term list
  val _Proj : term -> int * term
  val _Label : term -> info * term
  val _Ref : term -> term
  val _Deref : term -> term
  val _SetRef : term -> term * term
  val _TSome : term -> term
  val _Lazy : term -> term
  val _Module : term -> declaration list
  val _Pack : term -> term
  val _Unpack : term -> term
  val _MemSet : term -> term * term
  val _AddSet : term -> term * term
  val _Subset : term -> term * term
  val _Forall : term -> id * term
  val _Exists : term -> id * term

  val _Decl_let : declaration -> (id * term) list
  val _Decl_type : declaration -> type_decls
  val _Type_ext : declaration -> extension

  val _PVar : pattern -> id
  val _PAlias : pattern -> pattern * id
  val _PConst : pattern -> term
  val _PConstr : pattern -> bool * Type.path * pattern list
  val _PCons : pattern -> pattern * pattern
  val _PTuple : pattern -> pattern list
  val _PRecord : pattern -> (label * pattern) list
  val _PSome : pattern -> pattern
  val _POr : pattern -> pattern * pattern
  val _PWhen : pattern -> pattern * term
  val _PEval : pattern -> id * term * pattern
  val _PAFV : pat_attr -> id list
  val _PABV : pat_attr -> id list
end

module Is : sig
  val _LId : lid -> bool
  val _Const : term -> bool
  val _Var : term -> bool
  val _Fun : term -> bool
  val _App : term -> bool
  val _If : term -> bool
  val _Local : term -> bool
  val _BinOp : term -> bool
  val _Not : term -> bool
  val _Event : term -> bool
  val _Record : term -> bool
  val _Field : term -> bool
  val _SetField : term -> bool
  val _Cons : term -> bool
  val _Constr : term -> bool
  val _Match : term -> bool
  val _Raise : term -> bool
  val _TryWith : term -> bool
  val _Tuple : term -> bool
  val _Proj : term -> bool
  val _Label : term -> bool
  val _Ref : term -> bool
  val _Deref : term -> bool
  val _SetRef : term -> bool
  val _TSome : term -> bool
  val _Lazy : term -> bool
  val _Module : term -> bool
  val _Pack : term -> bool
  val _Unpack : term -> bool
  val _MemSet : term -> bool
  val _AddSet : term -> bool
  val _Subset : term -> bool
  val _Forall : term -> bool
  val _Exists : term -> bool

  val _PVar : pattern -> bool
  val _PAlias : pattern -> bool
  val _PConst : pattern -> bool
  val _PConstr : pattern -> bool
  val _PCons : pattern -> bool
  val _PTuple : pattern -> bool
  val _PRecord : pattern -> bool
  val _PSome : pattern -> bool
  val _POr : pattern -> bool
  val _PWhen : pattern -> bool
  val _PEval : pattern -> bool
  val _PAFV : pat_attr -> bool
  val _PABV : pat_attr -> bool
end

val tconstr_of_id : id -> Type.tconstr
val path_of_lid : lid -> Type.path
val lid_of_path : ?env:(unit Id.t * typ) list -> Type.path -> lid

module ID : sig
  type t = id
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end

module IdSet : Set.S with type elt = id
module IdMap : BatMap.S with type key = id

val safe_attr : attr list
val pure_attr : attr list
val const_attr : attr list

module Tr : sig
  type t =
    {mutable term:      term        -> term;
     mutable term_rec:  term        -> term;
     mutable desc:      desc        -> desc;
     mutable desc_rec:  desc        -> desc;
     mutable typ:       typ         -> typ;
     mutable typ_rec:   typ         -> typ;
     mutable var:       id          -> id;
     mutable lid:       lid         -> lid;
     mutable pat:       pattern     -> pattern;
     mutable pat_rec:   pattern     -> pattern;
     mutable info:      info        -> info;
     mutable info_rec:  info        -> info;
     mutable decl:      declaration -> declaration;
     mutable decl_rec:  declaration -> declaration;
     mutable const:     const       -> const;
     mutable const_rec: const       -> const;
     mutable attr:      attr list   -> attr list}

  val make : unit -> t
  val id : t
end

module Tr2 : sig
  type 'a t =
    {mutable term:      'a -> term        -> term;
     mutable term_rec:  'a -> term        -> term;
     mutable desc:      'a -> desc        -> desc;
     mutable desc_rec:  'a -> desc        -> desc;
     mutable typ:       'a -> typ         -> typ;
     mutable typ_rec:   'a -> typ         -> typ;
     mutable var:       'a -> id          -> id;
     mutable lid:       'a -> lid         -> lid;
     mutable pat:       'a -> pattern     -> pattern;
     mutable pat_rec:   'a -> pattern     -> pattern;
     mutable info:      'a -> info        -> info;
     mutable info_rec:  'a -> info        -> info;
     mutable decl:      'a -> declaration -> declaration;
     mutable decl_rec:  'a -> declaration -> declaration;
     mutable const:     'a -> const       -> const;
     mutable const_rec: 'a -> const       -> const;
     mutable attr:      'a -> attr list   -> attr list}
  val make : unit -> 'a t
  val to_Tr : 'a t -> 'a -> Tr.t
end

module Col : sig
  type 'a t =
    {mutable term:      term        -> 'a;
     mutable term_rec:  term        -> 'a;
     mutable desc:      desc        -> 'a;
     mutable desc_rec:  desc        -> 'a;
     mutable typ:       typ         -> 'a;
     mutable typ_rec:   typ         -> 'a;
     mutable var:       id          -> 'a;
     mutable lid:       lid         -> 'a;
     mutable pat:       pattern     -> 'a;
     mutable pat_rec:   pattern     -> 'a;
     mutable info:      info        -> 'a;
     mutable info_rec:  info        -> 'a;
     mutable decl:      declaration -> 'a;
     mutable decl_rec:  declaration -> 'a;
     mutable const:     const       -> 'a;
     mutable const_rec: const       -> 'a;
     mutable attr:      attr list   -> 'a;
     mutable app:       'a -> 'a -> 'a;
     mutable empty:     'a}
  val make : 'a -> ('a -> 'a -> 'a) -> 'a t
end

module Col2 : sig
  type ('a,'b) t =
    {mutable term:      'b -> term        -> 'a;
     mutable term_rec:  'b -> term        -> 'a;
     mutable desc:      'b -> desc        -> 'a;
     mutable desc_rec:  'b -> desc        -> 'a;
     mutable typ:       'b -> typ         -> 'a;
     mutable typ_rec:   'b -> typ         -> 'a;
     mutable var:       'b -> id          -> 'a;
     mutable lid:       'b -> lid         -> 'a;
     mutable pat:       'b -> pattern     -> 'a;
     mutable pat_rec:   'b -> pattern     -> 'a;
     mutable info:      'b -> info        -> 'a;
     mutable info_rec:  'b -> info        -> 'a;
     mutable decl:      'b -> declaration -> 'a;
     mutable decl_rec:  'b -> declaration -> 'a;
     mutable const:     'b -> const       -> 'a;
     mutable const_rec: 'b -> const       -> 'a;
     mutable attr:      'b -> attr list   -> 'a;
     mutable app:       'a -> 'a -> 'a;
     mutable empty:     'a}
  val make : 'a -> ('a -> 'a -> 'a) -> ('a,'b) t
end

module Iter : sig
  val make : unit -> unit Col.t
end

module Iter2 : sig
  val make : unit -> (unit,'b) Col2.t
end

module Tr_col2 : sig
  type ('a,'b) t =
    {mutable term:      'b -> term        -> 'a * term;
     mutable term_rec:  'b -> term        -> 'a * term;
     mutable desc:      'b -> desc        -> 'a * desc;
     mutable desc_rec:  'b -> desc        -> 'a * desc;
     mutable typ:       'b -> typ         -> 'a * typ;
     mutable typ_rec:   'b -> typ         -> 'a * typ;
     mutable var:       'b -> id          -> 'a * id;
     mutable lid:       'b -> lid         -> 'a * lid;
     mutable pat:       'b -> pattern     -> 'a * pattern;
     mutable pat_rec:   'b -> pattern     -> 'a * pattern;
     mutable info:      'b -> info        -> 'a * info;
     mutable info_rec:  'b -> info        -> 'a * info;
     mutable decl:      'b -> declaration -> 'a * declaration;
     mutable decl_rec:  'b -> declaration -> 'a * declaration;
     mutable const:     'b -> const       -> 'a * const;
     mutable const_rec: 'b -> const       -> 'a * const;
     mutable attr:      'b -> attr list   -> 'a * attr list;
     mutable app:       'a -> 'a -> 'a;
     mutable empty:     'a}
  val make : 'a -> ('a -> 'a -> 'a) -> ('a,'b) t
end

module Fold_tr : sig
  type 'a t =
    {mutable term:      'a -> term        -> 'a * term;
     mutable term_rec:  'a -> term        -> 'a * term;
     mutable desc:      'a -> desc        -> 'a * desc;
     mutable desc_rec:  'a -> desc        -> 'a * desc;
     mutable typ:       'a -> typ         -> 'a * typ;
     mutable typ_rec:   'a -> typ         -> 'a * typ;
     mutable var:       'a -> id          -> 'a * id;
     mutable lid:       'a -> lid         -> 'a * lid;
     mutable pat:       'a -> pattern     -> 'a * pattern;
     mutable pat_rec:   'a -> pattern     -> 'a * pattern;
     mutable info:      'a -> info        -> 'a * info;
     mutable info_rec:  'a -> info        -> 'a * info;
     mutable decl:      'a -> declaration -> 'a * declaration;
     mutable decl_rec:  'a -> declaration -> 'a * declaration;
     mutable const:     'a -> const       -> 'a * const;
     mutable const_rec: 'a -> const       -> 'a * const;
     mutable attr:      'a -> attr list   -> 'a * attr list}
  val list :       f:('a -> 'b -> 'a * 'c) -> acc:'a -> 'b list -> 'a * 'c list
  val list_left :  f:('a -> 'b -> 'a * 'c) -> acc:'a -> 'b list -> 'a * 'c list
  val list_right : f:('a -> 'b -> 'a * 'c) -> acc:'a -> 'b list -> 'a * 'c list
  val make : unit -> 'a t
end

val typ : term -> typ
val desc : term -> desc
val attr : term -> attr list
val pat_typ : pattern -> typ

val make : ?attr:attr list -> desc -> typ -> term
val make_pattern : ?attr:pat_attr list -> pat_desc -> typ -> pattern

val constr_of_id : id -> Type.constr
val path_of_lid : lid -> Type.path

val occur_typ : id -> typ -> bool
val get_vars : term -> id list
val get_fv : ?force:bool -> term -> id list
val get_fv_pat : ?force:bool -> pattern -> id list
val get_fv_decl : declaration -> id list
val get_bv_decl : ?env:(unit Id.t * typ) list -> declaration -> id list
val get_bt_decl : ?env:(unit Id.t * typ) list -> declaration -> Type.tconstr list
val get_bv_pat : ?force:bool -> pattern -> id list
val is_non_rec : (id * term) list -> bool
val head_of_lid : lid -> id

val set_afv : term -> term
val set_afv_shallowly : term -> term
val set_afv_abv_pat : pattern -> pattern
val get_fv_unique : ?eq:(id -> id -> bool) -> ?force:bool -> term -> id list
val get_fv_list : term list -> id list

val decomp_funs : term -> id list * term
val decomp_Decl_multi : declaration -> declaration list
val decomp_locals : term -> declaration list * term
val is_module : term -> bool
val is_functor : ?default:bool -> (Type.tconstr * typ) list -> term -> bool
val decomp_assert_desc : desc -> term option
val is_assert_desc : desc -> bool
val decomp_por : pattern -> pattern list
val decomp_forall : term -> id list * term
val decomp_exists : term -> id list * term

val add_attr : ?force:bool -> attr -> term -> term

module PrimId : sig
  val array_of_list : typ -> id
  val is_array_of_list : id -> bool
  val list_of_array : typ -> id
  val is_list_of_array : id -> bool
end

(* derived by ppx_deriving.show *)
val pp_term : Format.formatter -> term -> unit
val pp_id : Format.formatter -> id -> unit
val pp_typ : Format.formatter -> typ -> unit
val pp_declaration : Format.formatter -> declaration -> unit
val pp_pattern : Format.formatter -> pattern -> unit
val pp_pat_attr : Format.formatter -> pat_attr -> unit
val pp_params : Format.formatter -> params -> unit
val pp_binop : Format.formatter -> binop -> unit
val pp_const : Format.formatter -> const -> unit
val pp_lid : Format.formatter -> lid -> unit

val set_typ : term -> typ -> term
val set_pat_desc : pattern -> pat_desc -> pattern
(* The following functions are assumed to be used only in Term_util *)
val make_raw : ?attr:attr list -> desc -> typ -> term
[@@alert unsafe "This function must be used carefully"]
val set_desc : term -> desc -> term
[@@alert unsafe "This function must be used carefully"]
val set_attr : term -> attr list -> term
[@@alert unsafe "This function must be used carefully"]
