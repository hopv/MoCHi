
(** Syntax of intermediate language *)

type label = Read | Write | Close
type binop = Eq | Lt | Gt | Leq | Geq | And | Or | Add | Sub | Mult | Div
type typ = term Type.t
and tattr = term Type.attr
and id = typ Id.t
and attr =
  | AAbst_under
  | ATerminate
  | ANotFail
  | ADeterministic
  | AComment of string
  | AId of int
  | ADoNotInline
  | AEffect of Type.effect list
  | ALoc of Location.t
and term = {desc:desc; typ:typ; attr:attr list}
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
and desc =
  | End_of_definitions
  | Const of const
  | Var of id
  | Fun of id * term
  | App of term * term list
  | If of term * term * term
  | Local of declaration * term
  | BinOp of binop * term * term
  | Not of term
  | Event of string * bool (** true denotes CPS-term *)
  | Record of (string * term) list
  | Field of term * string
  | SetField of term * string * term
  | Nil
  | Cons of term * term
  | Constr of string * term list
  | Match of term * (pattern * term) list (** a term diverges if no patters are matched *)
  | Raise of term
  | TryWith of term * term
  | Tuple of term list
  | Proj of int * term
  | Bottom
  | Label of info * term
  | Ref of term
  | Deref of term
  | SetRef of term * term
  | TNone
  | TSome of term
  | Module of declaration list

and declaration =
  | Decl_let of (id * term) list
  | Decl_type of (string * typ) list

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
and pred = desc
and pattern = {pat_desc:pat_desc; pat_typ:typ}
and pat_desc =
  | PAny
  | PNondet (* match non-deterministically *)
  | PVar of id
  | PAlias of pattern * id
  | PConst of term
  | PConstr of string * pattern list
  | PNil
  | PCons of pattern * pattern
  | PTuple of pattern list
  | PRecord of (string * pattern) list
  | PNone
  | PSome of pattern
  | POr of pattern * pattern
  | PWhen of pattern * term

type env = (id * typ) list

module ID : sig
  type t = id
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end

module PredVar : sig
  val pvar_name : string
  val is_pvar : id -> bool
  val new_pvar : ?name:string -> typ list -> id
end

val safe_attr : attr list
val pure_attr : attr list
val const_attr : attr list

type trans =
  {mutable tr_term:      term        -> term;
   mutable tr_term_rec:  term        -> term;
   mutable tr_desc:      desc        -> desc;
   mutable tr_desc_rec:  desc        -> desc;
   mutable tr_typ:       typ         -> typ;
   mutable tr_typ_rec:   typ         -> typ;
   mutable tr_var:       id          -> id;
   mutable tr_var_rec:   id          -> id;
   mutable tr_pat:       pattern     -> pattern;
   mutable tr_pat_rec:   pattern     -> pattern;
   mutable tr_info:      info        -> info;
   mutable tr_info_rec:  info        -> info;
   mutable tr_decl:      declaration -> declaration;
   mutable tr_decl_rec:  declaration -> declaration;
   mutable tr_const:     const       -> const;
   mutable tr_const_rec: const       -> const;
   mutable tr_attr:      attr list   -> attr list}

type 'a trans2 =
  {mutable tr2_term:      'a -> term        -> term;
   mutable tr2_term_rec:  'a -> term        -> term;
   mutable tr2_desc:      'a -> desc        -> desc;
   mutable tr2_desc_rec:  'a -> desc        -> desc;
   mutable tr2_typ:       'a -> typ         -> typ;
   mutable tr2_typ_rec:   'a -> typ         -> typ;
   mutable tr2_var:       'a -> id          -> id;
   mutable tr2_var_rec:   'a -> id          -> id;
   mutable tr2_pat:       'a -> pattern     -> pattern;
   mutable tr2_pat_rec:   'a -> pattern     -> pattern;
   mutable tr2_info:      'a -> info        -> info;
   mutable tr2_info_rec:  'a -> info        -> info;
   mutable tr2_decl:      'a -> declaration -> declaration;
   mutable tr2_decl_rec:  'a -> declaration -> declaration;
   mutable tr2_const:     'a -> const       -> const;
   mutable tr2_const_rec: 'a -> const       -> const;
   mutable tr2_attr:      'a -> attr list   -> attr list}

type 'a col =
  {mutable col_term:      term        -> 'a;
   mutable col_term_rec:  term        -> 'a;
   mutable col_desc:      desc        -> 'a;
   mutable col_desc_rec:  desc        -> 'a;
   mutable col_typ:       typ         -> 'a;
   mutable col_typ_rec:   typ         -> 'a;
   mutable col_var:       id          -> 'a;
   mutable col_var_rec:   id          -> 'a;
   mutable col_pat:       pattern     -> 'a;
   mutable col_pat_rec:   pattern     -> 'a;
   mutable col_info:      info        -> 'a;
   mutable col_info_rec:  info        -> 'a;
   mutable col_decl:      declaration -> 'a;
   mutable col_decl_rec:  declaration -> 'a;
   mutable col_const:     const       -> 'a;
   mutable col_const_rec: const       -> 'a;
   mutable col_attr:      attr list   -> 'a;
   mutable col_app:       'a -> 'a -> 'a;
   mutable col_empty:     'a}

type ('a,'b) col2 =
  {mutable col2_term:      'b -> term        -> 'a;
   mutable col2_term_rec:  'b -> term        -> 'a;
   mutable col2_desc:      'b -> desc        -> 'a;
   mutable col2_desc_rec:  'b -> desc        -> 'a;
   mutable col2_typ:       'b -> typ         -> 'a;
   mutable col2_typ_rec:   'b -> typ         -> 'a;
   mutable col2_var:       'b -> id          -> 'a;
   mutable col2_var_rec:   'b -> id          -> 'a;
   mutable col2_pat:       'b -> pattern     -> 'a;
   mutable col2_pat_rec:   'b -> pattern     -> 'a;
   mutable col2_info:      'b -> info        -> 'a;
   mutable col2_info_rec:  'b -> info        -> 'a;
   mutable col2_decl:      'b -> declaration -> 'a;
   mutable col2_decl_rec:  'b -> declaration -> 'a;
   mutable col2_const:     'b -> const       -> 'a;
   mutable col2_const_rec: 'b -> const       -> 'a;
   mutable col2_attr:      'b -> attr list   -> 'a;
   mutable col2_app:       'a -> 'a -> 'a;
   mutable col2_empty:     'a}

type ('a,'b) tr_col2 =
  {mutable tr_col2_term:      'b -> term        -> 'a * term;
   mutable tr_col2_term_rec:  'b -> term        -> 'a * term;
   mutable tr_col2_desc:      'b -> desc        -> 'a * desc;
   mutable tr_col2_desc_rec:  'b -> desc        -> 'a * desc;
   mutable tr_col2_typ:       'b -> typ         -> 'a * typ;
   mutable tr_col2_typ_rec:   'b -> typ         -> 'a * typ;
   mutable tr_col2_var:       'b -> id          -> 'a * id;
   mutable tr_col2_var_rec:   'b -> id          -> 'a * id;
   mutable tr_col2_pat:       'b -> pattern     -> 'a * pattern;
   mutable tr_col2_pat_rec:   'b -> pattern     -> 'a * pattern;
   mutable tr_col2_info:      'b -> info        -> 'a * info;
   mutable tr_col2_info_rec:  'b -> info        -> 'a * info;
   mutable tr_col2_decl:      'b -> declaration -> 'a * declaration;
   mutable tr_col2_decl_rec:  'b -> declaration -> 'a * declaration;
   mutable tr_col2_const:     'b -> const       -> 'a * const;
   mutable tr_col2_const_rec: 'b -> const       -> 'a * const;
   mutable tr_col2_attr:      'b -> attr list   -> 'a * attr list;
   mutable tr_col2_app:       'a -> 'a -> 'a;
   mutable tr_col2_empty:     'a}

type 'a fold_tr =
  {mutable fld_term:      'a -> term        -> 'a * term;
   mutable fld_term_rec:  'a -> term        -> 'a * term;
   mutable fld_desc:      'a -> desc        -> 'a * desc;
   mutable fld_desc_rec:  'a -> desc        -> 'a * desc;
   mutable fld_typ:       'a -> typ         -> 'a * typ;
   mutable fld_typ_rec:   'a -> typ         -> 'a * typ;
   mutable fld_var:       'a -> id          -> 'a * id;
   mutable fld_var_rec:   'a -> id          -> 'a * id;
   mutable fld_pat:       'a -> pattern     -> 'a * pattern;
   mutable fld_pat_rec:   'a -> pattern     -> 'a * pattern;
   mutable fld_info:      'a -> info        -> 'a * info;
   mutable fld_info_rec:  'a -> info        -> 'a * info;
   mutable fld_decl:      'a -> declaration -> 'a * declaration;
   mutable fld_decl_rec:  'a -> declaration -> 'a * declaration;
   mutable fld_const:     'a -> const       -> 'a * const;
   mutable fld_const_rec: 'a -> const       -> 'a * const;
   mutable fld_attr:      'a -> attr list   -> 'a * attr list}
val fold_tr_list : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list


val typ : term -> typ
val desc : term -> desc
val attr : term -> attr list

val make_trans : unit -> trans
val make_trans2 : unit -> 'a trans2
val make_col : 'a -> ('a -> 'a -> 'a) -> 'a col
val make_col2 : 'a -> ('a -> 'a -> 'a) -> ('a,'b) col2
val make_tr_col2 : 'a -> ('a -> 'a -> 'a) -> ('a,'b) tr_col2
val make_fold_tr : unit -> 'a fold_tr

val occur_typ : id -> typ -> bool
val get_vars : term -> id list
val get_fv : ?eq:(id -> id -> bool) -> term -> id list
val get_bv : term -> id list
val get_bv_pat : pattern -> id list
val is_non_rec : (id * term) list -> bool

val is_prim_var : id -> bool
val decomp_funs : term -> id list * term
val decomp_locals : term -> declaration list * term

val print_location_ref : (Format.formatter -> Location.t -> unit) ref
val print_location : Format.formatter -> Location.t -> unit

(* ppx_deriving show *)
val pp_term : Format.formatter -> term -> unit
val pp_id : Format.formatter -> id -> unit
val pp_typ : Format.formatter -> typ -> unit
val pp_declaration : Format.formatter -> declaration -> unit
val pp_pattern : Format.formatter -> pattern -> unit
