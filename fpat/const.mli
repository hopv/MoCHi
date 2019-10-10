(** Constants *)

(** @invariant the type of each constant is monomorphic
    @invariant the type of the elements of a vector must be of the order 0
    @invariant the number of the elements of a tuple must be >= 2
    BinTrue (resp. BinFalse) is necessary to make the constants closed under cor (resp. cand)
    @todo add pairwise max, min, scale for vectors *)

type t =
  (* comparables *)
  | Eq of Type.t | Neq of Type.t
  | Lt of Type.t | Gt of Type.t
  | Leq of Type.t | Geq of Type.t
  | BinTrue of Type.t (** binary true operator *)
  | BinFalse of Type.t (** binary false operator *)
  (* numbers *)
  | Neg of Type.t
  | Add of Type.t | Sub of Type.t
  | Mul of Type.t | Div of Type.t
  | Max of Type.t | Min of Type.t
  (* unit *)
  | Unit
  (* booleans *)
  | True | False
  | Not
  | And | Or | Imply | Iff
  | Box of string | Diamond of string
  (* integers *)
  | Int of int
  | BigInt of Big_int_Z.big_int
  | BitNot
  | BitShiftLeft | BitShiftRight | BitAnd | BitOr | BitXor
  | Mod
  | Divides of int
  (* real numbers *)
  | Real of float
  | FRsq | FRcp | FLog2 | FExp2 | FClamp
  | FPow
  (* strings *)
  | String of string
  (* lists *)
  | Nil of Type.t
  | Cons of Type.t
  (* uninterpreted functions *)
  | UFun of Type.t * Idnt.t
  (* path constructors *)
  | Call | Ret of Type.t | Error
  (* functions *)
  | App | Flip | Comp | Tlu
  | FShift
  (* events *)
  | Event of string
  (* random value generation *)
  | RandBool
  | RandInt
  | RandReal
  (* external value input *)
  | ReadBool of Idnt.t * Type.t list
  | ReadInt of Idnt.t * Type.t list
  | ReadReal of Idnt.t * Type.t list
  (* type annotations *)
  | Annot of Type.t
  (* others *)
  | Undef (** deprecated ? *)
  | Bot | Top
  (* *)
  | Coerce of Type.t

(** {6 Constants} *)

val event_fail : string
val event_end : string

(** {6 Printers} *)

val pr : unit Printer.t list -> t Printer.t
val pr_tex : unit Printer.t list -> t Printer.t
(** {6 Inspectors} *)

val string_of : t -> string
(** @require is_infix c *)
val string_of_infix : t -> string
val tex_string_of_infix : t -> string
val type_of : t -> Type.t
val arity_of : t -> int

(** @return whether c causes a side effect *)
val has_side_effect : t -> bool

(** @return whether c returns a unit value *)
val ret_unit : t -> bool
(** @return whether c returns a boolean value *)
val ret_bool : t -> bool
(** @return whether c returns an integer value *)
val ret_int : t -> bool
(** @return whether c returns an real value *)
val ret_real : t -> bool

(** @return whether c is binary *)
val is_bin : t -> bool
(** @return whether c is an integer binary operator *)
val is_ibop : t -> bool
(** @return whether c is an real binary operator *)
val is_rbop : t -> bool

(** @require is_bin c *)
val is_infix : t -> bool

(** @return whether c is a binary relation *)
val is_brel : t -> bool
(** @return whether c is a binary relation on unit *)
val is_ubrel : t -> bool
(** @return whether c is a binary relation on booleans *)
val is_bbrel : t -> bool
(** @return whether c is a binary relation on integers *)
val is_ibrel : t -> bool
(** @return whether c is a binary relation on real numbers *)
val is_rbrel : t -> bool

(** @return whether c is equality *)
val is_eq : t -> bool
(** @return whether c is non-equality *)
val is_neq : t -> bool
(** @return whether c is equality or non-equality *)
val is_eq_neq : t -> bool

val lift_int : t -> int
val lift_ibop : t -> int -> int -> int
val lift_rbop : t -> float -> float -> float
val lift_brel : t -> 'a -> 'a -> bool
val lift_iurel : t -> int -> bool

(** {6 Operators} *)

(** binary negate binary relations
    @require [is_brel c] *)
val not : t -> t
(** number negate binary relations *)
val neg : t -> t
val cand : t -> t -> t
val cor : t -> t -> t
(** x c1 n1 && x c2 n2 *)
val candn : t * int -> t * int -> (t * int) list
(** @todo candns (candns cns) may not be equivalent to candns cns *)
val candns : (t * int) list -> (t * int) list
(** x c1 n1 || x c2 n2 *)
val corn : t * int -> t * int -> (t * int) list
(** @todo corns (corns cns) may not be equivalent to corns cns *)
val corns : (t * int) list -> (t * int) list
val eval : t list -> t list

val subst_tvars : TypEnv.t -> t -> t

val int_to_real : t -> t
val real_to_int : t -> t
