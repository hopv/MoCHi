(** Abstract terms *)

(* @todo how to support De Bruijn indices? *)

exception CannotUnify
exception CannotMatch

module type BINDER = sig
  type t
  val pr : Pattern.t -> unit Printer.t -> t Printer.t
end

module type CONST = sig
  type t
  val pr : unit Printer.t list -> t Printer.t
  val pr_tex : unit Printer.t list -> t Printer.t
end

module Make : functor (Binder : BINDER) -> functor (Const : CONST) -> sig
  (** {6 Constructors} *)

  type t =
  | Var of Idnt.t (** variables *)
  | Const of Const.t (** constants *)
  | App of t * t (** applications *)
  | Binder of Binder.t * Pattern.t * t (** binders *)

  (** {6 Auxiliary constructors} *)

  val mk_var : Idnt.t -> t
  val mk_const : Const.t -> t
  val mk_binder : Binder.t -> Pattern.t -> t -> t
  val mk_app : t -> t list -> t
  val mk_app2 : t list -> t
  
  val new_var : unit -> t
  val var_of_string : string -> t
  val new_coeff : unit -> t

  (** {6 Auxiliary destructors} *)

  val fun_args : t -> t * t list

  val let_var : t -> (Idnt.t -> 'r) -> 'r
  val let_const : t -> (Const.t -> 'r) -> 'r
  val let_app : t -> (t -> t -> 'r) -> 'r
  val let_fun_args : t -> (t -> t list -> 'r) -> 'r
  val let_binder : t -> (Binder.t -> Pattern.t -> t -> 'r) -> 'r

  val var_of : t -> Idnt.t

  val is_var : t -> bool
  val is_const : t -> bool
  val is_app : t -> bool
  val is_binder : t -> bool

  (** {6 Morphisms} *)

  val para :
    < fvar : Idnt.t -> 'r;
      fcon : Const.t -> 'r;
      fapp : t -> 'r -> t -> 'r -> 'r;
      fbin : Binder.t -> Pattern.t -> t -> 'r -> 'r; .. > ->
    t -> 'r

  val para_app :
    < fvar : Idnt.t -> 'r;
      fcon : Const.t -> 'r;
      fapp : t -> 'r -> t list -> 'r list -> 'r;
      fbin : Binder.t -> Pattern.t -> t -> 'r -> 'r; .. > ->
    t -> 'r

  val para_wo_app :
    < fvar : Idnt.t -> t list -> 'r list -> 'r;
      fcon : Const.t -> t list -> 'r list -> 'r;
      fbin : Binder.t -> Pattern.t -> t -> 'r -> t list -> 'r list -> 'r; .. > ->
    t -> 'r

  val lazy_para :
    < fvar : Idnt.t -> 'r;
      fcon : Const.t -> 'r;
      fapp : t -> 'r Lazy.t -> t -> 'r Lazy.t -> 'r;
      fbin : Binder.t -> Pattern.t -> t -> 'r Lazy.t -> 'r; .. > ->
    t -> 'r

  val lazy_para_app :
    < fvar : Idnt.t -> 'r;
      fcon : Const.t -> 'r;
      fapp : t -> 'r Lazy.t -> t list -> 'r Lazy.t list -> 'r;
      fbin : Binder.t -> Pattern.t -> t -> 'r Lazy.t -> 'r; .. > ->
    t -> 'r

  val lazy_para_wo_app :
    < fvar : Idnt.t -> t list -> 'r Lazy.t list -> 'r;
      fcon : Const.t -> t list -> 'r Lazy.t list -> 'r;
      fbin : Binder.t -> Pattern.t -> t -> 'r Lazy.t -> t list -> 'r Lazy.t list -> 'r; .. > ->
    t -> 'r

  val fold :
    < fvar : Idnt.t -> 'r;
      fcon : Const.t -> 'r;
      fapp : 'r -> 'r -> 'r;
      fbin : Binder.t -> Pattern.t -> 'r -> 'r; .. > ->
    t -> 'r

  val fold_app :
    < fvar : Idnt.t -> 'r;
      fcon : Const.t -> 'r;
      fapp : 'r -> 'r list -> 'r;
      fbin : Binder.t -> Pattern.t -> 'r -> 'r; .. > ->
    t -> 'r

  val fold_wo_app :
    < fvar : Idnt.t -> 'r list -> 'r;
      fcon : Const.t -> 'r list -> 'r;
      fbin : Binder.t -> Pattern.t -> 'r -> 'r list -> 'r; .. > ->
    t -> 'r

  (** @todo implement a CIL-like visitor for terms *)
  val visit :
    < fvar : Idnt.t -> 'r;
      fcon : Const.t -> 'r;
      fapp : t -> t -> 'r;
      fbin : Binder.t -> Pattern.t -> t -> 'r; .. > ->
    t -> 'r

  val visit_wo_app :
    < fvar : Idnt.t -> t list -> 'r;
      fcon : Const.t -> t list -> 'r;
      fbin : Binder.t -> Pattern.t -> t -> t list -> 'r; .. > ->
    t -> 'r

  val map_var : (Idnt.t -> Idnt.t) -> t -> t

  val map_con : (Const.t -> Const.t) -> t -> t

  (** {6 Printers} *)

  val pr : Format.formatter -> t -> unit
  val pr_tex : Format.formatter -> t -> unit
  val pr_list : Format.formatter -> t list -> unit

  (** {6 Inspectors} *)

  val string_of : t -> string

  (** @todo implement equivalence up to alpha conversion *)
  val equiv : t -> t -> bool

  val occurs : Idnt.t -> t -> bool

  val num_of_const_occurrences : Const.t -> t -> int
  val num_of_var_occurrences : Idnt.t -> t -> int

  val fvs : t -> Idnt.t list
  val coeffs : t -> Idnt.t list
  val constants : t -> Const.t list

  (** composition of find and mapc *)
  val find_mapc : ((t -> t) -> t -> 'r option) -> t -> 'r

  (** composition of find_all and mapc *)
  val find_all_mapc : ((t -> t) -> t -> 'r option) -> t -> 'r list

  (** {6 Operators} *)

  (** @require t does not use De Bruijn index
      @todo assume that t is not like "fun x -> (fun y -> fun x -> y) x"? *)
  val subst : (Idnt.t * t) list -> t -> t

  (** @todo compute the fixed-point of sub first
      @require t does not use De Bruijn index
      @require for any t, simplify (simplify t) = simplify t *)
  val subst_fixed : ?simplify:(t -> t) -> (Idnt.t * t) list -> t -> t

  (** rename given variables to fresh ones
      @param xs variables to be renamed
      @require not (List.duplicate xs) *)
  val fresh : Idnt.t list -> t -> t

  val rename : (Idnt.t * Idnt.t) list -> t -> t

  val alpha_conv : t -> t

  val shift : int -> t -> t

  val unify : ?gvs:Idnt.t list -> (t * t) list -> (Idnt.t * t) list

  (** [pat_match t p] matches [t] with [p] *)
  val pat_match : t -> t -> (Idnt.t * t) list
end
