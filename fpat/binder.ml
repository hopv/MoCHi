open Combinator
open Util

(** Binders *)

type t =
  | Lambda of Type.t (** lambda abstraction *)
  | Fix of Type.t (** least fixed-point operator *)
  | CallCC of Type.t (** call/CC *)
  | Random of Type.t (** random number generator *)
  | Forall of Type.t (** universal quantifier *)
  | Exists of Type.t (** existential quantifier *)
  | Mu (** least fixed-point operator for mu calculus *)
  | Nu (** greatest fixed-point operator for mu calculus *)

(* Fix : Type.mk_fun [Type.mk_fun [ty; ty]; ty] *)

let string_of = function
  | Lambda(_) -> "fun"
  | Fix(_) -> "fix"
  (* @note not supported by OCaml *)
  | CallCC(_) -> "call/cc"
  (* @note not supported by OCaml *)
  | Random(_) -> "rand"
  (* @note not supported by OCaml *)
  | Forall(_) -> "forall"
  (* @note not supported by OCaml *)
  | Exists(_) -> "exists"
  (* @note not supported by OCaml *)
  | Mu -> "mu"
  (* @note not supported by OCaml *)
  | Nu -> "nu"

let pr p upr ppf b =
  Format.fprintf
    ppf
    "@[<hov2>%s %a.@ %a@]"
    (string_of b)
    Pattern.pr p
    upr ()

let body_type_of b ty =
  match b with
  | Lambda(ty0) ->
    let [arg], ret = Type.args_ret ty in
    assert (Type.equiv arg ty0);
    ret
  | Fix(ty0) ->
    assert (Type.equiv ty0 ty);
    ty
  | CallCC(_) ->
    assert false
  | Random(_) ->
    ty
  | Forall(_) | Exists(_) | Mu | Nu ->
    assert (Type.equiv ty Type.mk_bool);
    Type.mk_bool

let is_quantifier = function
  | Forall(_) | Exists(_) -> true
  | _ -> false

(** @require is_quantifier b *)
let not = function
  | Forall(ty) -> Exists(ty)
  | Exists(ty) -> Forall(ty)
  | _ -> assert false

let subst_tvars tsub = function
  | Lambda(ty) -> Lambda(Type.subst tsub ty)
  | Fix(ty) -> Fix(Type.subst tsub ty)
  | CallCC(ty) -> CallCC(Type.subst tsub ty)
  | Random(ty) -> Random(Type.subst tsub ty)
  | Forall(ty) -> Forall(Type.subst tsub ty)
  | Exists(ty) -> Exists(Type.subst tsub ty)
  | Mu -> Mu
  | Nu -> Nu
