open Util
open Combinator

type t =
  (* comparables *)
  | Eq of Type.t | Neq of Type.t
  | Lt of Type.t | Gt of Type.t
  | Leq of Type.t | Geq of Type.t
  | BinTrue of Type.t
  | BinFalse of Type.t
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
  | ReadBool of Idnt.t * Type.t list(*@todo*)
  | ReadInt of Idnt.t * Type.t list(*@todo*)
  | ReadReal of Idnt.t * Type.t list(*@todo*)
  (* type annotations *)
  | Annot of Type.t
  (* others *)
  | Undef
  | Bot | Top
  (* *)
  | Coerce of Type.t

(** {6 Constants} *)

let event_fail = "fail"
let event_end = "end"

(** {6 Inspectors} *)

let string_of = function
  (* comparables *)
  | Eq(ty) -> if !Global.debug then "(=)[" ^ Type.string_of ty ^ "]" else "(=)"
  | Neq(ty) -> if !Global.debug then "(<>)[" ^ Type.string_of ty ^ "]" else "(<>)"
  | Lt(ty) -> if !Global.debug then "(<)[" ^ Type.string_of ty ^ "]" else "(<)"
  | Gt(ty) -> if !Global.debug then "(>)[" ^ Type.string_of ty ^ "]" else "(>)"
  | Leq(ty) -> if !Global.debug then "(<=)[" ^ Type.string_of ty ^ "]" else "(<=)"
  | Geq(ty) -> if !Global.debug then "(>=)[" ^ Type.string_of ty ^ "]" else "(>=)"
  (* @todo not supported by OCaml *)
  | BinTrue(ty) -> "bintrue[" ^ Type.string_of ty ^ "]"
  (* @todo not supported by OCaml *)
  | BinFalse(ty) -> "binfalse[" ^ Type.string_of ty ^ "]"
  (* numbers *)
  | Neg(ty) when Type.is_int ty -> "-"
  | Neg(ty) when Type.is_real ty -> "-."
  (* @todo not supported by OCaml *)
  | Add(ty) when Type.is_int ty -> "(+)"
  | Add(ty) when Type.is_real ty -> "(+.)"
  (* @todo not supported by OCaml *)
  | Sub(ty) when Type.is_int ty -> "(-)"
  | Sub(ty) when Type.is_real ty -> "(-.)"
  (* @todo not supported by OCaml *)
  | Mul(ty) when Type.is_int ty -> "( * )"
  | Mul(ty) when Type.is_real ty -> "( *. )"
  (* @todo not supported by OCaml *)
  | Div(ty) when Type.is_int ty -> "(/)"
  | Div(ty) when Type.is_real ty -> "(/.)"
  | Max(_) -> "max"
  | Min(_) -> "min"
  (* unit *)
  | Unit -> "()"
  (* booleans *)
  | True -> "true"
  | False -> "false"
  | Not -> "not"
  | And -> "(&&)"
  | Or -> "(||)"
  | Box(index) -> "([" ^ index ^ "])"
  | Diamond(index) -> "(<" ^ index ^ ">)"
  (* @todo not supported by OCaml *)
  | Imply -> "(=>)"
  (* @todo not supported by OCaml *)
  | Iff -> "(<=>)"
  (* integers *)
  | Int(n) -> string_of_int n
  | BigInt(n) -> Big_int_Z.string_of_big_int n
  | BitNot -> "lnot"
  | BitShiftLeft -> "(lsl)"
  | BitShiftRight -> "(lsr)"
  | BitAnd -> "(land)"
  | BitOr -> "(lor)"
  | BitXor -> "(lxor)"
  | Mod -> "(mod)"
  (* @todo not supported by OCaml *)
  | Divides(n) -> "divides(n)" (*"n |"*)
  (* real numbers *)
  | Real(f) -> string_of_float f
  (* @todo not supported by OCaml *)
  | FRsq -> "rsq"
  (* @todo not supported by OCaml *)
  | FRcp -> "rcp"
  (* @todo not supported by OCaml *)
  | FLog2 -> "log2"
  (* @todo not supported by OCaml *)
  | FExp2 -> "exp2"
  (* @todo not supported by OCaml *)
  | FClamp -> "clamp"
  (* @todo not supported by OCaml *)
  | FPow -> "pow"
  (* strings *)
  | String(str) -> "\"" ^ String.escaped str ^ "\""
  (* lists *)
  | Nil(_) -> "[]"
  (* @todo not supported by OCaml *)
  | Cons(_) -> "(::)"
  (* path constructors *)
  | Call -> "Call"
  | Ret(_) -> "Ret"
  | Error -> "Error"
  (* functions *)
  | App -> "(@@)"
  (* @todo not supported by OCaml *)
  | Flip -> "flip"
  (* @todo not supported by OCaml *)
  | Comp -> "comp"
  (* @todo not supported by OCaml *)
  | Tlu -> "tlu"
  (* @todo not supported by OCaml *)
  | FShift -> "shift"
  (* events *)
  (* @todo not supported by OCaml *)
  | Event(id) -> id
  (* random value generation *)
  | RandBool -> "(Random.bool ())"
  (* @todo string_of_int Integer.max_int instead of 0 is better?*)
  | RandInt -> "(Random.int " ^ "0" ^ ")"
  | RandReal -> "(Random.float " ^ "0." ^ ")"
  (* external value input *)
  | ReadBool(_, _) -> "(read_bool ())"
  | ReadInt(_, _) -> "(Pervasives.read_int ())"
  | ReadReal(_, _) -> "(Pervasives.read_float ())"
  (* type annotations *)
  (* @todo not supported by OCaml *)
  | Annot(ty) -> "<" ^ Type.string_of ty ^ ">"
  (* others *)
  (* @todo not supported by OCaml *)
  | Undef -> "undef"
  (* @todo not supported by OCaml *)
  | Bot -> "bot"
  (* @todo not supported by OCaml *)
  | Top -> "top"
  (**)
  | Coerce ty -> "coerce[" ^ Type.string_of ty ^ "]"
  | _ -> "(?undef:\"const.ml\")"(*assert false*)

let tex_string_of = function
  (* comparables *)
  | Eq(ty) -> if !Global.debug then "(=)[" ^ Type.string_of ty ^ "]" else "(=)"
  | Neq(ty) -> if !Global.debug
               then "(\\neq)[" ^ Type.string_of ty ^ "]"
               else "(\\neq)"
  | Lt(ty) -> if !Global.debug then "(<)[" ^ Type.string_of ty ^ "]" else "(<)"
  | Gt(ty) -> if !Global.debug then "(>)[" ^ Type.string_of ty ^ "]" else "(>)"
  | Leq(ty) -> if !Global.debug then "(<=)[" ^ Type.string_of ty ^ "]" else "(<=)"
  | Geq(ty) -> if !Global.debug then "(>=)[" ^ Type.string_of ty ^ "]" else "(>=)"
  (* @todo not supported by OCaml *)
  | BinTrue(ty) -> "bintrue[" ^ Type.string_of ty ^ "]"
  (* @todo not supported by OCaml *)
  | BinFalse(ty) -> "binfalse[" ^ Type.string_of ty ^ "]"
  (* numbers *)
  | Neg(ty) when Type.is_int ty -> "-"
  | Neg(ty) when Type.is_real ty -> "-."
  (* @todo not supported by OCaml *)
  | Add(ty) when Type.is_int ty -> "(+)"
  | Add(ty) when Type.is_real ty -> "(+.)"
  (* @todo not supported by OCaml *)
  | Sub(ty) when Type.is_int ty -> "(-)"
  | Sub(ty) when Type.is_real ty -> "(-.)"
  (* @todo not supported by OCaml *)
  | Mul(ty) when Type.is_int ty -> "( * )"
  | Mul(ty) when Type.is_real ty -> "( *. )"
  (* @todo not supported by OCaml *)
  | Div(ty) when Type.is_int ty -> "(/)"
  | Div(ty) when Type.is_real ty -> "(/.)"
  | Max(_) -> "max"
  | Min(_) -> "min"
  (* unit *)
  | Unit -> "()"
  (* booleans *)
  | True -> "true"
  | False -> "false"
  | Not -> "not"
  | And -> "(&&)"
  | Or -> "(||)"
  | Box(index) -> "([" ^ index ^ "])"
  | Diamond(index) -> "(<" ^ index ^ ">)"
  (* @todo not supported by OCaml *)
  | Imply -> "(=>)"
  (* @todo not supported by OCaml *)
  | Iff -> "(<=>)"
  (* integers *)
  | Int(n) -> string_of_int n
  | BigInt(n) -> Big_int_Z.string_of_big_int n
  | BitNot -> "lnot"
  | BitShiftLeft -> "(lsl)"
  | BitShiftRight -> "(lsr)"
  | BitAnd -> "(land)"
  | BitOr -> "(lor)"
  | BitXor -> "(lxor)"
  | Mod -> "(mod)"
  (* @todo not supported by OCaml *)
  | Divides(n) -> "divides(n)" (*"n |"*)
  (* real numbers *)
  | Real(f) -> string_of_float f
  (* @todo not supported by OCaml *)
  | FRsq -> "rsq"
  (* @todo not supported by OCaml *)
  | FRcp -> "rcp"
  (* @todo not supported by OCaml *)
  | FLog2 -> "log2"
  (* @todo not supported by OCaml *)
  | FExp2 -> "exp2"
  (* @todo not supported by OCaml *)
  | FClamp -> "clamp"
  (* @todo not supported by OCaml *)
  | FPow -> "pow"
  (* strings *)
  | String(str) -> "\"" ^ String.escaped str ^ "\""
  (* lists *)
  | Nil(_) -> "[]"
  (* @todo not supported by OCaml *)
  | Cons(_) -> "(::)"
  (* uninterpreted functions *)
  | UFun(ty, x) -> Idnt.string_of x
  (* path constructors *)
  | Call -> "Call"
  | Ret(_) -> "Ret"
  | Error -> "Error"
  (* functions *)
  | App -> "(@@)"
  (* @todo not supported by OCaml *)
  | Flip -> "flip"
  (* @todo not supported by OCaml *)
  | Comp -> "comp"
  (* @todo not supported by OCaml *)
  | Tlu -> "tlu"
  (* @todo not supported by OCaml *)
  | FShift -> "shift"
  (* events *)
  (* @todo not supported by OCaml *)
  | Event(id) -> id
  (* random value generation *)
  | RandBool -> "(Random.bool ())"
  (* @todo string_of_int Integer.max_int instead of 0 is better?*)
  | RandInt -> "(Random.int " ^ "0" ^ ")"
  | RandReal -> "(Random.float " ^ "0." ^ ")"
  (* external value input *)
  | ReadBool(_, _) -> "(read_bool ())"
  | ReadInt(_, _) -> "(Pervasives.read_int ())"
  | ReadReal(_, _) -> "(Pervasives.read_float ())"
  (* type annotations *)
  (* @todo not supported by OCaml *)
  | Annot(ty) -> "<" ^ Type.string_of ty ^ ">"
  (* others *)
  (* @todo not supported by OCaml *)
  | Undef -> "undef"
  (* @todo not supported by OCaml *)
  | Bot -> "bot"
  (* @todo not supported by OCaml *)
  | Top -> "top"
  (**)
  | Coerce ty -> "coerce[" ^ Type.string_of ty ^ "]"
  | _ -> "(?undef:\"const.ml\")"(*assert false*)

(** @require is_infix c *)
let string_of_infix = function
  (* comparables *)
  | Eq(ty) -> if !Global.debug then "=[" ^ Type.string_of ty ^ "]" else "="
  | Neq(ty) -> if !Global.debug then "<>[" ^ Type.string_of ty ^ "]" else "<>"
  | Lt(ty) -> if !Global.debug then "<[" ^ Type.string_of ty ^ "]" else "<"
  | Gt(ty) -> if !Global.debug then ">[" ^ Type.string_of ty ^ "]" else ">"
  | Leq(ty) -> if !Global.debug then "<=[" ^ Type.string_of ty ^ "]" else "<="
  | Geq(ty) -> if !Global.debug then ">=[" ^ Type.string_of ty ^ "]" else ">="
  (* numbers *)
  | Add(ty) when Type.is_int ty -> "+"
  | Add(ty) when Type.is_real ty -> "+."
  (* @todo not supported by OCaml *)
  | Add(_) -> "+"
  | Sub(ty) when Type.is_int ty -> "-"
  | Sub(ty) when Type.is_real ty -> "-."
  (* @todo not supported by OCaml *)
  | Sub(_) -> "-"
  | Mul(ty) when Type.is_int ty -> "*"
  | Mul(ty) when Type.is_real ty -> "*."
  (* @todo not supported by OCaml *)
  | Mul(_) -> "*"
  | Div(ty) when Type.is_int ty -> "/"
  | Div(ty) when Type.is_real ty -> "/."
  | Div(_) -> "/"
  (* booleans *)
  | And -> "&&"
  | Or -> "||"
  | Box(index) -> "[" ^ index ^ "]"
  | Diamond(index) -> "<" ^ index ^ ">"
  (* @todo not supported by OCaml *)
  | Imply -> "=>"
  (* @todo not supported by OCaml *)
  | Iff -> "<=>"
  (* integers *)
  | BitShiftLeft -> "lsl"
  | BitShiftRight -> "lsr"
  | BitAnd -> "land"
  | BitOr -> "lor"
  | BitXor -> "lxor"
  | Mod -> "mod"
  (* lists *)
  | Cons(_) -> "::"
  (* functions *)
  | App -> "@@"
  (* @todo not supported by OCaml *)
  | Comp -> "."
  | _ -> "CONST_ERROR(string_of_infix)"

let tex_string_of_infix = function
  (* comparables *)
  | Eq(ty) -> if !Global.debug then "=[" ^ Type.string_of ty ^ "]" else "="
  | Neq(ty) -> if !Global.debug then "\\neq[" ^ Type.string_of ty ^ "]"
               else "\\neq"
  | Lt(ty) -> if !Global.debug then "<[" ^ Type.string_of ty ^ "]" else "<"
  | Gt(ty) -> if !Global.debug then ">[" ^ Type.string_of ty ^ "]" else ">"
  | Leq(ty) -> if !Global.debug then "<=[" ^ Type.string_of ty ^ "]" else "<="
  | Geq(ty) -> if !Global.debug then ">=[" ^ Type.string_of ty ^ "]" else ">="
  (* numbers *)
  | Add(ty) when Type.is_int ty -> "+"
  | Add(ty) when Type.is_real ty -> "+."
  (* @todo not supported by OCaml *)
  | Add(_) -> "+"
  | Sub(ty) when Type.is_int ty -> "-"
  | Sub(ty) when Type.is_real ty -> "-."
  (* @todo not supported by OCaml *)
  | Sub(_) -> "-"
  | Mul(ty) when Type.is_int ty -> "*"
  | Mul(ty) when Type.is_real ty -> "*."
  (* @todo not supported by OCaml *)
  | Mul(_) -> "*"
  | Div(ty) when Type.is_int ty -> "/"
  | Div(ty) when Type.is_real ty -> "/."
  | Div(_) -> "/"
  (* booleans *)
  | And -> "\\land"
  | Or -> "\\lor"
  | Box(index) -> "[" ^ index ^ "]"
  | Diamond(index) -> "<" ^ index ^ ">"
  (* @todo not supported by OCaml *)
  | Imply -> "\\Rightarrow"
  (* @todo not supported by OCaml *)
  | Iff -> "\\Rightleftarrow"
  (* integers *)
  | BitShiftLeft -> "lsl"
  | BitShiftRight -> "lsr"
  | BitAnd -> "land"
  | BitOr -> "lor"
  | BitXor -> "lxor"
  | Mod -> "mod"
  (* lists *)
  | Cons(_) -> "::"
  (* functions *)
  | App -> "@@"
  (* @todo not supported by OCaml *)
  | Comp -> "."
  | _ -> "CONST_ERROR(string_of_infix)"

let type_of = function
  (* comparables *)
  | Eq(ty) | Neq(ty) | Lt(ty) | Gt(ty) | Leq(ty) | Geq(ty)
  | BinTrue(ty) | BinFalse(ty) -> Type.mk_fun [ty; ty; Type.mk_bool]
  (* numbers *)
  | Neg(ty) -> Type.mk_fun [ty; ty]
  | Add(ty) | Sub(ty) | Mul(ty) | Div(ty) | Max(ty) | Min(ty) ->
    Type.mk_fun [ty; ty; ty]
  (* unit *)
  | Unit -> Type.mk_unit
  (* booleans *)
  | True | False -> Type.mk_bool
  | Not -> Type.mk_bb
  | And | Or | Imply | Iff -> Type.mk_bbb
  | Box(index) | Diamond(index) -> Type.mk_bb
  (* integers *)
  | Int(_) -> Type.mk_int
  | BigInt(_) -> Type.mk_int
  | BitNot -> Type.mk_ii
  | BitShiftLeft | BitShiftRight | BitAnd | BitOr | BitXor
  | Mod -> Type.mk_iii
  | Divides(_) -> Type.mk_ib
  (* real numbers *)
  | Real(_) -> Type.mk_real
  | FRsq | FRcp | FLog2 | FExp2 | FClamp -> Type.mk_rr
  | FPow -> Type.mk_rrr
  (* strings *)
  | String(_) -> Type.mk_string
  (* lists *)
  | Nil(ty) -> Type.mk_list ty
  | Cons(ty) -> Type.mk_fun [ty; Type.mk_list ty; Type.mk_list ty]
  (* uninterpreted functions *)
  | UFun(ty, _) -> ty
  (* path constructors *)
  | Call | Ret _ | Error -> raise (Global.NotImplemented "Const.type_of")
  (* functions *)
  | App | Flip | Comp | Tlu | FShift ->
    raise (Global.NotImplemented "Const.type_of")
  (* events *)
  | Event(_) -> Type.mk_ua(*@todo*)
  (* random value generation *)
  | RandBool -> Type.mk_bool(*@todo*)
  | RandInt -> Type.mk_int(*@todo*)
  | RandReal -> Type.mk_real(*@todo*)
  (* external value input *)
  | ReadBool(_, _) -> Type.mk_bool(*@todo*)
  | ReadInt(_, _) -> Type.mk_int(*@todo*)
  | ReadReal(_, _) -> Type.mk_real(*@todo*)
  (* type annotations *)
  | Annot(ty) -> Type.mk_fun [ty; ty]
  (* others *)
  | Undef -> assert false
  | Bot -> Type.mk_bot
  | Top -> Type.mk_top
  (* *)
  | Coerce(ty) -> ty

let arity_of c = Type.arity_of (type_of c)

let has_side_effect = function
  | Event(_)
  | RandBool | RandInt | RandReal
  | ReadBool(_, _) | ReadInt(_, _) | ReadReal(_, _) -> true
  | _ -> false

let ret_unit = type_of >> Type.args_ret >> snd >> (=) Type.mk_unit
let ret_bool = type_of >> Type.args_ret >> snd >> (=) Type.mk_bool
let ret_int = type_of >> Type.args_ret >> snd >> (=) Type.mk_int
let ret_real = type_of >> Type.args_ret >> snd >> (=) Type.mk_real

let is_bin = type_of >> Type.args_ret >> fst >> List.length >> (=) 2(* @todo *)
let is_ibop c = is_bin c && ret_int c
let is_rbop c = is_bin c && ret_real c

(** @require if is_infix c then c is x c y is of order-0
    App and Comp are of order-1!! *)
let rec is_infix c =
  match c with
  | Eq(_) | Neq(_) | Lt(_) | Gt(_) | Leq(_) | Geq(_)
  | Add(_) | Sub(_) | Mul(_) | Div(_)
  | And | Or | Imply | Iff
  | BitShiftLeft | BitShiftRight | BitAnd | BitOr | BitXor
  | Mod
  | Cons(_)
  | App | Comp -> true
  | _ -> false

let is_brel c = is_bin c && ret_bool c
let is_ubrel c = type_of c = Type.mk_uub
let is_bbrel c = type_of c = Type.mk_bbb
let is_ibrel c = type_of c = Type.mk_iib
let is_rbrel c = type_of c = Type.mk_rrb

let is_eq = function Eq(_)  -> true | _ -> false
let is_neq = function Neq(_)  -> true | _ -> false
let is_eq_neq c = is_eq c || is_neq c

let lift_int = function
  | Int(n) -> n
  | _ -> assert false

let lift_ibop = function
  | Add(ty) when Type.is_int ty -> (+)
  | Sub(ty) when Type.is_int ty -> (-)
  | Mul(ty) when Type.is_int ty -> ( * )
  | Div(ty) when Type.is_int ty -> (/)
  | Mod -> (mod)
  | _ -> assert false

let lift_rbop = function
  | Add(ty) when Type.is_real ty -> (+.)
  | Sub(ty) when Type.is_real ty -> (-.)
  | Mul(ty) when Type.is_real ty -> ( *. )
  | Div(ty) when Type.is_real ty -> (/.)
  | _ -> assert false

let lift_brel = function
  | Eq(_) -> (=)
  | Neq(_) -> (<>)
  | Lt(_) -> (<)
  | Gt(_) -> (>)
  | Leq(_) -> (<=)
  | Geq(_) -> (>=)
  | BinTrue(_) -> fun _ _ -> true
  | BinFalse(_) -> fun _ _ -> false
  | c ->
    Format.printf "%s" (string_of c);
    assert false

let lift_iurel = function
  | Divides(n) -> fun x -> x mod n = 0
  | c ->
    Format.printf "%s" (string_of c);
    assert false

(** {6 Printers} *)

let pr uprs ppf c =
  match c, uprs with
  | _, [upr1; upr2] when is_bin c && is_infix c ->
    Format.fprintf ppf "@[<hov>%a %s@ %a@]" upr1 () (string_of_infix c) upr2 ()
  | Annot(_), [upr1] -> upr1 ppf ()
  | _, _ ->
    Printer.concat_uprs_app
      ((Printer.upr_of String.pr (string_of c)) :: uprs)
      "@ "
      ppf
      ()

let pr_tex uprs ppf c =
  match c, uprs with
  | _, [upr1; upr2] when is_bin c && is_infix c ->
    Format.fprintf
      ppf "@[<hov>%a %s@ %a@]" upr1 () (tex_string_of_infix c) upr2 ()
  | Annot(_), [upr1] -> upr1 ppf ()
  | _, _ ->
    Printer.concat_uprs_app
      ((Printer.upr_of String.pr (tex_string_of c)) :: uprs)
      "@ "
      ppf
      ()

(** {6 Operators} *)

let not = function
  | Eq(ty) -> Neq(ty)
  | Neq(ty) -> Eq(ty)
  | Lt(ty) -> Geq(ty)
  | Gt(ty) -> Leq(ty)
  | Leq(ty) -> Gt(ty)
  | Geq(ty) -> Lt(ty)
  | BinTrue(ty) -> BinFalse(ty)
  | BinFalse(ty) -> BinTrue(ty)
  | c ->
    Logger.debug_assert_false
      ~on_failure:(fun () ->
          Format.printf "error in Const.not: %s@," (string_of c))
      ()

let neg = function
  | Eq(ty) -> Eq(ty)
  | Neq(ty) -> Neq(ty)
  | Lt(ty) -> Gt(ty)
  | Gt(ty) -> Lt(ty)
  | Leq(ty) -> Geq(ty)
  | Geq(ty) -> Leq(ty)
  | BinTrue(ty) -> BinTrue(ty)
  | BinFalse(ty) -> BinFalse(ty)
  | c ->
    Logger.debug_assert_false
      ~on_failure:(fun () ->
          Format.printf "error in Const.neg: %s@," (string_of c))
      ()

let rec cand c1 c2 =
  match c1, c2 with
  | Eq(ty1), Eq(ty2) when ty1 = ty2 -> Eq(ty1)
  | Eq(ty1), Neq(ty2) when ty1 = ty2 -> BinFalse(ty1)
  | Eq(ty1), Lt(ty2) when ty1 = ty2 -> BinFalse(ty1)
  | Eq(ty1), Gt(ty2) when ty1 = ty2 -> BinFalse(ty1)
  | Eq(ty1), Leq(ty2) when ty1 = ty2 -> Eq(ty1)
  | Eq(ty1), Geq(ty2) when ty1 = ty2 -> Eq(ty1)

  | Neq(ty1), Eq(ty2) when ty1 = ty2 -> cand c2 c1
  | Neq(ty1), Neq(ty2) when ty1 = ty2 -> Neq(ty1)
  | Neq(ty1), Lt(ty2) when ty1 = ty2 -> Lt(ty1)
  | Neq(ty1), Gt(ty2) when ty1 = ty2 -> Gt(ty1)
  | Neq(ty1), Leq(ty2) when ty1 = ty2 -> Lt(ty1)
  | Neq(ty1), Geq(ty2) when ty1 = ty2 -> Gt(ty1)

  | Lt(ty1), Eq(ty2) when ty1 = ty2 -> cand c2 c1
  | Lt(ty1), Neq(ty2) when ty1 = ty2 -> cand c2 c1
  | Lt(ty1), Lt(ty2) when ty1 = ty2 -> Lt(ty1)
  | Lt(ty1), Gt(ty2) when ty1 = ty2 -> BinFalse(ty1)
  | Lt(ty1), Leq(ty2) when ty1 = ty2 -> Lt(ty1)
  | Lt(ty1), Geq(ty2) when ty1 = ty2 -> BinFalse(ty1)

  | Gt(ty1), Eq(ty2) when ty1 = ty2 -> cand c2 c1
  | Gt(ty1), Neq(ty2) when ty1 = ty2 -> cand c2 c1
  | Gt(ty1), Lt(ty2) when ty1 = ty2 -> cand c2 c1
  | Gt(ty1), Gt(ty2) when ty1 = ty2 -> Gt(ty1)
  | Gt(ty1), Leq(ty2) when ty1 = ty2 -> BinFalse(ty1)
  | Gt(ty1), Geq(ty2) when ty1 = ty2 -> Gt(ty1)

  | Leq(ty1), Eq(ty2) when ty1 = ty2 -> cand c2 c1
  | Leq(ty1), Neq(ty2) when ty1 = ty2 -> cand c2 c1
  | Leq(ty1), Lt(ty2) when ty1 = ty2 -> cand c2 c1
  | Leq(ty1), Gt(ty2) when ty1 = ty2 -> cand c2 c1
  | Leq(ty1), Leq(ty2) when ty1 = ty2 -> Leq(ty1)
  | Leq(ty1), Geq(ty2) when ty1 = ty2 -> Eq(ty1)

  | Geq(ty1), Eq(ty2) when ty1 = ty2 -> cand c2 c1
  | Geq(ty1), Neq(ty2) when ty1 = ty2 -> cand c2 c1
  | Geq(ty1), Lt(ty2) when ty1 = ty2 -> cand c2 c1
  | Geq(ty1), Gt(ty2) when ty1 = ty2 -> cand c2 c1
  | Geq(ty1), Leq(ty2) when ty1 = ty2 -> cand c2 c1
  | Geq(ty1), Geq(ty2) when ty1 = ty2 -> Geq(ty1)

  | BinTrue(ty), c | c, BinTrue(ty) when ty = type_of c -> c
  | BinFalse(ty), c | c, BinFalse(ty) when ty = type_of c -> BinFalse(ty)

  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () ->
          Format.printf
            "error in Const.cand: %s, %s@,"
            (string_of c1) (string_of c2))
      ()

let rec cor c1 c2 =
  match c1, c2 with
  | Eq(ty1), Eq(ty2) when ty1 = ty2 -> Eq(ty1)
  | Eq(ty1), Neq(ty2) when ty1 = ty2 -> BinTrue(ty1)
  | Eq(ty1), Lt(ty2) when ty1 = ty2 -> Leq(ty1)
  | Eq(ty1), Gt(ty2) when ty1 = ty2 -> Geq(ty1)
  | Eq(ty1), Leq(ty2) when ty1 = ty2 -> Leq(ty1)
  | Eq(ty1), Geq(ty2) when ty1 = ty2 -> Geq(ty1)

  | Neq(ty1), Eq(ty2) when ty1 = ty2 -> cor c2 c1
  | Neq(ty1), Neq(ty2) when ty1 = ty2 -> Neq(ty1)
  | Neq(ty1), Lt(ty2) when ty1 = ty2 -> Neq(ty1)
  | Neq(ty1), Gt(ty2) when ty1 = ty2 -> Neq(ty1)
  | Neq(ty1), Leq(ty2) when ty1 = ty2 -> BinTrue(ty1)
  | Neq(ty1), Geq(ty2) when ty1 = ty2 -> BinTrue(ty1)

  | Lt(ty1), Eq(ty2) when ty1 = ty2 -> cor c2 c1
  | Lt(ty1), Neq(ty2) when ty1 = ty2 -> cor c2 c1
  | Lt(ty1), Lt(ty2) when ty1 = ty2 -> Lt(ty1)
  | Lt(ty1), Gt(ty2) when ty1 = ty2 -> Neq(ty1)
  | Lt(ty1), Leq(ty2) when ty1 = ty2 -> Leq(ty1)
  | Lt(ty1), Geq(ty2) when ty1 = ty2 -> BinTrue(ty1)

  | Gt(ty1), Eq(ty2) when ty1 = ty2 -> cor c2 c1
  | Gt(ty1), Neq(ty2) when ty1 = ty2 -> cor c2 c1
  | Gt(ty1), Lt(ty2) when ty1 = ty2 -> cor c2 c1
  | Gt(ty1), Gt(ty2) when ty1 = ty2 -> Gt(ty1)
  | Gt(ty1), Leq(ty2) when ty1 = ty2 -> BinTrue(ty1)
  | Gt(ty1), Geq(ty2) when ty1 = ty2 -> Geq(ty1)

  | Leq(ty1), Eq(ty2) when ty1 = ty2 -> cor c2 c1
  | Leq(ty1), Neq(ty2) when ty1 = ty2 -> cor c2 c1
  | Leq(ty1), Lt(ty2) when ty1 = ty2 -> cor c2 c1
  | Leq(ty1), Gt(ty2) when ty1 = ty2 -> cor c2 c1
  | Leq(ty1), Leq(ty2) when ty1 = ty2 -> Leq(ty1)
  | Leq(ty1), Geq(ty2) when ty1 = ty2 -> BinTrue(ty1)

  | Geq(ty1), Eq(ty2) when ty1 = ty2 -> cor c2 c1
  | Geq(ty1), Neq(ty2) when ty1 = ty2 -> cor c2 c1
  | Geq(ty1), Lt(ty2) when ty1 = ty2 -> cor c2 c1
  | Geq(ty1), Gt(ty2) when ty1 = ty2 -> cor c2 c1
  | Geq(ty1), Leq(ty2) when ty1 = ty2 -> cor c2 c1
  | Geq(ty1), Geq(ty2) when ty1 = ty2 -> Geq(ty1)

  | BinTrue(ty), c | c, BinTrue(ty) when ty = type_of c -> BinTrue(ty)
  | BinFalse(ty), c | c, BinFalse(ty) when ty = type_of c -> c

  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () ->
          Format.printf
            "error in Const.cor: %s, %s@,"
            (string_of c1) (string_of c2))
      ()

(* @todo consider !CunAtom.disable_elim_lt_gt *)
let rec candn (c1, n1) (c2, n2) =
  match c1, c2 with
  | Eq(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2 then [Eq(Type.mk_int), n1] else [BinFalse(Type.mk_int), 0]
  | Eq(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2 then [BinFalse(Type.mk_int), 0] else [Eq(Type.mk_int), n1]
  | Eq(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 >= n2 then [BinFalse(Type.mk_int), 0] else [Eq(Type.mk_int), n1]
  | Eq(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 <= n2 then [BinFalse(Type.mk_int), 0] else [Eq(Type.mk_int), n1]
  | Eq(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 > n2 then [BinFalse(Type.mk_int), 0] else [Eq(Type.mk_int), n1]
  | Eq(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 < n2 then [BinFalse(Type.mk_int), 0] else [Eq(Type.mk_int), n1]

  | Neq(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Neq(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2
    then [Neq(Type.mk_int), n1]
    (*else if n1 + 1 = n2
      then [Lt(Type.mk_int), n1 or Gt(Type.mk_int), n2]
      else if n2 + 1 = n1
      then [Lt(Type.mk_int), n2 or Gt(Type.mk_int), n1]*)
    else [Neq(Type.mk_int), n1; Neq(Type.mk_int), n2]
  | Neq(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 + 1 = n2
    then [Lt(Type.mk_int), n1](*integer!*)
    else if n1 >= n2
    then [Lt(Type.mk_int), n2]
    else [Neq(Type.mk_int), n1; Lt(Type.mk_int), n2]
  | Neq(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2 + 1
    then [Gt(Type.mk_int), n1](*integer!*)
    else if n1 <= n2
    then [Gt(Type.mk_int), n2]
    else [Neq(Type.mk_int), n1; Gt(Type.mk_int), n2]

  | Neq(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2
    then [Lt(Type.mk_int), n2]
    else if n1 > n2
    then [Leq(Type.mk_int), n2]
    else [Neq(Type.mk_int), n1; Leq(Type.mk_int), n2]
  | Neq(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2
    then [Gt(Type.mk_int), n2]
    else if n1 < n2
    then [Geq(Type.mk_int), n2]
    else [Neq(Type.mk_int), n1; Geq(Type.mk_int), n2]

  | Lt(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Lt(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Lt(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 <= n2 then [Lt(Type.mk_int), n1] else [Lt(Type.mk_int), n2]
  | Lt(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2 + 2
    then [Eq(Type.mk_int), n2 + 1]
    else if n1 <= n2 + 1
    then [BinFalse(Type.mk_int), 0]
    else [Lt(Type.mk_int), n1; Gt(Type.mk_int), n2]
  | Lt(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 <= n2
    then [Lt(Type.mk_int), n1]
    else [Leq(Type.mk_int), n2]
  | Lt(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2 + 1
    then [Eq(Type.mk_int), n2]
    else if n1 <= n2
    then [BinFalse(Type.mk_int), 0]
    else [Lt(Type.mk_int), n1; Geq(Type.mk_int), n2]

  | Gt(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Gt(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Gt(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Gt(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 >= n2 then [Gt(Type.mk_int), n1] else [Gt(Type.mk_int), n2]
  | Gt(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 + 1 = n2
    then [Eq(Type.mk_int), n2]
    else if n1 >= n2
    then [BinFalse(Type.mk_int), 0]
    else [Gt(Type.mk_int), n1; Leq(Type.mk_int), n2]
  | Gt(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 >= n2 then [Gt(Type.mk_int), n1] else [Geq(Type.mk_int), n2]

  | Leq(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Leq(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Leq(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Leq(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Leq(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 <= n2 then [Leq(Type.mk_int), n1] else [Leq(Type.mk_int), n2]
  | Leq(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2
    then [Eq(Type.mk_int), n1]
    else if n1 < n2
    then [BinFalse(Type.mk_int), 0]
    else [Leq(Type.mk_int), n1; Geq(Type.mk_int), n2]

  | Geq(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Geq(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Geq(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Geq(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Geq(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    candn (c2, n2) (c1, n1)
  | Geq(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 >= n2 then [Geq(Type.mk_int), n1] else [Geq(Type.mk_int), n2]

  | BinTrue(ty), _ when Type.is_int_unknown ty -> [c2, n2]
  | _, BinTrue(ty) -> [c1, n1]
  | BinFalse(ty), _ | _, BinFalse(ty) when Type.is_int_unknown ty ->
    [BinFalse(Type.mk_int), 0]

  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () ->
          Format.printf
            "error in Const.candn: (%s, %d), (%s, %d)@,"
            (string_of c1) n1
            (string_of c2) n2)
      ()

let rec candns cns =
  match cns with
  | [] ->
    Logger.debug_assert_false
      ~on_failure:(fun () -> Format.printf "error in Const.candns")
      ()
  | [cn] -> [cn]
  | cn :: cns' ->
    let cns'' = candns cns' in
    let cns''' = List.unique (List.concat_map (candn cn) cns'') in
    if Set_.equiv cns''' (cn :: cns'') then cns''' else candns cns'''

(* @todo consider !CunAtom.disable_elim_lt_gt *)
let rec corn (c1, n1) (c2, n2) =
  match c1, c2 with
  | Eq(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2
    then [Eq(Type.mk_int), n1]
    (*else if n1 + 1 = n2
      then [Geq(Type.mk_int), n1 and Leq(Type.mk_int), n2]
      else if n2 + 1 = n1
      then [Geq(Type.mk_int), n2 and Leq(Type.mk_int), n1]*)
    else [Eq(Type.mk_int), n1; Eq(Type.mk_int), n2]
  | Eq(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2 then [BinTrue(Type.mk_int), 0] else [Neq(Type.mk_int), n2]
  | Eq(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2
    then [Leq(Type.mk_int), n1]
    else if n1 < n2
    then [Lt(Type.mk_int), n2]
    else [Eq(Type.mk_int), n1; Lt(Type.mk_int), n2]
  | Eq(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2
    then [Geq(Type.mk_int), n1]
    else if n1 > n2
    then [Gt(Type.mk_int), n2]
    else [Eq(Type.mk_int), n1; Gt(Type.mk_int), n2]
  | Eq(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 <= n2
    then [Leq(Type.mk_int), n2]
    else [Eq(Type.mk_int), n1; Leq(Type.mk_int), n2]
  | Eq(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 >= n2
    then [Geq(Type.mk_int), n2]
    else [Eq(Type.mk_int), n1; Geq(Type.mk_int), n2]

  | Neq(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Neq(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2 then [Neq(Type.mk_int), n1] else [BinTrue(Type.mk_int), 0]
  | Neq(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 < n2 then [BinTrue(Type.mk_int), 0] else [Neq(Type.mk_int), n1]
  | Neq(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 > n2 then [BinTrue(Type.mk_int), 0] else [Neq(Type.mk_int), n1]
  | Neq(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 <= n2 then [BinTrue(Type.mk_int), 0] else [Neq(Type.mk_int), n1]
  | Neq(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 >= n2 then [BinTrue(Type.mk_int), 0] else [Neq(Type.mk_int), n1]

  | Lt(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Lt(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Lt(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 <= n2 then [Lt(Type.mk_int), n2] else [Lt(Type.mk_int), n1]
  | Lt(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2
    then [Neq(Type.mk_int), n1]
    else if n1 > n2
    then [BinTrue(Type.mk_int), 0]
    else [Lt(Type.mk_int), n1; Gt(Type.mk_int), n2]
  | Lt(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 <= n2 then [Leq(Type.mk_int), n2] else [Lt(Type.mk_int), n1]
  | Lt(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 + 1 = n2
    then [Neq(Type.mk_int), n1]
    else if n1 >= n2
    then [BinTrue(Type.mk_int), 0]
    else [Lt(Type.mk_int), n1; Geq(Type.mk_int), n2]

  | Gt(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Gt(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Gt(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Gt(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 >= n2 then [Gt(Type.mk_int), n2] else [Gt(Type.mk_int), n1]
  | Gt(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 = n2 + 1
    then [Neq(Type.mk_int), n1]
    else if n1 <= n2
    then [BinTrue(Type.mk_int), 0]
    else [Gt(Type.mk_int), n1; Leq(Type.mk_int), n2]
  | Gt(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 >= n2 then [Geq(Type.mk_int), n2] else [Gt(Type.mk_int), n1]

  | Leq(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Leq(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Leq(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Leq(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Leq(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 <= n2 then [Leq(Type.mk_int), n2] else [Leq(Type.mk_int), n1]
  | Leq(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 >= n2
    then [BinTrue(Type.mk_int), 0]
    else [Leq(Type.mk_int), n1; Geq(Type.mk_int), n2]

  | Geq(ty1), Eq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Geq(ty1), Neq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Geq(ty1), Lt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Geq(ty1), Gt(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Geq(ty1), Leq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    corn (c2, n2) (c1, n1)
  | Geq(ty1), Geq(ty2) when Type.is_int_unknown ty1 && Type.is_int_unknown ty2 ->
    if n1 >= n2 then [Geq(Type.mk_int), n2] else [Geq(Type.mk_int), n1]

  | BinTrue(ty), _ | _, BinTrue(ty) when Type.is_int_unknown ty ->
    [BinTrue(Type.mk_int), 0]
  | BinFalse(ty), _ when Type.is_int_unknown ty -> [c2, n2]
  | _, BinFalse(ty) when Type.is_int_unknown ty -> [c1, n1]

  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () ->
          Format.printf
            "error in Const.corn: (%s, %d), (%s, %d)@,"
            (string_of c1) n1
            (string_of c2) n2)
      ()

let rec corns cns =
  match cns with
  | [] ->
    Logger.debug_assert_false ()
      ~on_failure:(fun () -> Format.printf "error in Const.corns")
  | [cn] -> [cn]
  | cn :: cns' ->
    let cns'' = corns cns' in
    let cns''' = List.unique (List.concat_map (corn cn) cns'') in
    if Set_.equiv cns''' (cn :: cns'') then cns''' else corns cns'''

let eval cs =
  match cs with
  | [] -> assert false
  | c :: cs' ->
    if arity_of c = List.length cs' then
      if is_ibop c then
        let [n1; n2] = List.map lift_int cs' in
        [Int(lift_ibop c n1 n2)]
      else if is_ibrel c then
        let [n1; n2] = List.map lift_int cs' in
        if lift_brel c n1 n2 then [True] else [False]
      else raise (Global.NotImplemented "Const.eval")
    else cs


let subst_tvars tsub = function
  (* comparables *)
  | Eq(ty) -> Eq(Type.subst tsub ty)
  | Neq(ty) -> Neq(Type.subst tsub ty)
  | Lt(ty) -> Lt(Type.subst tsub ty)
  | Gt(ty) -> Gt(Type.subst tsub ty)
  | Leq(ty) -> Leq(Type.subst tsub ty)
  | Geq(ty) -> Geq(Type.subst tsub ty)
  | BinTrue(ty) -> BinTrue(Type.subst tsub ty)
  | BinFalse(ty) -> BinFalse(Type.subst tsub ty)
  (* numbers *)
  | Neg(ty) -> Neg(Type.subst tsub ty)
  | Add(ty) -> Add(Type.subst tsub ty)
  | Sub(ty) -> Sub(Type.subst tsub ty)
  | Mul(ty) -> Mul(Type.subst tsub ty)
  | Div(ty) -> Div(Type.subst tsub ty)
  | Max(ty) -> Max(Type.subst tsub ty)
  | Min(ty) -> Min(Type.subst tsub ty)
  (* unit *)
  | Unit -> Unit
  (* booleans *)
  | True -> True
  | False -> False
  | Not -> Not
  | And -> And
  | Or -> Or
  | Imply -> Imply
  | Iff -> Iff
  | Box(index) -> Box(index)
  | Diamond(index) -> Diamond(index)
  (* integers *)
  | Int(n) -> Int(n)
  | BigInt(n) -> BigInt(n)
  | BitNot -> BitNot
  | BitShiftLeft -> BitShiftLeft
  | BitShiftRight -> BitShiftRight
  | BitAnd -> BitAnd
  | BitOr -> BitOr
  | BitXor -> BitXor
  | Mod -> Mod
  | Divides(n) -> Divides(n)
  (* real numbers *)
  | Real(f) -> Real(f)
  | FRsq -> FRsq
  | FRcp -> FRcp
  | FLog2 -> FLog2
  | FExp2 -> FExp2
  | FClamp -> FClamp
  | FPow -> FPow
  (* strings *)
  | String(str) -> String(str)
  (* lists *)
  | Nil(ty) -> Nil(Type.subst tsub ty)
  | Cons(ty) -> Cons(Type.subst tsub ty)
  (* uninterpreted functions *)
  | UFun(ty, id) -> UFun(Type.subst tsub ty, id)
  (* path constructors *)
  | Call -> Call
  | Ret(ty) -> Ret(Type.subst tsub ty)
  | Error -> Error
  (* functions *)
  | App -> App
  | Flip -> Flip
  | Comp -> Comp
  | Tlu -> Tlu
  | FShift -> FShift
  (* events *)
  | Event(id) -> Event(id)
  (* random value generation *)
  | RandBool -> RandBool
  | RandInt -> RandInt
  | RandReal -> RandReal
  (* external value input *)
  | ReadBool(id, tys) -> ReadBool(id, List.map (Type.subst tsub) tys)
  | ReadInt(id, tys) -> ReadInt(id, List.map (Type.subst tsub) tys)
  | ReadReal(id, tys) -> ReadReal(id, List.map (Type.subst tsub) tys)
  (* type annotations *)
  | Annot(ty) -> Annot(Type.subst tsub ty)
  (* others *)
  | Undef -> Undef
  | Bot -> Bot
  | Top -> Top
  (* *)
  | Coerce(ty) -> Coerce(Type.subst tsub ty)


let int_to_real = function
  (* comparables *)
  | Eq(ty) when Type.is_int ty -> Eq(Type.mk_real)
  | Neq(ty) when Type.is_int ty -> Neq(Type.mk_real)
  | Lt(ty) when Type.is_int ty -> Lt(Type.mk_real)
  | Gt(ty) when Type.is_int ty -> Gt(Type.mk_real)
  | Leq(ty) when Type.is_int ty -> Leq(Type.mk_real)
  | Geq(ty) when Type.is_int ty -> Geq(Type.mk_real)
  | BinTrue(ty) when Type.is_int ty -> BinTrue(Type.mk_real)
  | BinFalse(ty) when Type.is_int ty -> BinFalse(Type.mk_real)
  (* numbers *)
  | Neg(ty) when Type.is_int ty -> Neg(Type.mk_real)
  | Add(ty) when Type.is_int ty -> Add(Type.mk_real)
  | Sub(ty) when Type.is_int ty -> Sub(Type.mk_real)
  | Mul(ty) when Type.is_int ty -> Mul(Type.mk_real)
  | Div(ty) when Type.is_int ty -> Div(Type.mk_real)
  | Max(ty) when Type.is_int ty -> Max(Type.mk_real)
  | Min(ty) when Type.is_int ty -> Min(Type.mk_real)
  (* integers *)
  | Int(n) -> Real(float_of_int n)
  | BigInt(n) -> Real(Big_int_Z.float_of_big_int n)
  | c -> c

let real_to_int = function
  (* comparables *)
  | Eq(ty) when Type.is_real ty -> Eq(Type.mk_int)
  | Neq(ty) when Type.is_real ty -> Neq(Type.mk_int)
  | Lt(ty) when Type.is_real ty -> Lt(Type.mk_int)
  | Gt(ty) when Type.is_real ty -> Gt(Type.mk_int)
  | Leq(ty) when Type.is_real ty -> Leq(Type.mk_int)
  | Geq(ty) when Type.is_real ty -> Geq(Type.mk_int)
  | BinTrue(ty) when Type.is_real ty -> BinTrue(Type.mk_int)
  | BinFalse(ty) when Type.is_real ty -> BinFalse(Type.mk_int)
  (* numbers *)
  | Neg(ty) when Type.is_real ty -> Neg(Type.mk_int)
  | Add(ty) when Type.is_real ty -> Add(Type.mk_int)
  | Sub(ty) when Type.is_real ty -> Sub(Type.mk_int)
  | Mul(ty) when Type.is_real ty -> Mul(Type.mk_int)
  | Div(ty) when Type.is_real ty -> Div(Type.mk_int)
  | Max(ty) when Type.is_real ty -> Max(Type.mk_int)
  | Min(ty) when Type.is_real ty -> Min(Type.mk_int)
  | c -> c
