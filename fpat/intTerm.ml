open Combinator
open Util

include Term

(** {6 Auxiliary constructors} *)

let make n = mk_const (Const.Int n)
let of_big_int n = mk_const (Const.BigInt n)
let zero = make 0
let one = make 1

(** {6 Inspectors} *)

let is_zero t = t = zero
let is_one t = t = one

(** {6 Operators} *)

let add t1 t2 = NumTerm.add Type.mk_int t1 t2
let sub t1 t2 = NumTerm.sub Type.mk_int t1 t2
let mul t1 t2 = NumTerm.mul Type.mk_int t1 t2
let div t1 t2 = if is_one t2 then t1 else NumTerm.div Type.mk_int t1 t2
let max t1 t2 = NumTerm.max Type.mk_int t1 t2
let min t1 t2 = NumTerm.min Type.mk_int t1 t2
let mk_mod t1 t2 = NumTerm.mk_bop Const.Mod t1 t2

let rec sum = function
  | [] -> zero
  | [t] -> t
  | t :: ts' when is_zero t -> sum ts'
  | t :: ts' ->
    match sum ts' with
    | t' when is_zero t' -> t
    | t' -> add t t'

let prod ts =
  let rec aux = function
    | [] -> one
    | [t] -> t
    | t :: ts' when is_one t -> aux ts'
    | t :: _ when is_zero t -> raise Not_found
    | t :: ts' ->
      match aux ts' with
      | t' when is_one t' -> t
      | t' -> mul t t'
  in
  try aux ts with Not_found -> zero

(** {6 Auxiliary constructors} *)

let of_lin_exp (nxs, n) =
  (if n = 0 then [] else [make n])
  @ List.map
    (fun (n, x) ->
       if n = 0 then assert false
       else if n = 1 then mk_var x
       else mul (make n) (mk_var x))
    nxs
  |> sum
let of_mono_exp (n, xs) =
  if n = 0 then assert false
  else if n = 1 then prod (List.map mk_var xs)
  else prod (make n :: List.map mk_var xs)
let of_poly_exp = List.map of_mono_exp >> sum
let of_lin_poly_exp _ = raise (Global.NotImplemented "IntTerm.of_lin_poly_exp")

(** {6 Inspectors} *)

let int_of = function
  | Const(Const.Int(n)) -> n
  | _ -> raise Not_found

let is_const = function
  | Const(Const.Int(n)) -> true
  | _ -> false

let equiv t1 t2 = is_const t1 && is_const t2 && int_of t1 = int_of t2
let (>) t1 t2 = is_const t1 && is_const t2 && int_of t1 > int_of t2
let (<) t1 t2 = is_const t1 && is_const t2 && int_of t1 < int_of t2

(** {6 Operators} *)

let neg t =
  if is_const t then make (-int_of t) else NumTerm.neg Type.mk_int t

(** @require not (PolyIntExp.is_zero pol)
    @ensure the result does not contain make 1 *)
let factorize pol =
  let n, pol = PolyIntExp.gcd_coeff pol in
  let xs, pol = PolyIntExp.gcd_vars pol in
  (if n = 1 then [] else [make n])
  @ List.map mk_var xs
  @ (if PolyIntExp.is_one pol then [] else [of_poly_exp pol])

(** {6 Auxiliary constructors} *)

let rec of_sexp = function
  | Sexp.S(s) when String.is_int s -> make (int_of_string s)
  | Sexp.S(s) -> Term.var_of_string s
  | Sexp.L(Sexp.S("+") :: e1 :: es) ->
    List.fold_left
      (fun acc e -> add acc (of_sexp e))
      (of_sexp e1) es
  | Sexp.L(Sexp.S("-") :: [e]) -> neg (of_sexp e)
  | Sexp.L(Sexp.S("-") :: e1 :: es) ->
    List.fold_left
      (fun acc e -> sub acc (of_sexp e))
      (of_sexp e1) es
  | Sexp.L(Sexp.S("*") :: e1 :: es) ->
    List.fold_left
      (fun acc e -> mul acc (of_sexp e))
      (of_sexp e1) es
  | Sexp.L(Sexp.S("/") :: e1 :: es) ->
    List.fold_left
      (fun acc e -> div acc (of_sexp e))
      (of_sexp e1) es
  | e ->
    Format.printf "sexp: %a@," Sexp.pr e;
    assert false
