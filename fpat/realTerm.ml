open Util
open Combinator

include Term

(** {6 Auxiliary constructors} *)

let make f = mk_const (Const.Real f)
let zero = make 0.0
let one = make 1.0
let of_int n =  make (float_of_int n)

(** {6 Operators} *)

let neg t = mk_app (mk_const (Const.Neg Type.mk_real)) [t]
let rsq t = mk_app (mk_const Const.FRsq) [t]
let rcp t = mk_app (mk_const Const.FRcp) [t]
let log2 t = mk_app (mk_const Const.FLog2) [t]
let exp2 t = mk_app (mk_const Const.FExp2) [t]
let add t1 t2 =
  match t1, t2 with
  | Const(Const.Real(0.0)), t | t, Const(Const.Real(0.0)) -> t
  | _, _ -> mk_app (mk_const (Const.Add Type.mk_real)) [t1; t2]
let mul t1 t2 =
  match t1, t2 with
  | Const(Const.Real(0.0)), t | t, Const(Const.Real(0.0)) -> zero
  | Const(Const.Real(1.0)), t | t, Const(Const.Real(1.0)) -> t
  | _, _ -> mk_app (mk_const (Const.Mul Type.mk_real)) [t1; t2]
let div t1 t2 = NumTerm.div Type.mk_real t1 t2
let sub t1 t2 =
  match t1, t2 with
  | Const(Const.Real(0.0)), t -> mul (make (-1.0)) t
  | t, Const(Const.Real(0.0)) -> t
  | _, _ -> mk_app (mk_const (Const.Sub Type.mk_real)) [t1; t2]
let max t1 t2=
  if t1 = t2 then t1 else mk_app (mk_const (Const.Max(Type.mk_real))) [t1; t2]
let min t1 t2 =
  if t1 = t2 then t1 else mk_app (mk_const (Const.Min(Type.mk_real))) [t1; t2]
let sum ts =
  let fs, ts =
    List.partition_map
      (function
        | Const(Const.Real(f)) -> `L(f)
        | t -> `R(t))
      ts
  in
  let f = List.fold_left (fun f1 f2 -> f1 +. f2) 0.0 fs in
  if ts = [] then make f
  else List.fold_left (fun t1 t2 -> add t1 t2) (make f) ts
let prod ts =
  let fs, ts =
    List.partition_map
      (function
        | Const(Const.Real(f)) -> `L(f)
        | t -> `R(t))
      ts
  in
  let f = List.fold_left (fun f1 f2 -> f1 *. f2) 1.0 fs in
  if ts = [] then make f
  else List.fold_left (fun t1 t2 -> mul t1 t2) (make f) ts

(** {6 Inspectors} *)

let rec sum_of t =
  match fun_args t with
  | Const(Const.Add(ty)), [t1; t2] when Type.is_real ty ->
    sum_of t1 @ sum_of t2
  | _ -> [t]

let rec prod_of t =
  match fun_args t with
  | Const(Const.Mul(ty)), [t1; t2] when Type.is_real ty ->
    prod_of t1 @ prod_of t2
  | _ -> [t]

let of_lin_exp (nxs, n) =
  (if n = 0.0 then [] else [make n])
  @ List.map
    (fun (n, x) ->
       if n = 0.0 then assert false
       else if n = 1.0 then mk_var x
       else mul (make n) (mk_var x))
    nxs
  |> sum

let rec of_sexp = function
  | Sexp.S(s) when String.is_float s -> make (float_of_string s)
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
  | e ->
    Format.printf "sexp: %a@," Sexp.pr e;
    assert false

let of_lin_exp (nxs, n) =
  (if n = 0.0 then [] else [make n])
  @ List.map
    (fun (n, x) ->
       if n = 0.0 then assert false
       else if n = 1.0 then mk_var x
       else mul (make n) (mk_var x))
    nxs
  |> sum
let of_mono_exp (n, xs) =
  if n = 0. then assert false
  else if n = 1. then prod (List.map mk_var xs)
  else prod (make n :: List.map mk_var xs)
let of_poly_exp = List.map of_mono_exp >> sum

let float_of = function
  | Const(Const.Real f) -> f
  | _ -> raise Not_found
