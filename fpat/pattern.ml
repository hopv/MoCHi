open Util
open Combinator

(** Patterns *)

(* @todo reimplement this module using AbsTerm *)

type t =
  | V of Idnt.t (** variable *)
  | U (** unit *)
  | T of t list (** tuple : length ts >= 2 *)
  | K of Idnt.t * t (** constructor *)
  | C of constant (** constant *)
  | W (** wild pattern *)
and constant = Const_int of int | Const_bool of bool

let of_list = function
  | [] -> U
  | [p] -> p
  | ps -> T(ps)

let list_of = function
  | U -> []
  | T(ps) -> ps
  | p -> [p]

let mk_var x = V(x)

(* @todo make this modulo alpha conv *)
let equiv p1 p2 = p1 = p2

let rec pr ppf = function
  | V(x) -> Idnt.pr ppf x
  | U -> String.pr ppf "()"
  | T(ps) -> Format.fprintf ppf "(%a)" (List.pr pr ", ") ps
  | K(c, p) -> Format.fprintf ppf "(%a %a)" Idnt.pr c pr p
  | C(t) -> Format.fprintf ppf "()"
  | W -> String.pr ppf "_"
let rec pr_tex ppf = function
  | V(x) -> Idnt.pr ppf x
  | U -> String.pr ppf "()"
  | T(ps) -> Format.fprintf ppf "(%a)" (List.pr pr ", ") ps
  | K(c, p) -> Format.fprintf ppf "(%a %a)" Idnt.pr_tex c pr p
  | C(t) -> Format.fprintf ppf "()"
  | W -> String.pr ppf "_"
let pr_const ppf = function
  | Const_int(n) -> Format.fprintf ppf "%d" n
  | Const_bool(b) -> Format.fprintf ppf "%b" b

let rec occurs x = function
  | V(y) -> x = y
  | U -> false
  | T(ps) -> List.exists (occurs x) ps
  | K(_, p) -> occurs x p
  | C(_) -> false
  | W -> false

let rec fvs p =
  match p with
  | V(x) -> if Idnt.is_coeff x then [] else [x]
  | U -> []
  | T(ps) -> List.concat_map fvs ps
  | K(_, p) -> fvs p
  | C(_) -> []
  | W -> []

let rec fcs p =
  match p with
  | V(x) -> []
  | U -> []
  | T(ps) -> List.concat_map fcs ps
  | K(c, p) -> c :: fcs p
  | C(_) -> []
  | W -> []

let rec coeffs p =
  match p with
  | V(x) -> if Idnt.is_coeff x then [x] else []
  | U -> []
  | T(ps) -> List.concat_map coeffs ps
  | K(_, p) -> coeffs p
  | C(_) -> []
  | W -> []

(* we assume here that the argument [p] is linear *)
let new_vmap = fvs >> Idnt.new_vmap

let rec rename vmap p =
  match p with
  | V(x) -> V(Map_.apply_default x vmap x)
  | U -> U
  | T(ps) -> T(List.map (rename vmap) ps)
  | K(c, p) -> K(c, rename vmap p)
  | C(t) -> C(t)
  | W -> W


let rec var_list_of p =
  match p with
  | V(x) -> [x]
  | T(ps) -> List.concat_map var_list_of ps
  | _ -> assert false

let rec has_args = function
  | K(_, T _) -> true
  | T ts -> true
  | C _ -> true
  | _ -> false
