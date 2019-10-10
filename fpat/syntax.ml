open Util
open Combinator

(* Hylo用 *)
type variable =
  | Var of string
  | Intlit of int
  | Plus
  | Minus
  | Mul
  | Div
  | Max
  | Min
  | Less
  | Greater
  | Error

type c =
  | Nil
  | Cons
  | True
  | False

type p =
  | Pc of c * p
  | Pt of p list
  | Pv of variable

type term =
  | Tv of variable
  | Tt of term list
  | Ta of variable * term
  | Tc of c * term

type r = Al of (p * term) list

type vs = V of variable | Vs of variable list

type b = B of vs * term * r

type decl = Def of variable * b

module VSet = Set.Make
  (struct
    type t = variable
    let compare = compare
   end)

module VTSet = Set.Make
  (struct
    type t = variable * term
    let compare = compare
   end)

type typ =
  Int
| A
| Arrow of (typ * typ)
| List of typ
| Tree of typ

type fnct =
  Identity
| Constant of string
| Product of fnct list
| Sum of fnct list

type expr =
  App of expr * expr
| Circle of expr * expr
| Plus of expr list
| InvTri of expr list
| Tag of int * expr
| Lambda of expr * expr
| Id
| Case of expr * ((expr * expr) list)
(* | Term of term この方法ではなく、term -> expr の関数を書くべき *代入ができない *)
| Const of c
| EVar of variable
| Tuple of expr list
| Banana of expr * fnct
| Envelope of hylo
| Wildcard



(* 仕様用 *)
type eq =
  | Gt
  | Lt
  | Eq
  | Geq
  | Leq
  | Neq

type fs =
  | Fun of variable
  | Circ of (variable * fs)

type spec = fs * eq * variable

let rec expr_of_p = function
  | Pc (c, p) -> App (Const c, expr_of_p p)
  | Pt ps -> Tuple (List.map expr_of_p ps)
  | Pv v -> EVar v

let rec expr_of_term = function
  | Tv v -> EVar v
  | Tt ts ->
   begin
     match ts with
     | [t] -> expr_of_term t
     | ts -> Tuple (List.map expr_of_term ts)
   end
  | Ta (v, t) -> App (EVar v, expr_of_term t)
  | Tc (c, t) -> App (Const c, expr_of_term t)
