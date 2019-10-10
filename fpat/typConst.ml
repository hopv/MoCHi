open Util
open Combinator

(** Type constants *)

(** {6 Constructors} *)

type t =
  (* base types *)
  | Unit
  | Bool
  | Int
  | Real
  | String
  | Ext of string (* external types *)
  | Bot
  | Top
  | Unknown
  (* composed types *)
  | Arrow
  | List
  (* intersection and union types *)
  | Inter of int
  | Union of int
  (* refinement types *)
  | Ref (*of t * Idnt.t * Formulat.t*)
  (* abstraction types *)
  | Abs (*of t * Idnt.t * Formulat.t*)

(** {6 Inspectors} *)

let arity_of = function
  | Unit | Bool | Int | Real | String -> 0
  | Ext(_) -> 0(*@todo*)
  | Bot | Top -> 0
  | Unknown -> 0

  | Arrow -> 2
  | List -> 1

  | Inter(n) -> n
  | Union(n) -> n
  | Ref -> 2
  | Abs -> 2

let rec string_of = function
  | Unit -> "unit"
  | Bool -> "bool"
  | Int -> "int"
  | Real -> "real"
  | String -> "string"
  | Ext(a) -> a
  | Bot -> "bot"
  | Top -> "top"
  | Unknown -> "unknown"

  | Arrow -> "arrow"
  | List -> "list"

  | Inter(n) -> "inter " ^ string_of_int n
  | Union(n) -> "union " ^ string_of_int n
  | Ref -> "refine"
  | Abs -> "abst"

let sexp_of = function
  | Unit -> "Unit"
  | Bool -> "Bool"
  | Int -> "Int"
  | Real -> "Real"
  | _ -> assert false

let is_base = function
  | Unit | Bool | Int | Real | String
  | Ext(_)(*@todo?*)
  | Bot | Top
  | Unknown -> true
  | _ -> false

let is_ext = function
  | Ext _ -> true
  | _ -> false

let is_unknown = function
  | Unknown -> true
  | _ -> false

let equiv_mod_unknown tyc1 tyc2 =
  tyc1 = tyc2
  || is_unknown tyc1
  || is_unknown tyc2

(** {6 Printers} *)

let pr uprs ppf c =
  match c, uprs with
  | Arrow, [upr1; upr2] ->
     Format.fprintf
       ppf
       "@[<hov>%a ->@ %a@]"
       upr1 ()
       upr2 ()
  | _, _ ->
     Printer.concat_uprs_app
       ((Printer.upr_of String.pr (string_of c)) :: uprs)
       "@ "
       ppf
       ()

let pr_tex uprs ppf c =
  match c, uprs with
  | Arrow, [upr1; upr2] ->
     Format.fprintf
       ppf
       "@[<hov>%a \\rightarrow@ %a@]"
       upr1 ()
       upr2 ()
  | _, _ ->
     Printer.concat_uprs_app
       ((Printer.upr_of String.pr (string_of c)) :: uprs)
       "@ "
       ppf
       ()
