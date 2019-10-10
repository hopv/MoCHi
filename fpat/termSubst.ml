open Util
open Combinator

(** Term substitutions *)

include Map_

type elem = (Idnt.t, Term.t) _elem
type t = (Idnt.t, Term.t) _t

(** {6 Printers} *)

let pr_elem ppf (x, t) = Format.fprintf ppf "%a = %a" Idnt.pr x Term.pr t
let pr ppf tsub = Format.fprintf ppf "%a" (List.pr pr_elem "@,") tsub

(** {6 Morphisms} *)

let map_term f = List.map (fun (x, t) -> x, f t)

(** {6 Inspectors} *)

let fvs tsub = List.concat_map (snd >> Term.fvs) tsub

(** {6 Auxiliary constructors} *)

let of_vmap = List.map (fun (x, y) -> x, Term.mk_var y)
let of_vars = Idnt.new_vmap >> of_vmap

let of_terms tsub = List.map (fun t -> Idnt.new_var (), t) tsub
let of_tenvs tenv1 tenv2 =
  List.map2
    (fun (x, ty) (x', ty') ->
       Logger.debug_assert (fun () -> ty = ty');
       x, Term.mk_var x')
    tenv1 tenv2

(** {6 Operators} *)

let subst tsub = map_term (Term.subst tsub)

let complement ?(real=false) cs sol =
  sol @
  (sol |> Map_.dom |> Set_.diff cs
   |> List.map (flip Pair.make (if real
                                then Term.mk_const (Const.Real 0.0)
                                else Term.mk_const (Const.Int 0))))


let rec normalize tsubL = function
  | [] -> tsubL
  | (x, t) :: tsubR ->
    normalize
      (subst [x, t] tsubL @ [x, t])
      (subst [x, t] tsubR)
let normalize tsub = normalize [] tsub
