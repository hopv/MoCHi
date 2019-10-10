open Util
open Combinator

(** Maps *)

type ('a, 'b) _elem = 'a * 'b
type ('a, 'b) _t = ('a, 'b) _elem list

(** {6 Printers} *)

let pr_elem epr1 epr2 ppf (x, y) =
  Format.fprintf ppf "@[<hov>%a ->@ %a@]" epr1 x epr2 y
let pr epr1 epr2 ppf =
  Format.fprintf ppf "%a" (List.pr (pr_elem epr1 epr2) "@,")

(** {6 Morphisms} *)

let map_dom f = List.map (fun (x, y) -> f x, y)
let map_codom f = List.map (fun (x, y) -> x, f y)

(** {6 Inspectors} *)

let apply m x = List.assoc x m
let apply_default d m x = List.assoc_default d x m
let applyD = apply_default
let apply_fail m x = List.assoc_fail x m
let applyF = apply_fail

let apply_inverse m x =
  List.find_map (fun (a, b) -> if b = x then Some a else None) m
let apply_inverse_fail m x =
  try apply_inverse m x with Not_found -> assert false

let non_dup m =
  m |> List.classify (comp2 (=) fst fst)
  |> List.for_all (List.unique >> List.length >> (=) 1)
let is_map m = m |> List.map fst |> Bag.non_duplicated
let in_dom = List.mem_assoc

let dom m = List.map fst m
let codom m = List.map snd m

(** {6 Operators} *)

let diff m xs = List.filter (fun (x, _) -> not (List.mem x xs)) m
let restrict m xs = List.filter (fun (x, _) -> List.mem x xs) m
let update m x y = (x, y) :: diff m [x]

let rec merge = function
  | [] -> []
  | (x, v) :: m' ->
    let t, f = List.partition (fst >> (=) x) m' in
    (x, v @ List.concat_map snd t) :: merge f
let merge2 m1 m2 = merge (m1 @ m2)
