open Util
open Combinator

(** Sets (aka lists modulo permutation and contraction) *)

type 'a t = 'a list

let subset ?(cmp = (=)) l1 l2 =
  List.for_all (fun x -> List.mem ~cmp:cmp x l2) l1
let equiv ?(cmp = (=)) l1 l2 =
  subset ~cmp:cmp l1 l2 && subset ~cmp:cmp l2 l1
let intersects ?(cmp = (=)) l1 l2 =
  List.exists (fun x -> List.mem ~cmp:cmp x l2) l1
let disjoint ?(cmp = (=)) l1 l2 =
  List.for_all (fun x -> not (List.mem ~cmp:cmp x l2)) l1

(*let rec diff xs ys =
  match xs, ys with
  | [], [] | [],  _ |  _, [] -> xs
  | x' :: xs', ys ->
     if List.mem x' ys then
       diff xs' ys
     else
       x' :: diff xs' ys*)
let diff ?(cmp = (=)) l1 l2 =
  List.filter (fun x -> not (List.mem ~cmp:cmp x l2)) l1
let inter ?(cmp = (=)) l1 l2 = List.filter (fun x -> List.mem ~cmp:cmp x l2) l1
let union ?(eq = (=)) l1 l2 = List.unique ~eq (l1 @ l2)


let rec power = function
  | [] -> [[]]
  | x :: s' -> s' |> power |> List.concat_map (fun s -> [s; x :: s])

let subsets_of_size n s =
  let rec aux n s1s2s =
    if n = 0 then s1s2s
    else
      List.concat_map
        (fun (s1, s2) ->
           (** @invariant Set_.equiv (s1 @ s2) s *)
           List.maplr (fun s11 x s12 -> s11 @ s12, x :: s2) s1)
        (aux (n - 1) s1s2s)
  in
  List.map snd (aux n [s, []])

let rec equiv_classes rel s =
  match s with
  | [] -> []
  | x :: s' ->
     let aux s1 s2 =
       List.partition (fun y -> List.exists (rel y) s1) s2
       |> Pair.map_fst ((@) s1)
     in
     let ls, rs =
       fix
         (uncurry2 aux)
         (comp2 List.eq_length fst fst)
         ([x], s')
     in
     ls :: equiv_classes rel rs

let rec representatives eqrel = function
  | [] -> []
  | x :: s' -> x :: representatives eqrel (List.filter (eqrel x >> not) s')

let minimal p s =
  let rec aux s1 s2 =
    match s1 with
    | [] -> s2
    | x :: s1' ->if p (s1' @ s2) then aux s1' s2 else aux s1' (x :: s2)
  in
  aux s []

let rec cover = function
  | [] -> []
  | s :: ss' ->
    if List.exists (flip subset s) ss' then cover ss' else s :: cover ss'

let rec reachable ids next =
  let rec loop ids nids =
    let ids' = ids @ nids in
    let nids' = diff (List.unique (List.concat_map next nids)) ids' in
    if nids' = [] then ids' else loop ids' nids'
  in
  loop [] ids
