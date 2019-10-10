open Util
open Combinator

(** Bags (aka multisets, lists modulo permutation) *)

type 'a t = 'a list

(** {6 Inspectors} *)

let rec subset l1 l2 =
  match l1 with
  | [] -> true
  | x :: l1' ->
    try let l, _, r = List.pick ((=) x) l2 in subset l1' (l @ r)
    with Not_found -> false

let equiv l1 l2 = subset l1 l2 && subset l2 l1


let non_duplicated ?(eq = (=)) b =
  List.eq_length (List.unique ~eq b) b

let duplicated ?(eq = (=)) = non_duplicated ~eq >> not

let num_occurrences x = List.filter ((=) x) >> List.length

(** {6 Operators} *)

let rec inter l1 l2 =
  match l1 with
  | [] -> []
  | x :: l1' ->
    try let l, _, r = List.pick ((=) x) l2 in x :: inter l1' (l @ r)
    with Not_found -> inter l1' l2

let rec diff l1 l2 =
  match l1 with
  | [] -> []
  | x :: l1' ->
    try let l, _, r = List.pick ((=) x) l2 in diff l1' (l @ r)
    with Not_found -> x :: diff l1' l2


let rec get_dup_elems ?(cmp = (=)) = function
  | [] -> []
  | x :: b' ->
    let b'' = List.delete (cmp x) b' in
    if not (List.eq_length b' b'')
    then x :: get_dup_elems b''
    else get_dup_elems b'
