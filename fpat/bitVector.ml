open Util
open Combinator

(** Bit vectors *)

let not =
  List.map (fun n -> if n = 0 then 1 else if n = 1 then 0 else assert false)

let inc =
  let rec aux = function
    | [] -> assert false
    | 0 :: bv -> 1 :: bv
    | 1 :: bv -> 0 :: aux bv
    | _ -> assert false
  in
  List.rev >> aux >> List.rev

let dec =
  let rec aux = function
    | [] -> assert false
    | 0 :: bv -> 1 :: aux bv
    | 1 :: bv -> 0 :: bv
    | _ -> assert false
  in
  List.rev >> aux >> List.rev

let of_nat n =
  assert (n >= 0);
  let rec aux bv n = if n = 0 then bv else aux (n mod 2 :: bv) (n / 2) in
  if n = 0 then [0] else aux [] n

let of_int bits n = assert false
(*
  if n >= 0 then of_nat bits n else inc (not (of_nat bits (-n)))
*)

let nat_of = List.fold_left (fun x y -> x * 2 + y) 0

let int_of bv =
  if List.hd bv = 0 then nat_of bv
  else if List.hd bv = 1 then -nat_of (not (dec bv))
  else assert false
