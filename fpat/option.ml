open Util

(** Options *)

let some x = Some(x)
let return = some

let list_of = function None -> [] | Some(x) -> [x]
let of_list = function [] -> None | xs -> Some(xs)

let elem_of = function None -> assert false | Some(x) -> x
let elem_of_nf = function None -> raise Not_found | Some(x) -> x
let nf_of f x = match f x with None -> raise Not_found | Some(res) -> res

let of_nf f x = try Some(f x) with Not_found -> None
let of_exc f x = try Some(f x) with _ -> None

let pr epr none ppf = function
  | None -> Format.fprintf ppf "%s" none
  | Some(x) -> Format.fprintf ppf "%a" epr x

let fold none some = function None -> none | Some(x) -> some x
let map f = function None -> None | Some(x) -> Some(f x)
