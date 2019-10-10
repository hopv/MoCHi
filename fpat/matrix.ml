open Util
open Combinator

(** Matrices *)

type 'a t = 'a Vector.t list

let make v m n = List.duplicate (List.duplicate v n) m

let pr_float ppf m =
  Format.fprintf ppf "@[<v>%a@]" (List.pr Vector.pr_float "@,") m

let rec transpose xss =
  if List.for_all (fun xs -> xs = []) xss then []
  else
    let xs, xss =
      xss
      |> List.map (function x :: xs -> x, xs | _ -> assert false )
      |> List.split
    in
    xs :: transpose xss

let cols = List.length
let rows xss = xss |> List.hd |> List.length

let elem i j xss = List.nth (List.nth xss i) j

let replace i j v xss =
  let ys = List.nth xss i in
  List.take i xss
  @ [List.take j ys @ [v] @ List.drop (j + 1) ys]
  @ List.drop (i + 1) xss



let thread xss =
  let minlength = Integer.min_list (List.map List.length xss) in
  List.map
    (fun k -> List.map (fun ys -> List.nth ys k) xss)
    (List.from_to 0 (minlength - 1))

let row i xss = List.nth xss i

let column i xss = List.nth (thread(*@todo replace this with transpose*) xss) i

let diag_rd (i, j) xss =
  let n = List.length xss in
  List.from_to (-n) n
  |> List.filter (fun k -> i + k >= 0 && i + k < n && j + k >= 0 && j + k < n)
  |> List.map (fun k -> List.nth (List.nth xss (i + k)) (j + k))

let diag_ld (i, j) xss =
  let n = List.length xss in
  List.from_to (-n) n
  |> List.filter (fun k -> i + k >= 0 && i + k < n && j - k >= 0 && j - k < n)
  |> List.map (fun k -> List.nth (List.nth xss (i + k)) (j - k))



let map f = List.map (List.map f )

let id one zero n =
  List.gen n (fun i ->
      List.gen n (fun j -> if i = j then one else zero))

let array_of xss = Array.of_list (List.map Array.of_list xss)
let of_array ar = Array.to_list (Array.map Array.to_list ar)
