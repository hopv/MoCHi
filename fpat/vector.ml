open Util
open Combinator

(** Vectors *)

type 'a t = 'a list

let make v n = List.duplicate v n

let pr_float ppf v = Format.fprintf ppf "%a" (List.pr Float.pr " ") v
let pr_bool ppf v = Format.fprintf ppf "%a" (List.pr Bool.pr " ") v

let map f = List.map f
let dot xs ys = List.map2 (fun x -> fun y -> x *. y) xs ys |> Float.sum
let array_of = Array.of_list
let of_array = Array.to_list

(** [multiply \[x1; ... ; xm\] \[y1; ... ; yn\]]
    returns [\[f x1 y1; ... ; f x1 yn;
               ... ;
               f xm y1; ... ; f xm yn\]] *)
let multiply f xs ys = List.concat_map (fun x -> List.map (f x) ys) xs

(** [product f \[\[1; 2; 3\]; \[4\]; \[5; 6\]\]] returns
    [\[f \[1; 4; 5\]; f \[1; 4; 6\];
       f \[2; 4; 5\]; f \[2; 4; 6\];
       f \[3; 4; 5\]; f \[3; 4; 6\]\]] *)
let product f xss =
  let rec aux ac = function
    | [] -> [f ac]
    | xs :: xss ->
      xs
      |> List.map (fun x -> aux (ac @ [x]) xss)
      |> List.concat
  in
  aux [] xss

let producti f xss =
  let cnt = ref 0 in
  let rec aux ac xss =
    match xss with
    | [] ->
      let res = [f !cnt ac] in
      cnt := !cnt + 1;
      res
    | xs :: xss ->
       xs
       |> List.map (fun x -> aux (ac @ [x]) xss)
       |> List.concat
  in
  aux [] xss

(** [product_ f \[xs1; ...; xsn\]] returns
    [multiply f (...multiply f (multiply f xs1 xs2) xs3...) xsn]
    @require n > 0 *)
let product_ f = function
  | [] -> assert false
  | xs :: xss -> List.fold_left (multiply f) xs xss
