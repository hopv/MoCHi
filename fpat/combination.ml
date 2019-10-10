open Util
open Combinator

(** Combinations *)

let comb2 xs =
  List.concat_mapi
    (fun i x -> List.map (Pair.make x) (List.drop (i + 1) xs))
    xs
