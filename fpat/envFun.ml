open Util
open Combinator

(** Environments as functions *)

(** empty environment *)
let mk_empty x =
  Format.printf "\"%a\" not found@," Idnt.pr x;
  assert false

let update f bs x =
  try
    List.find_map
      (fun (y, t) -> if Idnt.equiv x y then Some(t) else None)
      bs
  with Not_found ->
    f x
