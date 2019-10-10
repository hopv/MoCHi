open Util
open Combinator

(** Function call identifiers *)

let pr ppf (x, uid) = Format.fprintf ppf "<%a@@%d>" Idnt.pr x uid

(** [root_id_of x] returns the call id of the root (top level) function call *)
let rec root_id_of = function
  | Idnt.V(_) -> raise Not_found
  | Idnt.C(_) -> assert false
  | Idnt.T(x', uid, _) -> try root_id_of x' with Not_found -> x', uid
let root_id_of x = try root_id_of x with Not_found -> assert false

(** [parent_id_of x] returns the call id of the parent function call *)
let parent_id_of = function
  | Idnt.V(_) -> assert false
  | Idnt.C(_) -> assert false
  | Idnt.T(x', uid, _) -> x', uid

let rec is_ancestor_or_eq (x, uid) (x', uid') =
  (x = x' && uid = uid')
  || match x' with
     | Idnt.V(_) -> false
     | Idnt.C(_) -> assert false
     | Idnt.T(x', uid', _) -> is_ancestor_or_eq (x, uid) (x', uid')

