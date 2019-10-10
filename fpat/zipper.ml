open Util

(** Zippers *)

(** {6 Constructors} *)

type 'a tree =
  | Node of 'a * 'a tree list
type 'a path =
  | Top
  | Path of 'a path * 'a tree list * 'a * 'a tree list
type 'a location =
  | Loc of 'a tree * 'a path

(** {6 Auxiliary constructors for trees} *)

let make nd cs = Node(nd, cs)

(** {6 Inspectors for trees} *)

let get (Node(nd, _)) = nd
let children (Node(_, trs)) = trs
let rec nodes_of_tree (Node(nd, trs)) = nd :: List.concat_map nodes_of_tree trs

(** {6 Operators for trees} *)

let set (Node(_, trs)) nd = Node(nd, trs)

(** {6 Auxiliary constructors for paths} *)

let rec nodes_of_path = function
  | Top -> []
  | Path(up, trs1, nd, trs2) ->
    nodes_of_path up
    @ List.concat_map nodes_of_tree trs1
    @ [nd]
    @ List.concat_map nodes_of_tree trs2

(** {6 Auxiliary constructors for zippers} *)

let zipper tr = Loc(tr, Top)

(** {6 Operators for zippers} *)

let up (Loc(tr, p)) =
  match p with
  | Top -> raise Not_found
  | Path(up, trs1, nd, trs2) -> Loc(Node(nd, trs1 @ tr :: trs2), up)
let down (Loc(tr, p)) cond =
  match tr with
  | Node(nd, trs) ->
    let trs1, tr', trs2 =
      try List.pick (fun tr -> cond (get tr)) trs with Not_found -> assert false
     in
     Loc(tr', Path(p, trs1, nd, trs2))
let rec root (Loc(tr, p) as l) = match p with Top -> tr | _ -> root (up l)
let insert_down (Loc(Node(nd, trs), p)) tr = Loc(tr, Path(p, trs, nd, []))

(** {6 Inspectors for zippers} *)

let find_rightmost_leaf tr =
  let rec aux (Loc(Node(nd, trs), p) as loc) =
    match List.rev trs with
    | [] -> loc
    | tr' :: trs' -> aux (Loc(tr', Path(p, List.rev trs', nd, [])))
  in
  aux (zipper tr)

let find_leaves tr =
  let rec aux (Loc(Node(nd, trs), p) as loc) =
    match trs with
    | [] -> [loc]
    | _ ->
      List.concat
        (List.init
           (List.length trs)
           (fun i ->
              let trs1, tr :: trs2 = List.split_nth i trs in
              aux (Loc(tr, Path(p, trs1, nd, trs2)))))
  in
  aux (zipper tr)

let find_leftmost_leaf tr =
  let rec aux (Loc(Node(nd, trs), p) as loc) =
    match trs with
    | [] -> loc
    | tr' :: trs' -> aux (Loc(tr', Path(p, [], nd, trs')))
  in
  aux (zipper tr)

let find_all cond tr =
  let rec aux (Loc(Node(nd, trs), p) as loc) =
    (if cond nd then [loc] else [])
    @ (List.concat_map
         (fun tr -> aux (down loc (fun nd -> nd = get tr(*@todo*))))
         trs)
  in
  aux (zipper tr)
