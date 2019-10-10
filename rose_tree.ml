open Util

type 'a t =  Node of 'a * 'a t list
type path = int list

let leaf a = Node (a, [])

let decomp (Node(l,ts)) = l, ts

let label t = fst @@ decomp t
let children t = snd @@ decomp t

let root = function
  | Node (l, []) -> l
  | _ -> raise (Invalid_argument "Rose_tree.root")

let rec flatten = function
  | Node (l, ts) -> l::(List.flatten_map flatten ts)

let rec map f path = function
  | Node (l, ts) -> Node(f path l, List.mapi (fun i t -> map f (path@[i]) t) ts)
let map f t = map f [] t

let rec fold f_node = function
  | Node (l, ts) -> f_node l @@ List.map (fold f_node) ts

let rec for_all f = function
  | Node (l, ts) -> f l && List.for_all (for_all f) ts

let rec exists f = function
  | Node (l, ts) -> f l || List.exists (exists f) ts

let rec proj path t =
  match path,t with
  | [],_ -> t
  | i::path',Node (l, ts) -> proj path' @@ List.nth ts i

let rec print pr fm t =
  match t with
  | Node (l, ts) -> Format.fprintf fm "(@[%a,@ [%a]@])" pr l (print_list (print pr) ";@ ") ts

let rec update path t' t =
  match path,t with
  | [], _ -> t'
  | i::path', Node (l, ts) ->
      Node (l, List.mapi (fun j t -> if i = j then update path' t' t else t) ts)

let rec zip t1 t2 =
  match t1, t2 with
  | Node (l1, ts1), Node (l2, ts2) -> Node ((l1, l2), List.map2 zip ts1 ts2)

let rec find_all_subtree f (Node(l,ts)) =
  let trees = List.flatten_map (find_all_subtree f) ts in
  if f (Node(l,ts)) then Node(l,ts)::trees else trees

let rec find_all_label f (Node(l,ts)) =
  let ls = List.flatten_map (find_all_label f) ts in
  if f l then l::ls else ls

let rec filter_map_subtree f (Node(l,ts)) =
  let ls = List.flatten_map (filter_map_subtree f) ts in
  match f (Node(l,ts)) with
  | None -> ls
  | Some r -> r::ls

let filter_map_label f t = filter_map_subtree (f -| label) t

let is_leaf (Node(_, ts)) = ts = []
