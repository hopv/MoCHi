type 'a t = Leaf of 'a | Node of 'a t * 'a t
type path = int list

let root = function
  | Leaf t -> t
  | Node _ -> raise (Invalid_argument "Tree.root")
let rec flatten = function
  | Leaf t -> [t]
  | Node(lhs,rhs) -> flatten lhs @ flatten rhs

let rec map f path = function
  | Leaf t -> Leaf (f path t)
  | Node(t1,t2) -> Node(map f (path@[1]) t1, map f (path@[2]) t2)
let map f t = map f [] t

let rec fold f_node f_leaf = function
  | Leaf typ -> f_leaf typ
  | Node(t1,t2) -> f_node (fold f_node f_leaf t1) (fold f_node f_leaf t2)

let rec for_all f = function
  | Leaf typ -> f typ
  | Node(t1,t2) -> for_all f t1 && for_all f t2

let rec exists f = function
  | Leaf typ -> f typ
  | Node(t1,t2) -> exists f t1 || exists f t2

let rec proj path t =
  match path,t with
  | [],_ -> t
  | 1::path',Node(t',_) -> proj path' t'
  | 2::path',Node(_,t') -> proj path' t'
  | _ -> assert false

let rec print pr fm t =
  match t with
  | Leaf x -> pr fm x
  | Node(lhs,rhs) -> Format.fprintf fm "(%a,%a)" (print pr) lhs (print pr) rhs

let rec update path t' t =
  match path,t with
  | [], _ -> t'
  | 1::path', Node(t1,t2) -> Node(update path' t' t1, t2)
  | 2::path', Node(t1,t2) -> Node(t1, update path' t' t2)
  | _ -> failwith "Tree.update"

let rec zip t1 t2 =
  match t1, t2 with
  | Leaf x, Leaf y -> Leaf (x,y)
  | Node(t11,t12), Node(t21,t22) -> Node(zip t11 t21, zip t12 t22)
  | _ -> raise (Invalid_argument "Tree.zip")
