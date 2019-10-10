open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type t =
  {size : int; (* number of nodes *)
   nodes : IntSet.t; (* elements must not be negative *)
   edges : (int * int) list;
   directed : bool;
   mutable in_neighbor : int list Array.t option;
   mutable out_neighbor : int list Array.t option}

let size g = g.size
let nodes g = g.nodes
let edges g = g.edges

let from_edges_aux directed edges =
  let nodes = List.fold_left (fun acc (x,y) -> IntSet.add x @@ IntSet.add y acc) IntSet.empty edges in
  let size = 1 + IntSet.fold max nodes 0 in
  let in_neighbor = None in
  let out_neighbor = None in
  {size; nodes; edges; directed; in_neighbor; out_neighbor}

let from_edges edges = from_edges_aux false edges
let from_directed_edges edges = from_edges_aux true edges

let fold_node f graph = IntSet.fold f graph.nodes
let fold_edge f graph = List.fold_right (fun (x,y) acc -> f x y acc) graph.edges

let save_as_dot filename ?(name_of=string_of_int) ?(attribute_of_node=Fun.const "") ?(attribute_of_edge=Fun.const "") graph =
  let oc = open_out filename in
  let ocf = Format.formatter_of_out_channel oc in
  Format.fprintf ocf "@[<v>digraph flow {@ ";
  IntSet.iter (fun x -> Format.fprintf ocf "  \"%s\" %s@ " (name_of x) (attribute_of_node x)) graph.nodes;
  List.iter (fun (x,y) -> Format.fprintf ocf "  \"%s\" -> \"%s\" %s@ " (name_of x) (name_of y) (attribute_of_edge (x,y))) graph.edges;
  Format.fprintf ocf "}@]@?";
  close_out oc

let make_in_neighbor ({size;nodes;edges;directed} as graph) =
  let in_neighbor = Array.make size [] in
  if directed then
    List.iter (fun (x,y) -> in_neighbor.(y) <- x::in_neighbor.(y)) edges
  else
    List.iter (fun (x,y) -> in_neighbor.(y) <- x::in_neighbor.(y); in_neighbor.(x) <- y::in_neighbor.(x)) edges;
  graph.in_neighbor <- Some in_neighbor;
  if directed then graph.out_neighbor <- Some in_neighbor;
  in_neighbor

let make_out_neighbor ({size;nodes;edges;directed} as graph) =
  if directed then
    let out_neighbor = Array.make size [] in
    List.iter (fun (x,y) -> out_neighbor.(x) <- y::out_neighbor.(x)) edges;
    graph.out_neighbor <- Some out_neighbor;
    out_neighbor
  else
    make_in_neighbor graph

let make_neighbor ({size;nodes;edges;directed} as graph) =
  if directed then
    let out_neighbor = Array.make size [] in
    let in_neighbor = Array.make size [] in
    List.iter (fun (x,y) -> out_neighbor.(x) <- y::out_neighbor.(x); in_neighbor.(y) <- x::in_neighbor.(y)) edges;
    graph.in_neighbor <- Some in_neighbor;
    graph.out_neighbor <- Some out_neighbor;
    in_neighbor, out_neighbor
  else
    let in_neighbor = make_in_neighbor graph in
    in_neighbor, in_neighbor

let get_neighbor ({in_neighbor;out_neighbor} as graph) =
  match in_neighbor, out_neighbor with
  | Some i, Some o -> i, o
  | Some i, None -> i, make_out_neighbor graph
  | None, Some o -> make_in_neighbor graph, o
  | None, None -> make_neighbor graph

let get_in_neighbor graph =
  match graph.in_neighbor with
  | Some i -> i
  | None -> make_in_neighbor graph

let get_out_neighbor ({in_neighbor} as graph) =
  match graph.out_neighbor with
  | Some o -> o
  | None -> make_out_neighbor graph

(* Kosaraju's algorithm *)
let scc ({size;nodes;edges} as graph) =
  let in_neighbor,out_neighbor = get_neighbor graph in
  let visited = Array.make size false in
  let root = Array.make size (-1) in
  let rec visit x acc =
    if not visited.(x) then
      begin
        visited.(x) <- true;
        x :: List.fold_right visit out_neighbor.(x) acc
      end
    else
      acc
  in
  let rec assign x r =
    if root.(x) < 0 then
      begin
        root.(x) <- r;
        List.iter (assign -$- r) in_neighbor.(x)
      end
  in
  IntSet.fold visit nodes []
  |> List.iter (Fun.copy assign);
  root

(* Dijkstra's algorithm *)
(* `dist x y < 0` means disconnected *)
let shortest_to ({size;nodes;edges} as graph) dist goal =
  let d = Array.make size (-1) in
  let in_neighbor = get_in_neighbor graph in
  d.(goal) <- 0;
  let rec take m xs1 xs2 =
    match xs2 with
    | [] -> m, xs1
    | x::xs2' ->
        let m',xs1' =
          if d.(x) >= 0 then
            match m with
            | None -> Some x, xs1
            | Some m' when d.(x) < d.(m') -> Some x, m'::xs1
            | _ -> m, x::xs1
          else
            m, x::xs1
        in
        take m' xs1' xs2'
  in
  let rec go i xs =
    if xs <> [] then
      let y,ys = take None [] xs in
      match y with
      | None -> ()
      | Some y ->
          let update z =
            let d_zy = dist z y in
            if d.(z) < 0 || d_zy >= 0 && d.(z) > d.(y) + d_zy then
              d.(z) <- d.(y) + d_zy
          in
          List.iter update in_neighbor.(y);
          go (i+1) ys
  in
  go goal @@ IntSet.elements nodes;
  d

(* graph must be DAG *)
let paths_to ({size;nodes;edges} as graph) goal =
  let paths = Array.make size None in
  let out_neighbor = get_out_neighbor graph in
  paths.(goal) <- Some [[]];
  let rec go x =
    match paths.(x) with
    | None ->
        let ps =
          out_neighbor.(x)
          |> List.map (Pair.add_right go)
          |> List.flatten_map (fun (y,ps) -> List.map (List.cons y) ps)
        in
        paths.(x) <- Some ps;
        ps
    | Some ps -> ps
  in
  IntSet.iter (go |- ignore) nodes;
  fun x -> Option.default [] paths.(x)

(* graph must be DAG *)
let hops_to {size;nodes;edges} goal =
  let init = -2 in
  let hops = Array.make size init in
  let out_neighbor = Array.make size [] in
  List.iter (fun (x,y) -> out_neighbor.(x) <- y::out_neighbor.(x)) edges;
  hops.(goal) <- 0;
  let rec go i prev x =
    if hops.(x) = init then
      let l =
        out_neighbor.(x)
        |> List.map (go (i+1) x)
        |> List.fold_left max (-1)
      in
      let l = if l < 0 then -1 else l + 1 in
      hops.(x) <- l;
      l
    else
      hops.(x)
  in
  IntSet.iter (go 0 (-1) |- ignore) nodes;
  hops

let hops_to ({size;nodes;edges} as graph) goals =
  let queue = Queue.create () in
  let hops = Array.make size (-1) in
  let in_neighbor = get_in_neighbor graph in
  List.iter (fun goal -> hops.(goal) <- 0; Queue.add goal queue) goals;
  let count = ref 0 in
  while not (Queue.is_empty queue) do
    incr count;
    let x = Queue.take queue in
    let neighbor = List.filter (fun y -> hops.(y) < 0) in_neighbor.(x) in
    let n = hops.(x) + 1 in
    List.iter (fun y -> hops.(y) <- n) neighbor;
    List.iter (Queue.add -$- queue) neighbor
  done;
  hops
