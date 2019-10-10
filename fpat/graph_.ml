open Util
open Combinator

(** Graphs *)

(* @todo
walk can be of the length 0
trail: walk with no repetition of an edge
path: walk with no repetition of a vertex

path <: trail <: walk

path can be of the length 0
# a single node is connected

circuit: trail with the length >= 1 that starts and ends with the same vertex
cycle: path with the length >= 1 that starts and ends with the same vertex

cycle <: circuit

trail/circuit is Eulerian if it contains every edge of the graph
path/cycle is Hamitonian if it contains every vertex of the graph
*)

(** @todo there is a bug related to vertices? *)
let save_graphviz filename vertices edges =
  let oc = open_out filename in
  let ocf = Format.formatter_of_out_channel oc in
  Format.fprintf ocf "@[<v>digraph flow {@ ";

  List.iter
    (fun (vertex, attribute) ->
       Format.fprintf ocf "  \"%s\" %s@ " vertex attribute)
    vertices;
  List.iter
    (fun (vertex1, vertex2, attribute) ->
       Format.fprintf ocf "  \"%s\" -> \"%s\" %s@ " vertex1 vertex2 attribute)
    edges;

  Format.fprintf ocf "}@]@?";
  close_out oc

let succs es v =
  List.filter_map (fun (v1, v2) -> if v1 = v then Some(v2) else None) es
let preds es v =
  List.filter_map (fun (v1, v2) -> if v2 = v then Some(v1) else None) es

let rec assign es assigned v root =
  if List.mem_assoc v assigned then assigned
  else
    List.fold_left
      (fun assigned v -> assign es assigned v root)
      ((v, root) :: assigned)
      (preds es v)

(** Kosaraju's algorithm *)
let rec visit es visited l v =
  if List.mem v visited then
    (visited, l)
  else
    let visited, l =
      List.fold_left
        (uncurry2 (visit es))
        (v :: visited, l)
        (succs es v)
    in
    (visited, v :: l)

let scc es =
  let vs = List.map fst es @ List.map snd es |> List.unique in
  let _, l = List.fold_left (uncurry2 (visit es)) ([], []) vs in
  List.fold_left (fun assigned v -> assign es assigned v v) [] l
