open Util
open Syntax
open Term_util


module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let normalize = Tr.make ()
let normalize_term t =
  let t' = normalize.term_rec t in
  match t'.desc with
  | App(t1, ts) ->
      let aux t1 t2 = make_app_raw t1 [t2] in
      List.fold_left aux t1 ts
  | _ -> t'
let () = normalize.term <- normalize_term
let normalize = normalize.term


let add_flow flow t1 t2 =
  let id1 = get_id t1 in
  let id2 = get_id t2 in
  try
    let fl = Hashtbl.find flow id1 in
    let fl' = IntSet.union (Hashtbl.find flow id2) fl in
    if IntSet.cardinal fl = IntSet.cardinal fl'
    then false
    else (Hashtbl.replace flow id1 fl'; true)
  with Not_found -> assert false

let get_flow map flow t =
  get_id t
  |> Hashtbl.find flow
  |> IntSet.elements
  |> List.map (Hashtbl.find map)

let update_var = Col2.make false (||)
let update_var_term (flow,x,t') t =
  match t.desc with
  | Var (LId y) when Id.(x = y) -> add_flow flow t t'
  | Var _ -> unsupported "CFA"
  | _ -> update_var.term_rec (flow,x,t') t
let () = update_var.term <- update_var_term
let update_var flow x t' t = update_var.term (flow,x,t') t

let rec update map flow t =
  let (||) = (||) in (* for strictness *)
  match t.desc with
  | Const _ -> add_flow flow t t
  | Var _ -> false
  | Event _ -> false
  | Bottom -> false
  | Fun(_, t1) -> update map flow t1 || add_flow flow t t
  | App(t1, [t2]) ->
      let ts1 = get_flow map flow t1 in
      let aux t3 =
        match t3.desc with
        | Fun(x, t3') -> update_var flow x t2 t3' || add_flow flow t t3'
        | _ -> false
      in
      update map flow t1 || update map flow t2 || List.fold_left (fun b t -> b || aux t) false ts1
  | Local(Decl_let bindings, t2) ->
      let b =
        let aux b (f,t1) = b || update_var flow f t1 t2 || update map flow t1 in
        List.fold_left aux false bindings
      in
      b || update map flow t2 || add_flow flow t2 t
  | If(t1, t2, t3) -> update map flow t1 || update map flow t2 || update map flow t3 || add_flow flow t2 t || add_flow flow t3 t
  | BinOp(_, t1, t2) -> update map flow t1 || update map flow t2
  | Tuple _ -> assert false
  | Proj _ -> assert false
  | _ ->
      Debug.printf "CFA: %a@." Print.term t;
      unsupported "CFA"

let cfa t =
  let t' = normalize t in
  Debug.printf "NORMALIZE: %a@." Print.term t';
  let n,t'' = Trans.add_id t' in
  Debug.printf "ADD_ID: %a@." Print.term t'';
  let map = get_id_map t'' in
  let flow = Hashtbl.create (n+1) in
  Debug.printf "n: %d@." n;
  ignore @@ List.init (n+1) (fun i -> Hashtbl.add flow i @@ IntSet.singleton i);
  if false then Hashtbl.iter (fun n m -> Debug.printf "MAP: %d ===> %a@." n Print.term m) map;
  let rec loop () = if update map flow t'' then loop () in
  loop ();
  Hashtbl.iter (fun n m -> if n<>0
                           then
                             let t = Hashtbl.find map n in
                             match t.desc with
                             | Var _ ->
                                 Debug.printf "%d:%a ===> %a@.@."
                                               n
                                               Print.term t
                                               (List.print Print.term) (List.map (Trans.remove_id -| Hashtbl.find map) @@ IntSet.elements m)
                             | _ -> ()) flow;
  (flow, map), t''


let replace_const =
  let tr = Tr2.make () in
  let replace_const_term (flow,map) t =
    match t.desc with
    | Var (LId x) ->
        let ts = get_flow map flow t in
        let check t =
          match t.desc with
          | Const _ -> true
          | Var (LId y) -> Id.(x = y)
          | Var _ -> unsupported "CFA"
          | _ -> false
        in
        if List.for_all check ts then
          let cs = List.filter_map (fun t -> match t.desc with Const c -> Some c | _ -> None) ts in
          match cs with
          | c::cs' when List.for_all ((=) c) cs' -> make (Const c) t.typ
          | _ -> t
        else
          t
    | Var _ -> unsupported "CFA"
    | _ -> tr.term_rec (flow,map) t
  in
  tr.term <- replace_const_term;
  Problem.map (cfa
               |- Fun.uncurry tr.term
               |- Trans.remove_id
               |- Trans.reconstruct)
