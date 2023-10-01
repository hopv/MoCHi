open Type
open Type_util
open Syntax
open Term_util
open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

(*
let remove_unrelated =
  let tr = Tr2.make () in
  let tr_term (dist,longest) t =
    let d = dist t in
    let effects = effect_of_typ t.typ in
    if d < 0 && is_base_typ t.typ && List.Set.(effects <= [ENonDet;EDiv]) then
      let () = Debug.printf "REMOVE CONTEXT %d@." (get_id t.typ) in
      make_default_term t.typ
    else if d > longest && is_base_typ t.typ && List.Set.(effects <= [ENonDet;EDiv]) then
      let () = Debug.printf "REMOVE FAR %d@." (get_id t.typ) in
      let () = Debug.printf "%a@.@." Print.term' t in
      make_rand_unit @@ elim_tid label t.typ
    else
      tr.term_rec (dist,longest) t
      |> remove_attr_if (function AId _ -> true | _ -> false)
  in
  tr.term <- tr_term;
  tr.typ <- Fun.snd;
  Fun.curry tr.term


let make_slice_sub respect_div t =
  let env,t' = gen_constr_init respect_div @@ Effect.infer t in
  let graph = Graph.from_directed_edges env.constr in
  if !!Debug.check then Graph.save_as_dot "test.dot" graph;
  let hops = Graph.hops_to graph [0] in
  Array.iteri (fun i x -> Debug.printf "hops(%d) = %d@." i x) hops;
  let dist t = hops.(get_id t.typ) in
  let longest = Graph.fold_node (fun i l -> max l hops.(i)) graph (-1) in
  fun p ->
    let far = int_of_float (p *. float_of_int longest) in
    Debug.printf "longest: %d@." longest;
    Debug.printf "far: %d@." far;
    Debug.printf "INFER_ORIG: @[%a@." Print.term' t';
    let t'' = Trans.remove_effect_attribute @@ remove_unrelated dist far t' in
    Debug.printf "ORIG: @[%a@." Print.term t;
    Debug.printf "INFER: @[%a@." Print.term' t';
    Debug.printf "REMOVE_UNRELATED: @[%a@." Print.term t'';
    let t'' =
      t''
      |> Trans.remove_tid label
      |> Trans.reconstruct
      |@> Type_check.check
      |> Trans.reduce_rand
    in
    Debug.printf "SIMPLIFIED: @[%a@." Print.term t'';
    t''

let slice_sub respect_div t p =
  make_slice_sub respect_div t p

let slice_subs respect_div t p =
  let make = make_slice_sub respect_div t in
  let n = int_of_float (ceil (1. /. p)) in
  let p_of i =
    let p' = min 1. (float_of_int i *. p) in
    make p'
    |&!!Debug.check&> add_comment (Format.sprintf "SLICE_SUB %.3f" p')
  in
  List.init n p_of
 *)

let normalize =
  let aux t =
    match decomp_assert t with
    | None -> t
    | Some(t', _) ->
        let u = Id.new_var Ty.unit in
        Term.(let_ [u, assert_ t'] unit)
  in
  Trans.map_main aux
  |- Trans.elim_unused_let
  |- Trans.top_def_to_funs

let get_top_fun_dependencies unsafe_ext_funs t =
  let decls,_ = decomp_decls t in
  let defs = List.flatten_map (function Decl_let defs -> defs | _ -> []) decls in
  let id_of,fun_of =
    let module IDMap = Map.Make(ID) in
    let module IDRevMap = Map.Make(struct type t = int let compare = compare end) in
    let fs = get_fv_unique t @ List.map fst defs in
    let map = List.fold_lefti (fun acc cnt f -> IDMap.add f cnt acc) IDMap.empty fs in
    let rev_map = List.fold_lefti (fun acc cnt f -> IDRevMap.add cnt f acc) IDRevMap.empty fs in
    IDMap.find -$- map,
    IDRevMap.find -$- rev_map
  in
  let check t =
    let has_target_exn t =
      if !Flag.Method.target_exn = [] then
        false
      else
        let aux = function
          | None -> true
          | Some s -> List.mem (Path.to_string s) !Flag.Method.target_exn
        in
        List.exists aux (col_raise t)
    in
    has_event t || has_target_exn t
  in
  let goals = (* "goals" are functions that have fail or raise syntactically *)
    let unsafe_ext_funs' = List.filter (Exception.not_raise id_of) unsafe_ext_funs in
    defs
    |> List.filter_map (fun (f,t) -> if check t then Some f else None)
    |@> Debug.printf "GOALS: %a@." Print.(list id)
    |> (@) unsafe_ext_funs'
    |> List.map id_of
  in
  let deps =
    defs
    |> List.flatten_map (fun (f,t) -> List.map (Pair.pair -$- f) @@ get_fv_unique t)
    |> List.map (Pair.map_same id_of)
  in
  id_of, fun_of, goals, deps

(** remove function `f` in `t` if `dist f < 0 || far < dist f` *)
let rec remove_unrelated_funs dist far may_call_goal t =
  let ruf = remove_unrelated_funs dist far in
  let removed,target,desc =
    match t.desc with
    | Local(Decl_type decl, t') ->
        let removed,target,t'' = ruf may_call_goal t' in
        removed, target, Local(Decl_type decl, t'')
    | Local(Decl_let defs, t1) ->
        let defs_unrelated,defs' =
          let check (f,_) =
            let d = dist f in
            d < 0 || far < d
          in
          List.partition check defs
        in
        let removed1 = List.map fst defs_unrelated in
        if defs' <> [] then Debug.printf "Dom(defs'): @[%a@." Print.(list id) (List.map fst defs');
        let may_call_goal1 =
          let check (_,t) = List.exists (Id.List.mem -$- may_call_goal) (get_fv t) in
          if List.exists check defs then
            List.map fst defs
          else
            []
        in
        if may_call_goal1 <> [] then Debug.printf "may_call_goal1: %a@." Print.(list id) may_call_goal1;
        let removed2,target2,t1' = ruf (may_call_goal1@may_call_goal) t1 in
        let desc =
          if defs' = [] then
            t1'.desc
          else
            Local(Decl_let defs', t1')
        in
        let target1 =
          let fv = List.rev_flatten_map get_fv (t1 :: List.map snd defs_unrelated) in
          let fv' = get_fv t1' in
          Id.List.Set.(List.map fst defs' && may_call_goal1)
          |> List.L.filter_out ~f:(fun f -> Compare.eq_on (List.count (Id.(=) f)) fv fv')
        in
        if target1 <> [] then
          (Debug.printf "Dom(defs): @[%a@." Print.(list id) (List.map fst defs);
           Debug.printf "target1: @[%a@." Print.(list id) target1);
        removed1@removed2, target1@target2, desc
    | _ -> [], [], t.desc
  in
  removed, target, make desc t.typ

let add_raise_attr =
  let tr = Tr2.make () in
  let tr_typ exn ty =
    match tr.typ_rec exn ty with
    | TFun(x, ty2) -> TAttr([TARaise exn], TFun(x, ty2))
    | ty -> ty
  in
  tr.typ <- tr_typ;
  tr.typ


let rec may_raise_funs acc t =
  match t.desc with
  | Local(decl, t') ->
      let acc' =
        let check (_,t) =
          has_raise ~target:!Flag.Method.target_exn t || List.exists (Id.List.mem -$- get_fv t) acc
        in
        match decl with
        | Decl_let defs when List.exists check defs -> List.map fst defs @ acc
        | _ -> acc
      in
      may_raise_funs acc' t'
  | _ -> acc
let may_raise_funs t = may_raise_funs [] t

let output_dep_graph ?(filename="slice_deps.dot") _id_of fun_of goals deps =
  let is_in_stdlib x = String.starts_with (Id.name (fun_of x)) "Stdlib" in
  let deps = List.filter_out (fun (x,y) -> is_in_stdlib x || is_in_stdlib y) deps in
  let attribute_of_node x =
    if List.mem x goals then
      "[style = filled, fillcolor = red, fontcolor = white];"
    else
      ""
  in
  let name_of n = fun_of n |> Id.name in
  deps
  |> List.map Pair.swap (* To match the notations to ones in the paper *)
  |> Graph_wrapper.from_directed_edges
  |> Graph_wrapper.save_as_dot filename ~name_of ~attribute_of_node ~layout:"fdp";
  ignore @@ Sys.command @@ Format.sprintf "dot %s -Tpng > %s" filename (Filename.change_extension filename "png")

let calc_dist unsafe_ext_funs t =
  let id_of,fun_of,goals,deps = get_top_fun_dependencies unsafe_ext_funs t in
  let graph = Graph_wrapper.from_edges deps in
  if !!Debug.check then output_dep_graph id_of fun_of goals deps;
  let hops = Graph_wrapper.hops_to graph goals in
  Array.iteri (fun i x -> Debug.printf "hops(%d) = %d@." i x) hops;
  let dist f =
    let x = id_of f in
    let n = hops.(x) in
    if true then Debug.printf "hops(%a : #%d) = %d@." Print.id f x n;
    n
  in
  let longest = Graph_wrapper.fold_node (fun i l -> max l hops.(i)) graph (-1) in
  List.map fun_of goals, dist, longest

let slice_top_fun unsafe_ext_funs t =
  let t = normalize t in
  Debug.printf "normalized: %a@." Print.term t;
  let goals,dist,longest = calc_dist unsafe_ext_funs t in
  Flag.Experiment.Slice.max_hop := longest;
  let typ_exn = find_exn_typ t in
  let may_raise = may_raise_funs t in (* What the difference with [goals]? *)
  Debug.printf "MAY_RAISE: %a@." Print.(list id) may_raise;
  fun p ->
    Debug.printf "p: %f@." p;
    let far = int_of_float (ceil (p *. float_of_int longest)) in
    Debug.printf "longest: %d@." longest;
    Debug.printf "far: %d@." far;
    let removed,target,t = remove_unrelated_funs dist far goals t in
    Debug.printf "TARGET: %a@." Print.(list id) target;
    let t =
      t
      |> Trans.remove_effect_attribute
      |> Trans.replace_main ~main:Term.(tuple (vars target))
      |&!!Debug.check&> add_comment (Format.sprintf "SLICE_TOP_FUN %.3f" p)
    in
    Debug.printf "REMOVE_UNRELATED: @[%a@." Print.term t;
    Debug.printf "REMOVED[%.3f]: %a@." p Print.(list id) removed;
    let decls,body = split_type_decl_and_body t in
    let body' =
      let used_but_removed = Id.List.Set.inter removed (get_fv t) in
      let aux t x =
        let ty = Id.typ x in
        let ty =
          match typ_exn with
          | Some typ_exn when Id.List.mem x may_raise -> add_raise_attr typ_exn ty (* Should deal with target_exn *)
          | _ -> ty
        in
        Term.(let_ [x, rand ty] t)
      in
      List.fold_left aux body used_but_removed
    in
    body'
    |> List.fold_right make_let_type decls
