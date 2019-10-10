open Util
open Type
open Syntax
open Term_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let trans = make_trans2 ()

let rec root x bb path_rev =
  let aux (y,t) =
    match t with
    | {desc=Proj(i,{desc=Var z})} when Id.(x = y) -> Some (z,i)
    | _ -> None
  in
  try
    let y,dir = Option.get @@ List.find ((<>) None) @@ List.map aux bb in
    begin
      match elim_tattr @@ fst_typ @@ Id.typ y with
      | TFun _ -> root y bb (dir::path_rev)
      | _ -> raise Not_found
    end
  with Not_found -> x, List.rev path_rev
let root x bb = root x bb []

let rec find_proj i x bb =
  match bb with
  | [] -> None
  | (y,{desc=Proj(j,{desc=Var z})})::bb' when i = j && Id.(x = z) -> Some y
  | _::bb' -> find_proj i x bb'

let rec find_app x bb =
  match bb with
  | [] -> []
  | (_,{desc=App({desc=Var y},[t])})::bb' when Id.(x = y) ->
      let args = find_app x bb' in
      if List.exists (same_term t) args then
        args
      else
        t::args
  | _::bb' -> find_app x bb'

let decomp_tfun_ttuple typ =
  try
    let typs =
      try
        decomp_ttuple typ
      with Invalid_argument "decomp_ttuple" -> [typ]
    in
    let decomp typ =
      match typ with
      | TFun(x,typ') -> x, typ'
      | _ -> raise Option.No_value
    in
    Some (List.map decomp typs)
  with Option.No_value -> None

let rec make_tree x bb =
  if Debug.check() then Color.printf Color.Red "make_tree: %a@." Print.id_typ x;
  let children = List.mapi (fun i _ -> find_proj i x bb) @@ Option.get @@ decomp_tfun_ttuple @@ Id.typ x in
  if List.for_all Option.is_some children
  then
    Rose_tree.Node ((None, []), List.map (make_tree -$- bb) @@ List.map Option.get children)
  else
    if List.for_all Option.is_none children
    then
      let typ =
        try
          Some (Id.typ @@ arg_var @@ Id.typ x)
        with Invalid_argument _ -> None
      in
      let args = find_app x bb in
      Rose_tree.leaf (typ, args)
    else
      unsupported "not implemented: make_tree"

let rec make_trees tree =
  match tree with
  | Rose_tree.Node((None, []), []) -> assert false
  | Rose_tree.Node((None, _), []) -> assert false
  | Rose_tree.Node((Some typ, []), []) -> [Rose_tree.leaf (make_none typ)]
  | Rose_tree.Node((Some _, args), []) -> List.map (fun t -> Rose_tree.leaf (make_some t)) args
  | Rose_tree.Node (_, ts) ->
      let rec pick xss =
        match xss with
        | [] -> []
        | [xs] -> List.map List.singleton xs
        | xs::xss' ->
            let yss = pick xss' in
            List.rev_map_flatten (fun x -> List.map (List.cons x) yss) xs
      in
      List.map (fun ts -> Rose_tree.Node (unit_term, ts)) @@ pick @@ List.map make_trees ts

let rec term_of_tree tree =
  match tree with
  | Rose_tree.Node(t, [])  -> t
  | Rose_tree.Node(_, ts) -> make_tuple @@ List.map term_of_tree ts


let rec proj_of_path top path t =
  match path with
    [] when top -> t
  | [] -> make_get_val t
  | i::path' -> proj_of_path false path' @@ make_proj i t
let proj_of_path path t = proj_of_path true path t

let make_some' t =
  if is_none t
  then t
  else make_some t

let rec same_arg path_rev t1 t2 =
  match t1,t2 with
  | Rose_tree.Node(t1', []), Rose_tree.Node(t2', []) when t1' = t2' -> List.rev path_rev
  | Rose_tree.Node(t1', []), Rose_tree.Node(t2', []) -> []
  | Rose_tree.Node(_, ts1), Rose_tree.Node(_, ts2) ->
     List.rev_flatten @@ List.mapi2 (fun i -> same_arg @@ i::path_rev) ts1 ts2

let same_arg t1 t2 = same_arg [] t1 t2

let inst_var_fun x tt bb t =
  match Id.typ x with
  | TFun(y,_) ->
      let y' = Id.new_var_id y in
      Debug.printf "x: %a, y': %a@." Id.print x Id.print y';
      let r,path = root x bb in
      if Id.(x = r)
      then
        let () = Debug.printf "THIS IS ROOT@." in
        make_app (make_var x) [t]
      else
        let () = Debug.printf "THIS IS NOT ROOT@." in
        let tree = make_tree r bb in
        let tree' = Rose_tree.update path (Rose_tree.leaf(Some (Id.typ y'), [make_var y'])) tree in
        let r' = trans.tr2_var (tt,bb) r in
        let pr fm (_,ts) =
          Format.fprintf fm "[%a]" (print_list Print.term' "; ") ts
        in
        Debug.printf "y': %a@." Id.print y';
        Debug.printf "path: [%a]@." (print_list Format.pp_print_int ";") path;
        Debug.printf "TREE: %a@." (Rose_tree.print pr) tree;
        Debug.printf "TREE': %a@." (Rose_tree.print pr) tree';
        Debug.printf "r': %a:%a@." Id.print r' Print.typ (Id.typ r');
        let trees = make_trees tree' in
        Debug.printf "|trees|': %d@." (List.length trees);
        List.iter (Debug.printf "  tree: %a@." (Rose_tree.print Print.term)) trees;
        let argss = List.map Rose_tree.flatten trees in
        let args = List.map (List.singleton -| make_tuple) argss in
        let apps = List.map (make_app @@ make_var r') args in
        let same_arg_apps = (* negligence *)
          let rec aux i ts acc =
            match ts with
              [] -> assert false
            | [t] -> acc
            | t1::t2::ts ->
                let paths = same_arg t1 t2 in
                let paths' = List.map (fun path -> i,i+1,path) paths in
                aux (i+1) (t2::ts) (paths' @ acc)
          in
          aux 0 trees []
        in
        let xs = List.map new_var_of_term apps in
        let t' =
          let t1 = proj_of_path path @@ make_var @@ List.hd xs in
          let t2 =
            let aux t (i,j,path) =
              let t1 = make_var (List.nth xs i) in
              let t2 = make_var (List.nth xs j) in
              make_assume (make_eq t1 t2) t
            in
            List.fold_left aux t1 same_arg_apps
          in
          List.fold_left2 (fun t x app -> make_let [x,app] t) t2 xs apps
        in
        subst y' t t'
  | _ -> make_app (make_var x) [t] (* negligence *)

let rec tree_of_typ typ =
  match typ with
  | TTuple xs -> Rose_tree.Node (Ty.unit, List.map (tree_of_typ -| Id.typ) xs)
  | _ -> Rose_tree.leaf typ

let trans_typ ttbb typ =
  match typ with
  | TTuple _ ->
      begin
        match decomp_tfun_ttuple typ with
        | None -> trans.tr2_typ_rec ttbb typ
        | Some xtyps ->
            let xtyps' = List.map (fun (x,typ) -> trans.tr2_var ttbb x, trans.tr2_typ ttbb typ) xtyps in
            let arg_typs = List.map (fun (x,_) -> opt_typ @@ Id.typ x) xtyps' in
            let ret_typs = List.map (fun (_,typ) -> opt_typ typ) xtyps' in
            let name = String.join "" @@ List.map (fun (x,_) -> Id.name x) xtyps' in
            TFun(Id.new_var ~name @@ make_ttuple arg_typs, make_ttuple ret_typs)
      end
  | _ -> trans.tr2_typ_rec ttbb typ

(*
let trans_typ ttbb typ =
  trans_typ ttbb typ
  |@debug()&> Color.printf Color.Yellow "%a@ ===>@ @[%a@]@.@." print_typ typ print_typ
*)

let trans_term (tt,bb) t =
  match t.desc with
  | Local(Decl_let [x,({desc=App({desc=Var x1},[t11])} as t1)], t) when is_non_rec [x,t1] ->
      let x' = trans.tr2_var (tt,bb) x in
      let x1' = trans.tr2_var (tt,bb) x1 in
      let t11' = trans.tr2_term (tt,bb) t11 in
      let bb' = (x,t1)::bb in
      let t' = trans.tr2_term (tt,bb') t in
      let tx = inst_var_fun x1' tt bb' t11' in
      make_let [x',tx] t'
  | Local(Decl_let [x,({desc=Tuple[{desc=Var x1};{desc=Var x2}]} as t1)], t) when Id.(x1 = x2) && is_non_rec [x,t1] ->
      let x' =  trans.tr2_var (tt,bb) x in
      let x1' = trans.tr2_var (tt,bb) x1 in
      let bb' = (x,t1)::bb in
      let t' = trans.tr2_term (tt,bb') t in
      let t1' =
        match trans_typ (tt,bb) @@ Id.typ x with
        | TFun(y, _) ->
            let y' = Id.new_var_id y in
            let ty1 = make_fst (make_var y') in
            let ty2 = make_snd (make_var y') in
            let y1 = Id.new_var ~name:(Id.name y ^ "1") ty1.typ in
            let y2 = Id.new_var ~name:(Id.name y ^ "2") ty2.typ in
            let t1 = make_some @@ make_app (make_var x1') [make_get_val @@ make_var y1] in
            let t1' = make_if (make_is_none @@ make_var y1) (make_none @@ get_opt_typ t1.typ) t1 in
            let t2 = make_some @@ make_app (make_var x1') [make_get_val @@ make_var y2] in
            let t2' = make_if (make_is_none @@ make_var y2) (make_none @@ get_opt_typ t2.typ) t2 in
            let t_neq = make_pair t1' t2' in
            let z = Id.new_var ~name:"r" t1.typ in
            let t_eq = make_let [z,t1] @@ make_pair (make_var z) (make_var z) in
            let cond1 = make_and (make_is_some @@ make_var y1) (make_is_some @@ make_var y2) in
            let cond2 = make_eq (make_get_val @@ make_var y1) (make_get_val @@ make_var y2) in
            make_fun y' @@ make_lets [y1,ty1; y2,ty2] @@ make_if (make_and cond1 cond2) t_eq t_neq
        | _ -> make_pair (make_var x1') (make_var x1')
      in
      make_let [x',t1'] t'
  | Local(Decl_let [x,({desc=Tuple[{desc=Var x1};{desc=Var x2}]} as t1)], t) when is_non_rec [x,t1] ->
      let x' =  trans.tr2_var (tt,bb) x in
      let x1' = trans.tr2_var (tt,bb) x1 in
      let x2' = trans.tr2_var (tt,bb) x2 in
      let bb' = (x,t1)::bb in
      let t' = trans.tr2_term (tt,bb') t in
      let t1' =
        match trans_typ (tt,bb) @@ Id.typ x with
        | TFun(y, _) ->
            let y' = Id.new_var_id y in
            let ty1 = make_fst (make_var y') in
            let ty2 = make_snd (make_var y') in
            let y1 = Id.new_var ~name:(Id.name y ^ "1") ty1.typ in
            let y2 = Id.new_var ~name:(Id.name y ^ "2") ty2.typ in
            let t1 = make_some @@ make_app (make_var x1') [make_get_val @@ make_var y1] in
            let t1' = make_if (make_is_none @@ make_var y1) (make_none @@ get_opt_typ t1.typ) t1 in
            let t2 = make_some @@ make_app (make_var x2') [make_get_val @@ make_var y2] in
            let t2' = make_if (make_is_none @@ make_var y2) (make_none @@ get_opt_typ t2.typ) t2 in
            make_fun y' @@ make_lets [y1,ty1; y2,ty2] @@ make_pair t1' t2'
        | _ -> make_pair (make_var x1') (make_var x2')
      in
      make_let [x',t1'] t'
  | Local(Decl_let [x,({desc=Tuple ts} as t1)], t) when List.for_all (Option.is_some -| decomp_var) ts && is_non_rec [x,t1] ->
      let xs = List.map (function {desc=Var x} -> x | t -> Format.eprintf "%a@." Print.term t; assert false) ts in
      let x' =  trans.tr2_var (tt,bb) x in
      let xs' = List.map (trans.tr2_var (tt,bb)) xs in
      let bb' = (x,t1)::bb in
      let t' = trans.tr2_term (tt,bb') t in
      let t1' =
        match trans_typ (tt,bb) @@ Id.typ x with
        | TFun(y, _) ->
            let y' = Id.new_var_id y in
            let tys = List.map (fun i -> make_proj i @@ make_var y') @@ List.fromto 0 @@ List.length ts in
            let ys = List.mapi (fun i t -> Id.new_var ~name:(Id.name y ^ string_of_int (i+1)) t.typ) tys in
            let aux xi' yi =
              let ti = make_some @@ make_app (make_var xi') [make_get_val @@ make_var yi] in
              let ti' = make_if (make_is_none @@ make_var yi) (make_none @@ get_opt_typ ti.typ) ti in
              ti'
            in
            let ts' = List.map2 aux xs' ys in
            let bindings = List.combine ys tys in
            make_fun y' @@ make_lets bindings @@ make_tuple ts'
        | _ -> make_tuple @@ List.map make_var xs
      in
      make_let [x',t1'] t'
  | Local(Decl_let [x,({desc=Proj(i,{desc=Var x1})} as t1)], t) when is_non_rec [x,t1] ->
      let x' = trans.tr2_var (tt,bb) x in
      let x1' = trans.tr2_var (tt,bb) x1 in
      let bb' = (x,t1)::bb in
      let t' = trans.tr2_term (tt,bb') t in
      let t1' =
        match Id.typ x1' with
        | TTuple _ -> make_proj i @@ make_var x1'
        | TFun(y,typ) ->
            begin match decomp_tfun_ttuple @@ Id.typ x1 with
            | None -> assert false
            | Some xtyps ->
                let z = Id.new_var_id @@ fst @@ List.nth xtyps i in
                let arg = make_tuple @@ List.mapi (fun j (z',_) -> if j = i then make_some @@ make_var z else make_none @@ Id.typ z') xtyps in
                make_fun z @@ make_get_val @@ make_proj i @@ make_app (make_var x1') [arg]
            end
        | _ -> assert false
      in
      make_let [x',t1'] t'
  | _ -> trans.tr2_term_rec (tt,bb) t

let () = trans.tr2_term <- trans_term
let () = trans.tr2_typ <- trans_typ



let rec decomp_simple_let t =
  match t.desc with
  | Local(Decl_let [x,t1],t2) when is_non_rec [x,t1] ->
      let bindings,t2' = decomp_simple_let t2 in
      (x,t1)::bindings, t2'
  | _ -> [], t

let sort_let_pair = make_trans ()

let sort_let_pair_aux x t =
  let bindings,t' = decomp_simple_let t in
  let bindings' = List.map (Pair.map_snd sort_let_pair.tr_term) bindings in
  let is_proj (_,t) =
    match t.desc with
    | Proj(_, {desc=Var y}) -> Id.(x = y)
    | _ -> false
  in
  let bindings1,bindings2 = List.partition is_proj bindings' in
  let t'' = sort_let_pair.tr_term t' in
  make_lets bindings1 @@ make_lets bindings2 t''

let sort_let_pair_term t =
  match t.desc with
  | Local(Decl_let [x,({desc=Tuple _} as t1)],t2) when is_non_rec [x,t1] ->
      let t2' = sort_let_pair_aux x t2 in
      make_let [x,t1] t2'
  | Local(Decl_let [f,t1],t2) ->
      let xs,t1 = decomp_funs t1 in
      let t1' = sort_let_pair.tr_term t1 in
      let t2' = sort_let_pair.tr_term t2 in
      let t1'' = List.fold_right sort_let_pair_aux xs t1' in
      make_let [f, make_funs xs t1''] t2'
  | _ -> sort_let_pair.tr_term_rec t

let () = sort_let_pair.tr_term <- sort_let_pair_term



let move_proj = make_trans ()

let rec move_proj_aux x t =
  match Id.typ x with
  | TTuple xs ->
      let ts = List.mapi (fun i _ -> make_proj i @@ make_var x) xs in
      let xs' = List.mapi (fun i x -> Id.new_var ~name:(Id.name x ^ string_of_int (i+1)) @@ Id.typ x) xs in
      let subst_rev' t x t_acc =
        let ts = col_same_term t t_acc in
        List.fold_right (fun t1 t2 -> subst_rev t1 x t2) ts t_acc
      in
      t
      |> Trans.inline_var_const
      |> List.fold_right2 subst_rev' ts xs'
      |> List.fold_right move_proj_aux xs'
      |> make_lets @@ List.combine xs' ts
  | _ -> t

let move_proj_term t =
  match t.desc with
  | Local(Decl_let bindings,t2) ->
      let bindings' = List.map (fun (f,t) -> f, move_proj.tr_term t) bindings in
      let t2' = move_proj.tr_term t2 in
      let t2'' = List.fold_right (move_proj_aux -| fst) bindings t2' in
      make_let bindings' t2''
  | Fun(x,t1) -> make_fun x @@ move_proj_aux x t1
  | _ -> move_proj.tr_term_rec t

let () = move_proj.tr_term <- move_proj_term




let col_assert = make_col [] (@@@)

let col_assert_desc desc =
  match desc with
  | If(t1, t2, t3) when same_term t2 unit_term && same_term t3 (make_app fail_term [unit_term]) ->
      [t1]
  | Local(Decl_let [x,t1], t2) when is_non_rec [x,t1] ->
      let ts1 = col_assert.col_term t1 in
      let ts2 = col_assert.col_term t2 in
      let ts2' = List.map (subst x t1) ts2 in
      ts1 @ ts2'
  | _ -> col_assert.col_desc_rec desc

let () = col_assert.col_desc <- col_assert_desc
let col_assert = col_assert.col_term


let has_rand = make_col false (||)

let has_rand_const c =
  match c with
  | Rand _ -> true
  | _ -> false

let () = has_rand.col_const <- has_rand_const
let has_rand = has_rand.col_term


let col_rand_funs = make_col [] (@@@)

let col_rand_funs_desc desc =
  match desc with
  | Local(Decl_let bindings, t2) ->
      let aux (f,t) = if has_rand t then [f] else [] in
      let funs1 = List.flatten_map aux bindings in
      let funs2 = col_rand_funs.col_term_rec t2 in
      funs1 @ funs2
  | _ -> col_rand_funs.col_desc_rec desc

let () = col_rand_funs.col_desc <- col_rand_funs_desc
let col_rand_funs = col_rand_funs.col_term


let col_app_head = make_col [] (@@@)

let col_app_head_desc desc =
  match desc with
  | App({desc=Var f}, _) -> [f]
  | _ -> col_app_head.col_desc_rec desc

let () = col_app_head.col_desc <- col_app_head_desc

let col_app_head = col_app_head.col_term


let compare_pair (x1,x2) (y1,y2) =
  if Id.(x1 = y2 && x2 = y1) then
    0
  else
    let r1 = compare x1 y1 in
    if r1 <> 0 then
      r1
    else
      compare x2 y2

let eq_pair x y = 0 = compare_pair x y

let col_fun_arg = make_col [] (List.Set.union ~eq:eq_pair)

let col_fun_arg_desc desc =
  match desc with
  | App({desc=Var f}, ts) ->
      let funs = List.flatten_map col_app_head ts in
      List.map (fun g -> f, g) funs
  | _ -> col_fun_arg.col_desc_rec desc

let () = col_fun_arg.col_desc <- col_fun_arg_desc
let col_fun_arg = col_fun_arg.col_term



let col_app_terms = make_col2 [] (@@@)

let col_app_terms_term fs t =
  match t.desc with
  | App({desc=Var f}, ts) when Id.mem f fs ->
      t :: List.flatten_map (col_app_terms.col2_term fs) ts
  | _ -> col_app_terms.col2_term_rec fs t

let () = col_app_terms.col2_term <- col_app_terms_term
let col_app_terms = col_app_terms.col2_term



let replace_head fs fs' t =
  let ts = col_app_terms fs t in
  let rec aux fs ts =
    match fs,ts with
    | [], [] -> []
    | [], _ -> unsupported "replace_head"
    | f::fs', _ ->
        let ts1,ts2 = List.partition (Id.mem f -| get_fv) ts in
        List.hd ts1 :: aux fs' (List.tl ts1 @ ts2)
  in
  let ts' = aux fs ts in
  let xs = List.map (fun t -> Id.new_var t.typ) ts' in
  let t' = List.fold_right2 subst_rev ts' xs t in
  Debug.printf "t':@.%a@.@." Print.term t';
  let ts'' = List.map3 subst_var fs fs' ts' in
  let t'' = List.fold_right2 subst xs ts'' t' in
  Debug.printf "t'':@.%a@.@." Print.term t'';
  t''


let add_fun_tuple = make_trans2 ()

let defined fs env = List.for_all (Id.mem -$- env) fs

let add_fun_tuple_term (funs,env) t =
  match t.desc with
  | Local(Decl_let [f,t1],t2) ->
      let env' = f::env in
      let funs1,funs2 = List.partition (fun fs -> defined fs env') funs in
      let t1' = add_fun_tuple.tr2_term (funs2,env') t1 in
      let t2' = add_fun_tuple.tr2_term (funs2,env') t2 in
      let aux t fs =
        let name = String.join "__" @@ List.rev_map Id.name fs in
        let fg = Id.new_var ~name @@ make_ttuple @@ List.map Id.typ fs in
        let projs = List.mapi (fun i g -> Id.new_var_id g, make_proj i (make_var fg)) fs in
        let t' = replace_head fs (List.map fst projs) t in
        let defs = (fg, make_label ~label:"add_fun_tuple" (InfoString "") @@ make_tuple @@ List.map make_var fs)::projs in
        make_lets defs t'
      in
      make_let [f,t1'] @@ List.fold_left aux t2' funs1
  | Local(Decl_let _,_) -> unsupported "add_fun_tuple (let (rec) ... and ...)"
  | _ -> add_fun_tuple.tr2_term_rec (funs,env) t

let () = add_fun_tuple.tr2_term <- add_fun_tuple_term
let add_fun_tuple rel_funs t = add_fun_tuple.tr2_term (rel_funs,[]) t


let make_fun_tuple t =
  let asserts = col_assert t in
  List.iter (Debug.printf "ASSERT: %a@." Print.term) asserts;
  let rand_funs = col_rand_funs t in
  List.iter (Debug.printf "RAND: %a@." Id.print) rand_funs;
  let aux assrt =
    let funs = col_app_head assrt in
    List.iter (Debug.printf "FUN: %a@." Id.print) funs;
    let funs' = List.Set.diff ~eq:Id.eq funs rand_funs in
    List.iter (Debug.printf "FUN': %a@." Id.print) funs';
    let rec get_pairs acc fs =
      match fs with
      | [] -> acc
      | f::fs' -> get_pairs (List.map (fun g -> (f,g)) fs' @ acc) fs'
    in
    let all_fun_pairs = get_pairs [] funs' in
    List.iter (fun (f,g) -> Debug.printf "ALL_FUN_ARG: %a, %a@." Id.print f Id.print g) all_fun_pairs;
    let fun_args = col_fun_arg assrt in
    List.iter (fun (f,g) -> Debug.printf "FUN_ARG: %a, %a@." Id.print f Id.print g) fun_args;
    let rel_funs = List.Set.diff ~eq:eq_pair all_fun_pairs fun_args in
    List.iter (fun (f,g) -> Debug.printf "FUN_ARG': %a, %a@." Id.print f Id.print g) rel_funs;
    List.map (fun (f,g) -> [f;g]) rel_funs
  in
  let rel_funs = List.flatten_map aux asserts in
  let t' = add_fun_tuple rel_funs t in
  Debug.printf "@.@.%a@." Print.term t';
  t'



let trans t = t
  |@> Debug.printf "INPUT: %a@." Print.term
  |> Trans.remove_label ~label:"add_fun_tuple"
  |@> Debug.printf "remove_label: %a@." Print.term_typ
  |> move_proj.tr_term
  |@> Debug.printf "move_proj: %a@." Print.term_typ
  |@> Trans.inline_no_effect
  |@> Debug.printf "inline_no_effect: %a@." Print.term_typ
  |> Trans.normalize_let
  |> Trans.inline_simple_exp
  |@> Debug.printf "normalize_let: %a@." Print.term_typ
  |> Trans.flatten_let
  |> Trans.inline_var_const
  |@> Debug.printf "flatten_let: %a@." Print.term_typ
  |> sort_let_pair.tr_term
  |@> Debug.printf "sort_let_pair: %a@." Print.term_typ
  |@> Type_check.check
  |> trans.tr2_term (assert_false,[])
  |> Trans.inline_no_effect
  |@> Debug.printf "ref_trans: %a@." Print.term
  |@> Type_check.check

let trans t =
 trans t, fun _ _ -> raise Not_found
