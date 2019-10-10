open Syntax
open Term_util
open Type
open Util

module Tree = Rose_tree
module RT = Ref_type
module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let leaf x = Tree.leaf (Some x)
let node tys = Tree.Node(None, tys)
let root x = Option.get @@ Tree.root x
let flatten x = List.filter_map Fun.id @@ Tree.flatten x
let map f x = Tree.map (fun path label -> Option.map (f path) label) x

let rec element_num typ =
  match elim_tattr typ with
  | TTuple xs -> List.fold_right ((+) -| element_num -| Id.typ) xs 0
  | _ -> 1

let rec get_tuple_name_map rtyp =
  match rtyp with
  | RT.Tuple xrtyps ->
      let ixrtyps = List.mapi Pair.pair xrtyps in
      let ixs = List.filter_map (function (i,(_,RT.Base(_,x,_))) -> Some(i,x) | _ -> None) ixrtyps in
      let map = List.rev_flatten_map (fun (i,(_,typ)) -> List.map (Pair.map_snd (List.cons i)) @@ get_tuple_name_map typ) ixrtyps in
      List.map (fun (i,x) -> x,[i]) ixs @@@ map
  | RT.Inter(_, rtyps)
  | RT.Union(_, rtyps) -> List.rev_flatten_map get_tuple_name_map rtyps
  | _ -> []

let rec correct_arg_refer ?(z=None) sty rtyp =
  match rtyp, sty with
  | RT.Base _, _ -> rtyp
  | RT.Fun(x,rtyp1,rtyp2), TFun(x1,sty2) ->
      let rtyp1' = correct_arg_refer ~z:(Some x) (Id.typ x1) rtyp1 in
      let rtyp2' = correct_arg_refer ~z:(Some x) sty2 rtyp2 in
      let map = get_tuple_name_map rtyp1 in
      let aux (y,path) typ =
        let t = List.fold_left (Fun.flip make_proj) (make_var x) path in
        Ref_type.subst y t typ
      in
      RT.Fun(x, rtyp1', List.fold_right aux map rtyp2')
  | RT.Tuple xrtyps, TTuple xs ->
      let aux (x,rtyp) x2 (first,xrtyps) =
        let x' =
          match first, z with
          | true, Some z -> z
          | _ -> x
        in
        let x'' = Id.set_typ x' (Id.typ x2) in
        let rtyp' = correct_arg_refer ~z (Id.typ x2) rtyp in
        let map = get_tuple_name_map rtyp in
        let aux' (y,path) typ =
          let t = List.fold_left (Fun.flip make_proj) (make_var x'') path in
          Ref_type.subst y t typ
        in
        let xrtyps' = List.map (Pair.map_snd @@ List.fold_right aux' map) xrtyps in
        false, (x, rtyp') :: xrtyps'
      in
      RT.Tuple (snd @@ List.fold_right2 aux xrtyps xs (true,[]))
  | RT.Inter(typ, rtyps), _ -> RT.Inter(typ, List.map (correct_arg_refer ~z sty) rtyps)
  | RT.Union(typ, rtyps), _ -> RT.Union(typ, List.map (correct_arg_refer ~z sty) rtyps)
  | RT.ExtArg(x,rtyp1,rtyp2), _ -> unsupported "correct_arg_refer"
  | RT.List _, _ -> unsupported "correct_arg_refer"
  | RT.Exn _, _ -> unsupported "correct_arg_refer"
  | _ -> assert false
let correct_arg_refer rtyp =
  correct_arg_refer (RT.to_simple rtyp) rtyp

let rec uncurry_typ rtyp typ =
  let r =
  match rtyp,typ with
  | RT.Inter(styp, rtyps), _ ->
      let rtyps' = List.map (uncurry_typ -$- typ) rtyps in
      let typ' =
        match rtyps' with
        | [] -> RT.to_simple @@ uncurry_typ (RT.of_simple styp) typ
        | rtyp'::_ -> RT.to_simple rtyp'
      in
      if rtyps'=[] then Debug.printf "UNCURRY_TYP TOP: %a ===> %a@." Print.typ typ Print.typ typ';
      RT.Inter(typ', rtyps')
  | RT.Union(typ, rtyps), _ ->
      let rtyps' = List.map (uncurry_typ -$- typ) rtyps in
      let typ' =
        match rtyps' with
        | [] -> RT.to_simple @@ uncurry_typ (RT.of_simple typ) typ
        | rtyp'::_ -> RT.to_simple rtyp'
      in
      RT.Union(typ', rtyps')
  | _, TFun(x,typ2) ->
      let typ1 = Id.typ x in
      let n = element_num typ1 in
      let exts,xrtyps,rtyp2 = RT.decomp_funs_n n rtyp in
      let rtyp1' = uncurry_typ_arg (List.map snd xrtyps) typ1 in
      let rtyp2' = uncurry_typ rtyp2 typ2 in
      let y =
          match rtyp with
          | RT.Fun(y, _, _) -> Id.set_typ y (RT.to_simple rtyp1')
          | _ -> assert false
      in
      let rtyp = RT.Fun(y, rtyp1', rtyp2') in
      List.fold_right (Fun.uncurry RT._ExtArg) exts rtyp
  | _ -> rtyp
  in
  Debug.printf "rtyp:%a@.typ:%a@.r:%a@.@." RT.print rtyp Print.typ typ RT.print r;r

and uncurry_typ_arg rtyps typ =
  let r =
  match rtyps, elim_tattr typ with
  | _, TTuple xs ->
      let aux (rtyps,xrtyps) {Id.typ} =
        let rtyps1,rtyps2 = List.split_nth (element_num typ) rtyps in
        let rtyp = uncurry_typ_arg rtyps1 typ in
        let x =
          match rtyp with
          | RT.Base(_,x,_) -> x
          | _ -> Id.new_var typ_unknown
        in
        rtyps2, xrtyps @ [x, rtyp]
      in
      let rtyps',xrtyps = List.fold_left aux (rtyps,[]) xs in
      assert (rtyps' = []);
      RT.Tuple xrtyps
  | [rtyp], _ -> uncurry_typ rtyp typ
  | _ -> assert false
  in
  Debug.printf "rtyps:%a@.typ:%a@.r:%a@.@." Print.(list RT.print) rtyps Print.typ typ RT.print r;
  r

let uncurry_rtyp t get_rtyp f =
  let rtyp =
    f
    |@> Debug.printf "%a:@." Id.print
    |> get_rtyp
    |@> Debug.printf "rty1: %a@." RT.print
    |> RT.copy_fun_arg_to_base
    |@> Debug.printf "rty2: %a@." RT.print
    |> uncurry_typ -$- (Trans.assoc_typ f t)
    |@> Debug.printf "rty3: %a@." RT.print
    |> correct_arg_refer
    |@> Debug.printf "rty4: %a@.@." RT.print
  in
  if !!Flag.Debug.print_ref_typ then
    Format.printf "Curry ref_typ: %a: @[%a@]@]@." Id.print f RT.print rtyp;
  rtyp

let rec remove_pair_typ ty =
  match ty with
  | TBase _ -> leaf ty
  | TVar _ -> assert false
  | TFun _ ->
      (* ty' must be the result type *)
      let xs,ty' = decomp_tfun ty in
      let xs' = List.flatten_map (flatten -| remove_pair_var) xs in
      leaf @@ List.fold_right _TFun xs' ty'
  | TTuple xs ->
      node @@ List.map (remove_pair_typ -| Id.typ) xs
  | TData s -> leaf (TData s)
  | TAttr(_, TTuple[x; {Id.typ}]) when get_tapred ty <> None ->
      let y,ps = Option.get @@ get_tapred ty in
      begin
        match typ with
        | TFun _ -> (* Function types cannot have predicates *)
            let x1 = Id.new_var_id x in
            let x2 = Id.new_var typ in
            let ps' = List.map Term.(y |-> pair (var x1) (var x2)) ps in
            let x' = Id.map_typ (add_tapred x1 ps') x in
            remove_pair_typ @@ TTuple [x'; Id.new_var typ]
        | _ ->
            let y' = Id.set_typ y typ in
            let ps' = List.map Term.(y |-> pair (var x) (var y')) ps in
            let typ' = add_tapred y' ps' typ in
            remove_pair_typ @@ TTuple [x; Id.new_var typ']
      end
  | TAttr(_, typ) when get_tapred ty <> None ->
      let x,ps = Option.get @@ get_tapred ty in
      let ps' = List.map remove_pair ps in
      let typ' =
        match remove_pair_typ (Id.typ x) with
        | Tree.Node(Some typ, []) -> typ
        | Tree.Node _ -> fatal "Not implemented CPS.remove_pair_typ(TPred)"
      in
      leaf (add_tapred x ps' typ')
  | TAttr(attr, typ) ->
      typ
      |> remove_pair_typ
      |> root
      |> _TAttr attr
      |> leaf
  | typ ->
      Format.eprintf "remove_pair_typ: %a@." Print.typ typ;
      assert false

and remove_pair_var x =
  let aux path typ =
    let s = String.join "" @@ List.map string_of_int path in
    Id.set_typ (Id.add_name_after s x) typ
  in
  Id.typ x
  |> remove_pair_typ
  |> map aux

and remove_pair_aux ?typ t =
  let typs =
    typ
    |> Option.default t.typ
    |> remove_pair_typ
  in
  match t.desc with
  | Const _
  | Event _ -> leaf t
  | Bottom -> map (Fun.const make_bottom) typs
  | Var x -> map (Fun.const make_var) (remove_pair_var x)
  | Fun(x, t) ->
      let xs = flatten @@ remove_pair_var x in
      let t' = remove_pair t in
      leaf Term.(funs xs t')
  | App(t1, ts) ->
      let typs = get_argtyps t1.typ in
      assert (List.length typs >= List.length ts);
      let typs' = List.take (List.length ts) typs in
      let t' = remove_pair t1 in
      let ts' = List.flatten (List.map2 (fun t typ -> flatten @@ remove_pair_aux ~typ t) ts typs') in
      leaf Term.(t' @ ts')
  | If(t1, t2, t3) ->
      let t1' = remove_pair t1 in
      let t2' = remove_pair t2 in
      let t3' = remove_pair t3 in
      leaf (add_attrs t.attr @@ make_if t1' t2' t3')
  | Local(Decl_let bindings, t) ->
      let aux (f,t) =
        root @@ remove_pair_var f,
        root @@ remove_pair_aux t
      in
      let bindings' = List.map aux bindings in
      let t' = remove_pair t in
      leaf Term.(let_ bindings' t')
  | BinOp(op, t1, t2) ->
      begin
        match op, elim_tattr t1.typ with
        | (Eq | Lt | Gt | Leq | Geq), (TBase _ | TData _) -> ()
        | (Eq | Lt | Gt | Leq | Geq), _ ->
            Format.eprintf "%a@." Print.typ t1.typ;
            Format.eprintf "%a@." Print.typ t2.typ;
            Format.eprintf "%a@." Print.term' t;
            unsupported "polymorphic comparison"
        | _ -> ()
      end;
      let t1' = remove_pair t1 in
      let t2' = remove_pair t2 in
      leaf Term.(t1' <|op|> t2')
  | Not t1 ->
      let t1' = remove_pair t1 in
      leaf Term.(not t1')
  | Record fields -> assert false
  | Field(s,t1) -> assert false
  | SetField(s,t1,t2) -> assert false
  | Nil -> assert false
  | Cons(t1,t2) -> assert false
  | Constr(s,ts) -> assert false
  | Match(t1,pats) -> assert false
  | TryWith(t1,t2) -> assert false
  | Tuple ts -> node @@ List.map remove_pair_aux ts
  | Proj(i, {desc=Var x}) when x = abst_var -> leaf (make_var x) (* for predicates *)
  | Proj(i,t) ->
      let Tree.Node(_, ts) = remove_pair_aux t in
      List.nth ts i
  | _ ->
      Format.eprintf "%a@." Print.term t;
      assert false

and remove_pair t = {(root (remove_pair_aux t)) with attr=t.attr}
let remove_pair t =
  let xs = get_vars t in
  let collided =
    let vars = List.map (fun x -> x, Id.to_string x) xs in
    let collides (x,s_x) (y,s_y) =
      String.starts_with s_y s_x &&
      let a,b = String.split ~by:s_x s_y in
      a = "" &&
      Exception.not_raise int_of_string b
    in
    vars
    |> List.filter (is_tuple_typ -| Id.typ -| fst)
    |> List.filter (fun (x,s) -> s = Id.name x)
    |> List.filter (fun x -> List.exists (collides x) vars)
    |> List.map fst
  in
  t
  |*@> Format.printf "INPUT: @[%a@." Print.term
  |> Trans.alpha_rename_if (Id.mem -$- collided)
  |*@> Format.printf "OUTPUT: @[%a@." Print.term
  |> remove_pair


let rec remove_pair_arg x ty =
  let xtys,map = remove_pair_ref_typ ty in
  match ty with
  | RT.Tuple ytys ->
      let xtys = List.map (Pair.map_fst Option.get) xtys in
      let map' = (x, make_tuple @@ List.map (fst |- make_var) ytys) :: map in
      xtys, map'
  | _ -> [x, snd @@ List.get xtys], []

and remove_pair_ref_typ ty =
  match ty with
  | RT.Base _ -> [None, ty], []
  | RT.Fun(x,ty1,ty2) ->
      let xtys,map = remove_pair_arg x ty1 in
      let ty2' =
        remove_pair_ref_typ ty2
        |> fst
        |> List.get
        |> snd
        |> RT.subst_map map
      in
      let ty' = List.fold_right (fun (x,ty1) ty2 -> RT.Fun(x,ty1,ty2)) xtys ty2' in
      [None, ty'], []
  | RT.Tuple xtys ->
      let aux (x,ty) (xtys,map) =
        let xtys',map' = remove_pair_arg x ty in
        List.map (Pair.map Option.some (RT.subst_map map)) xtys' @ xtys,
        map' @ map
      in
      List.fold_right aux xtys ([],[])
  | _ ->
      Format.eprintf "remove_pair_typ: %a@." Ref_type.print ty;
      assert false

let remove_pair_ref_typ (x,t) =
  let rec aux results =
    match results with
    | [] -> assert false
    | [_, ty] -> [x, ty]
    | _ ->
        let aux' (y,ty) (i,acc) =
          let x' = Id.add_name_after (string_of_int i) x in
          let y' = Option.get y in
          i+1, (x',ty) :: List.map (Pair.map_snd @@ Ref_type.map_pred @@ subst_var y' x) acc
        in
        snd @@ List.fold_right aux' results (0,[])
  in
  t
  |*@> Format.printf "INPUT: %a, @[%a@." Id.print x Ref_type.print
  |> remove_pair_ref_typ
  |> fst
  |> List.map (Pair.map_snd @@ Ref_type.map_pred Trans.eta_tuple)
  |*@> Format.printf "TRANS: @[%a@." Print.(list (option id * Ref_type.print))
  |> aux


let remove_pair ?(check=true) {Problem.term=t; env; attr; kind; info} =
  assert (check => List.mem Problem.ACPS attr);
  let pr s = Debug.printf "##[remove_pair] %s: %a@." s Print.term in
  let t' =
    t
    |@> pr "INPUT"
    |> Trans.null_tuple_to_unit
    |@> pr "null_tuple_to_unit"
    |> remove_pair
    |@> pr "remove_pair"
    |@check&> Type_check.check ~ty:typ_result
    |> Trans.beta_affine_fun
    |@> pr "beta_affine_fun"
    |> Trans.beta_size1
    |@> pr "beta_size1"
  in
  let env = List.flatten_map remove_pair_ref_typ env in
  {Problem.term=t'; env; attr; kind; info}, uncurry_rtyp t

let remove_pair_direct t =
  t
  |> Problem.safety
  |> remove_pair ~check:false
  |> Pair.map_fst Problem.term
