open Util
open Syntax
open Term_util
open Type

module RT = Ref_type


let get_rtyp_lift t f rtyp =
  let rec aux rtyp typ =
    match rtyp with
    | RT.Inter(styp, rtyps) -> RT.Inter(styp, List.map (aux -$- typ) rtyps)
    | RT.Union(styp, rtyps) -> RT.Union(styp, List.map (aux -$- typ) rtyps)
    | RT.Fun(x,rtyp1,rtyp2) ->
        if RT.arg_num rtyp = arg_num typ
        then rtyp
        else
          let rtyp' = aux rtyp2 typ in
          if RT.occur x rtyp'
          then RT.ExtArg(x, rtyp1, rtyp')
          else rtyp'
    | _ -> assert false
  in
  aux rtyp (Trans.assoc_typ f t)

let get_rtyp_lift t f rtyp =
  let rtyp' = get_rtyp_lift t f rtyp in
  if !!Flag.Debug.print_ref_typ
  then Format.printf "LIFT: %a: @[@[%a@]@ ==>@ @[%a@]@]@." Id.print f RT.print rtyp RT.print rtyp';
  rtyp'

module Id' = struct
  type t = id

  (* TODO: fix for dependencies on predicates *)
  let compare x y =
    let dbg = 0=1 in
    let count_pred x =
      match get_tapred @@ Id.typ x with
      | None -> 0
      | Some(_,ps) -> List.length ps
    in
    let aux z =
      not @@ is_base_typ @@ Id.typ z,
      count_pred z,
      Id.to_string z
    in
    if dbg then Format.printf "%a, %a@." Print.id_typ x Print.id_typ y;
        Compare.on aux x y
end

module IdSet = Set.Make(Id')

let set_of_list xs = List.fold_left (Fun.flip IdSet.add) IdSet.empty xs
let (@@@) = IdSet.union

let filter_base = IdSet.filter @@ is_base_typ -| Id.typ

let get_fv' = make_col2 IdSet.empty IdSet.union

let get_fv'_term vars t =
  match t.desc with
  | Var x -> if IdSet.mem x vars then IdSet.empty else IdSet.singleton x
  | Local(Decl_let bindings, t2) ->
      let vars' = List.fold_left (fun vars (f,_) -> IdSet.add f vars) vars bindings in
      let aux fv (_,t) = fv @@@ get_fv'.col2_term vars' t in
      let fv_t2 = get_fv'.col2_term vars' t2 in
      List.fold_left aux fv_t2 bindings
  | Fun(x,t) -> get_fv'.col2_term (IdSet.add x vars) t
  | Match(t,pats) ->
      let aux acc (pat,t) =
        let vars' = vars @@@ set_of_list @@ get_bv_pat pat in
        get_fv'.col2_term vars' t @@@ acc
      in
      List.fold_left aux (get_fv'.col2_term vars t) pats
  | _ -> get_fv'.col2_term_rec vars t

let () = get_fv'.col2_term <- get_fv'_term
let get_fv' t = get_fv'.col2_term IdSet.empty t

let rec lift_aux post xs t =
  let defs,desc =
    match t.desc with
    | Const _
    | Var _ -> [], t.desc
    | Fun(x,t1) ->
        let f = Id.new_var ~name:("f" ^ post) t.typ in
        let defs,t' = lift_aux post xs (make_let [f,t] @@ make_var f) in
        defs, t'.desc
    | App(t, ts) ->
        let defs,t' = lift_aux post xs t in
        let defss,ts' = List.split_map (lift_aux post xs) ts in
        defs @ (List.flatten defss), App(t', ts')
    | If(t1,t2,t3) ->
        let defs1,t1' = lift_aux post xs t1 in
        let defs2,t2' = lift_aux post xs t2 in
        let defs3,t3' = lift_aux post xs t3 in
        defs1 @ defs2 @ defs3, If(t1',t2',t3')
    | Local(Decl_let bindings,t2) ->
        let fv = List.fold_left (fun acc (_,t) -> acc @@@ get_fv' t) IdSet.empty bindings in
        let fv = IdSet.inter fv xs in
        let fv = if !Flag.Method.lift_fv_only then fv else filter_base xs @@@ fv in
        let fv = IdSet.diff fv (set_of_list @@ List.map fst bindings) in
        let fv = IdSet.elements fv in
        let fs =
          let aux (f,_) =
            let tfun x ty =
              let x' =
                let has_no_true_pred = List.for_all (function TARefPred(_, t) -> t.desc <> Const True | _ -> true) -| fst -| Type.decomp_tattr in
                if !Flag.PredAbst.shift_pred && is_base_var x && has_no_true_pred (Id.typ x) then
                  Id.map_typ (_TAttr [TARefPred(Id.new_var_id x, Term.true_)]) x
                else
                  x
              in
              TFun(x', ty)
            in
            let f' = Id.map_typ (List.fold_right tfun fv) f in
            f, (f', make_app (make_var f') @@ List.map make_var fv)
          in
          List.map aux bindings
        in
        let subst_f t = List.fold_left2 (fun t (_,(_,f'')) (f,_) -> subst f f'' t) t fs bindings in
        let aux (f,t1) =
          let ys,t1 = decomp_funs t1 in
          let ys' = fv @ ys in
          let f',_ = List.assoc f fs in
          let defs1,t1' = lift_aux ("_" ^ Id.name f) (set_of_list ys') (subst_f t1) in
          (f',(ys',t1'))::defs1
        in
        let defs = List.flatten_map aux bindings in
        let defs2,t2' = lift_aux post xs (subst_f t2) in
        defs @ defs2, t2'.desc
    | BinOp(op,t1,t2) ->
        let defs1,t1' = lift_aux post xs t1 in
        let defs2,t2' = lift_aux post xs t2 in
        defs1 @ defs2, BinOp(op,t1',t2')
    | Not t ->
        let defs,t' = lift_aux post xs t in
        defs, Not t'
    | Event(s,b) -> [], Event(s,b)
    | Record fields ->
        let aux (s,t) =
          let defs,t' = lift_aux post xs t in
          defs, (s,t')
        in
        let defss,fields' = List.split_map aux fields in
        List.flatten defss, Record fields'
    | Field(t,s) ->
        let defs,t' = lift_aux post xs t in
        defs, Field(t',s)
    | Nil -> [], Nil
    | Cons(t1,t2) ->
        let defs1,t1' = lift_aux post xs t1 in
        let defs2,t2' = lift_aux post xs t2 in
        defs1 @ defs2, Cons(t1',t2')
    | Constr(c,ts) ->
        let defss,ts' = List.split_map (lift_aux post xs) ts in
        List.flatten defss, Constr(c,ts')
    | Match(t,pats) ->
        let defs,t' = lift_aux post xs t in
        let aux (pat,t) (defs,pats) =
          let xs' = (set_of_list @@ get_bv_pat pat) @@@ xs in
          let defs',t' = lift_aux post xs' t in
          defs'@defs, (pat,t')::pats
        in
        let defs',pats' = List.fold_right aux pats (defs,[]) in
        defs', Match(t',pats')
    | Tuple ts ->
        let defss,ts' = List.split_map (lift_aux post xs) ts in
        List.flatten defss, Tuple ts'
    | Proj(i,t) ->
        let defs,t' = lift_aux post xs t in
        defs, Proj(i,t')
    | Bottom -> [], Bottom
    | _ -> Format.eprintf "lift: %a@." Print.term t; assert false
  in
  defs, {t with desc}

let lift ?(args=[]) t =
  lift_aux "" (set_of_list args) t,
  get_rtyp_lift t

(* for preprocess of termination mode *)
(* TODO: merge with lift *)
let rec lift_aux' post xs t =
  let defs,desc =
    match t.desc with
    | Const _
    | Var _ -> [], t.desc
    | Fun _ ->
        let f = Id.new_var ~name:("f" ^ post) t.typ in
        let aux f ys t1 t2 =
          let fv = IdSet.inter (get_fv' t1) xs in
          let fv = if !Flag.Method.lift_fv_only then fv else filter_base xs @@@ fv in
          let fv = IdSet.elements fv in
          let ys' = fv @ ys in
          let typ = List.fold_right (fun x typ -> TFun(x,typ)) fv (Id.typ f) in
          let f' = Id.set_typ f typ in
          let f'' = List.fold_left (fun t x -> make_app t [make_var x]) (make_var f') fv in
          let defs1,t1' = lift_aux' post (set_of_list ys') t1 in
          let defs2,t2' = lift_aux' post xs (subst f f'' t2) in
          defs1 @ [(f',(ys',t1'))] @ defs2, t2'
        in
        let xs,t1 = decomp_funs t in
        let defs,t' = aux f xs t1 (make_var f) in
        defs, t'.desc
    | App(t, ts) ->
        let defs,t' = lift_aux' post xs t in
        let defss,ts' = List.split_map (lift_aux' post xs) ts in
        defs @ (List.flatten defss), App(t', ts')
    | If(t1,t2,t3) ->
        let defs1,t1' = lift_aux' post xs t1 in
        let defs2,t2' = lift_aux' post xs t2 in
        let defs3,t3' = lift_aux' post xs t3 in
        defs1 @ defs2 @ defs3, If(t1',t2',t3')
    | Local(Decl_let [x, t1],t2) when is_non_rec [x,t1] ->
        let defs1, t1' = lift_aux' post xs t1 in
	let defs2, t2' = lift_aux' post (IdSet.add x xs) t2 in
        defs1 @ defs2, Local(Decl_let [x, t1'],t2')
    | Local(Decl_let bindings,t2) ->
        let fv = List.fold_left (fun acc (_,t) -> acc @@@ get_fv' t) IdSet.empty bindings in
        let fv = IdSet.inter fv xs in
        let fv = if !Flag.Method.lift_fv_only then fv else filter_base xs @@@ fv in
        let fv = IdSet.elements fv in
        let aux (f,_) =
          let f' = Id.set_typ f @@ List.fold_right _TFun fv @@ Id.typ f in
          f, (f', make_app (make_var f') @@ List.map make_var fv)
        in
        let fs = List.map aux bindings in
        let subst_f t = List.fold_left2 (fun t (_,(_,f'')) (f,_) -> subst f f'' t) t fs bindings in
        let aux (f,t1) =
          let ys,t1 = decomp_funs t1 in
          let ys' = fv @ ys in
          let f' = fst (List.assoc f fs) in
          let defs1,t1' = lift_aux' ("_" ^ Id.name f) (set_of_list ys') (subst_f t1) in
          (f',(ys',t1'))::defs1
        in
        let defs = List.flatten_map aux bindings in
        let defs2,t2' = lift_aux' post xs (subst_f t2) in
        defs @ defs2, t2'.desc
    | BinOp(op,t1,t2) ->
        let defs1,t1' = lift_aux' post xs t1 in
        let defs2,t2' = lift_aux' post xs t2 in
        defs1 @ defs2, BinOp(op,t1',t2')
    | Not t ->
        let defs,t' = lift_aux' post xs t in
        defs, Not t'
    | Event(s,b) -> [], Event(s,b)
    | Record fields ->
        let aux (s,t) =
          let defs,t' = lift_aux' post xs t in
          defs, (s,t')
        in
        let defss,fields' = List.split_map aux fields in
        List.flatten defss, Record fields'
    | Field(t,s) ->
        let defs,t' = lift_aux' post xs t in
        defs, Field(t',s)
    | Nil -> [], Nil
    | Cons(t1,t2) ->
        let defs1,t1' = lift_aux' post xs t1 in
        let defs2,t2' = lift_aux' post xs t2 in
        defs1 @ defs2, Cons(t1',t2')
    | Constr(c,ts) ->
        let defss,ts' = List.split_map (lift_aux' post xs) ts in
        List.flatten defss, Constr(c,ts')
    | Match(t,pats) ->
        let defs,t' = lift_aux' post xs t in
        let aux (pat,t) (defs,pats) =
          let xs' = (set_of_list @@ get_bv_pat pat) @@@ xs in
          let defs',t' = lift_aux' post xs' t in
          defs'@defs, (pat,t')::pats
        in
        let defs',pats' = List.fold_right aux pats (defs,[]) in
        defs', Match(t',pats')
    | Tuple ts ->
        let defss,ts' = List.split_map (lift_aux' post xs) ts in
        List.flatten defss, Tuple ts'
    | Proj(i,t) ->
        let defs,t' = lift_aux' post xs t in
        defs, Proj(i,t')
    | Bottom -> [], Bottom
    | _ -> Format.eprintf "lift: %a@." Print.term t; assert false
  in
  defs, {t with desc}

let lift' ?(args=[]) t =
  lift_aux' "" (set_of_list args) t, get_rtyp_lift t
