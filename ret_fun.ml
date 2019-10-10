open Util
open Type
open Syntax
open Term_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let normalize = make_trans ()

let normalize_term t =
  match t.desc with
  | App(t1,ts) ->
      let t1' = normalize.tr_term t1 in
      let ts' = List.map normalize.tr_term ts in
      let x = new_var_of_term t1 in
      let xs = List.map new_var_of_term ts in
      let aux (bindings,y) x =
        let t = make_app (make_var y) [make_var x] in
        let z = new_var_of_term t in
        bindings @ [z, t], z
      in
      let bindings,_ = List.fold_left aux ([],x) xs in
      let bindings',(_,t) = List.decomp_snoc bindings in
      let y = Id.new_var ~name:("r_" ^ Id.name x) t.typ in
      let bindings'' = bindings' @ [y, t] in
      let t = make_lets bindings'' @@ make_var y in
      make_lets (List.rev @@ List.combine (x::xs) (t1'::ts')) t
  | If(t1,t2,t3) ->
      let x = new_var_of_term t1 in
      let t1' = normalize.tr_term t1 in
      let t2' = normalize.tr_term t2 in
      let t3' = normalize.tr_term t3 in
      make_let [x, t1'] @@ make_if (make_var x) t2' t3'
  | BinOp(op,t1,t2) ->
      let t1' = normalize.tr_term t1 in
      let t2' = normalize.tr_term t2 in
      let x1 = new_var_of_term t1 in
      let x2 = new_var_of_term t2 in
      make_lets [x1,t1'; x2,t2'] @@ make_binop op (make_var x1) (make_var x2)
  | Not t1 ->
      let t1' = normalize.tr_term t1 in
      let x = new_var_of_term t in
      make_let [x, t1'] @@ make_not (make_var x)
  | Tuple ts ->
      let xs,ts' = List.split_map (Pair.make new_var_of_term normalize.tr_term) ts in
      make_lets (List.combine xs ts') @@ make_tuple @@ List.map make_var xs
  | Proj(i, t1) ->
      let t1' = normalize.tr_term t1 in
      let x = new_var_of_term t1' in
      make_let [x, t1'] @@ make_proj i (make_var x)
  | Nil
  | Cons _
  | Constr _
  | Match _
  | Raise _
  | TryWith _
  | Record _
  | Field _
  | SetField _ -> assert false
  | _ -> normalize.tr_term_rec t

let () = normalize.tr_term <- normalize_term
let normalize = normalize.tr_term


let add_proj_info = make_trans ()

let add_proj_info_term t =
  match t.desc with
  | Local(Decl_let [x,({desc=Tuple ts} as t1)], t2) when is_non_rec [x,t1] ->
      begin
        try
          let ys = List.mapi (fun i t -> match t.desc with Var x -> i,x | _ -> raise Not_found) ts in
          let t1' = add_proj_info.tr_term t1 in
          let t2' = add_proj_info.tr_term t2 in
          make_let [x,t1'] @@ List.fold_right (fun (i,y) t -> make_label ~label:"ret_fun" (InfoIdTerm(y, make_proj i @@ make_var x)) t) ys t2'
        with Not_found -> add_proj_info.tr_term_rec t
      end
  | _ -> add_proj_info.tr_term_rec t

let () = add_proj_info.tr_term <- add_proj_info_term
let add_proj_info = add_proj_info.tr_term


let get_same_pair env y z =
  let fsts = List.filter (function (y', Some _, None) -> Id.(y = y') | _ -> false) env in
  let snds = List.filter (function (z', None, Some _) -> Id.(z = z') | _ -> false) env in
  try
    Triple.snd @@ List.find (fun (_,p,_) -> List.exists (fun (_,_,p') -> Id.(Option.get p = Option.get p')) snds) fsts
  with Not_found -> None

let pair_eta_reduce = make_trans2 ()

let pair_eta_reduce_term env t =
  match t.desc with
  | Local(Decl_let [x,{desc=Proj(0,{desc=Var y})}], t2) ->
      pair_eta_reduce.tr2_term_rec ((x, Some y, None)::env) t
  | Local(Decl_let [x,{desc=Proj(1,{desc=Var y})}], t2) ->
      pair_eta_reduce.tr2_term_rec ((x, None, Some y)::env) t
  | Local(Decl_let [x,{desc=Tuple[{desc=Var y}; {desc=Var z}]}], t2) ->
      begin
        match get_same_pair env y z with
        | None -> pair_eta_reduce.tr2_term_rec env t
        | Some p -> subst_var x p @@ pair_eta_reduce.tr2_term env t2
      end
  | _ -> pair_eta_reduce.tr2_term_rec env t

let () = pair_eta_reduce.tr2_term <- pair_eta_reduce_term

let pair_eta_reduce = pair_eta_reduce.tr2_term []


let rec make_deep_pair t rhs =
  match t.desc with
  | If(t1,t2,t3) -> make_if t1 (make_deep_pair t2 rhs) (make_deep_pair t3 rhs)
  | Local(Decl_let bindings,t) -> make_let bindings @@ make_deep_pair t rhs
  | Label(info, t) -> make_label info (make_deep_pair t rhs)
  | _ -> make_pair t (make_var rhs)




let subst_all x y t = t
  |> subst_var x y
  |> make_label ~label:"ret_fun" @@ InfoIdTerm(x, make_var y)



let subst_label = make_trans2 ()

let subst_label_term (map,env) t =
  match t.desc with
  | Var x when Id.mem_assoc x map ->
      let t' = Id.assoc x map in
      if Id.mem x @@ get_fv t'
      then t'
      else subst_label.tr2_term (map,env) t'
  | Fun(x,t) -> make_fun x @@ subst_label.tr2_term (map,x::env) t
  | Local(Decl_let bindings, t2) ->
      let env' = List.map fst bindings @ env in
      let bindings' = List.map (Pair.map_snd @@ subst_label.tr2_term (map,env')) bindings in
      make_let bindings' @@ subst_label.tr2_term (map,env') t2
  | Label(InfoIdTerm(x,t1), t2) ->
      let map' =
        if Id.mem_assoc x map
        then
          try
            let t1' = Id.assoc x map in
            let envi = List.mapi Pair.pair env in
            let index t =
              let y = Option.get @@ decomp_var t in
              fst @@ List.find (snd |- Id.same y) envi
            in
            let t1'' = if index t1 < index t1' then t1 else t1' in
            (x,t1'') :: List.filter_out (fst |- Id.same x) map
          with Option.No_value -> (x,t1)::map
        else (x,t1)::map
      in
      subst_label.tr2_term (map',env) t2
  | _ -> subst_label.tr2_term_rec (map,env) t

let () = subst_label.tr2_term <- subst_label_term
let subst_label = subst_label.tr2_term ([],[])



let trans = make_trans2 ()

let is_higher x = order (Id.typ x) > 0

let trans_typ funargs typ =
  match typ with
  | TFun(x,typ) when is_higher x ->
      let x' = trans.tr2_var funargs x in
      let r = Id.new_var ~name:"r" @@ trans.tr2_typ funargs typ in
      TFun(x', TTuple[r; x'])
  | _ -> trans.tr2_typ_rec funargs typ

let trans_term funargs t =
  match t.desc with
  | Local(Decl_let ([x,{desc=App({desc=Var x1}, [{desc=Var x2}])}] as bindings), t1) when is_higher x2 && is_non_rec bindings ->
      let x' = trans.tr2_var funargs x in
      let x1' = trans.tr2_var funargs x1 in
      let x2' = trans.tr2_var funargs x2 in
      let t1' = trans.tr2_term funargs t1 in
      let t = make_app (make_var x1') [make_var x2'] in
      let p = Id.new_var ~name:(Id.name x' ^ "_" ^ Id.name x2') t.typ in
      let x2'' = Id.new_var_id x2' in
      let t1'' = subst_all x2' x2'' t1' in
      make_lets [p, t;
                 x', make_fst @@ make_var p;
                 x2'', make_snd @@ make_var p] t1''
  | Local(Decl_let ([x,{desc=App({desc=Var f}, [{desc=Var y}])}] as bindings) ,t1) when Id.mem f funargs && is_non_rec bindings ->
      let x' = trans.tr2_var funargs x in
      let f' = trans.tr2_var funargs f in
      let y' = trans.tr2_var funargs y in
      let t1' = trans.tr2_term funargs t1 in
      let f'' = Id.new_var_id f' in
      let z = Id.new_var_id y' in
      let tf = make_if (make_eq (make_var z) (make_var y)) (make_var x') (make_app (make_var f') [make_var z]) in
      make_lets [x',make_app (make_var f') [make_var y']; f'',make_fun z tf] @@ subst_all f' f'' t1'
  | Fun(x,t) when is_higher x ->
      let funargs' = x::funargs in
      let x' = trans.tr2_var funargs x in
      let t' = trans.tr2_term funargs' t in
      make_fun x' @@ make_deep_pair t' x'
  | Local(Decl_let bindings,t) ->
      let aux (f,t) =
        trans.tr2_var funargs f,
        trans.tr2_term funargs t
      in
      let bindings' = List.map aux bindings in
      let t' = trans.tr2_term funargs t in
      make_let bindings' t'
  | Nil
  | Cons _
  | Constr _
  | Match _
  | Raise _
  | TryWith _
  | Record _
  | Field _
  | SetField _ -> assert false
  | _ -> trans.tr2_term_rec funargs t

let () = trans.tr2_term <- trans_term
let () = trans.tr2_typ <- trans_typ

let trans t = t
  |@> Debug.printf "INPUT:@.%a@.@." Print.term
  |> normalize
  |@> Debug.printf "normalize:@.%a@.@." Print.term
  |> Trans.inline_var_const
  |@> Debug.printf "inline_var_const:@.%a@.@." Print.term
  |> Trans.flatten_let
  |@> Debug.printf "flatten_let:@.%a@.@." Print.term
  |@> Type_check.check
  |> add_proj_info
  |@> Debug.printf "add_proj_info:@.%a@.@." Print.term
  |> trans.tr2_term []
  |@> Debug.printf "ret_fun:@.%a@.@." Print.term_typ
  |> subst_label
  |@> Debug.printf "subst_label:@.%a@.@." Print.term_typ
  |> Trans.remove_label ~label:"ret_fun"
  |@> Debug.printf "remove_label:@.%a@.@." Print.term_typ
  |> Trans.flatten_tuple
  |@> Debug.printf "flatten_tuple:@.%a@.@." Print.term_typ
  |@> Type_check.check
  |*> Trans.inline_no_effect
  |> Trans.inline_var_const
  |@> Debug.printf "inline_var_const:@.%a@.@." Print.term_typ
  |> pair_eta_reduce
  |> Trans.flatten_let
  |@> Debug.printf "flatten_let:@.%a@.@." Print.term
  |> Trans.beta_no_effect_tuple
  |> Trans.inline_var
  |> Trans.elim_unused_let
  |@> Debug.printf "beta_var_tuple:@.%a@.@." Print.term
  |> Trans.reduce_bottom
  |@> Debug.printf "%a:@.%a@.@." Color.s_red "reduce_bottom" Print.term
  |@> Type_check.check

let trans t =
  trans t, fun _ _ -> raise Not_found
