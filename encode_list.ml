open Util
open Syntax
open Term_util
open Type


module RT = Ref_type


module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)



let rec is_filled_pattern p =
  try
    match p.pat_desc with
    | PAny -> None
    | PNondet -> None
    | PVar x -> Some (make_var x)
    | PAlias(p1,x) ->
        Some (Option.default (make_var x) @@ is_filled_pattern p1)
    | PConst c -> Some c
    | PConstr(c, ps) ->
        let ts = List.map is_filled_pattern ps in
        Some (make_construct c (List.map Option.get ts) p.pat_typ)
    | PNil -> Some (make_nil @@ list_typ p.pat_typ)
    | PCons(p1,p2) ->
        let t1 = Option.get @@ is_filled_pattern p1 in
        let t2 = Option.get @@ is_filled_pattern p2 in
        Some (make_cons t1 t2)
    | PTuple ps ->
        let ts = List.map is_filled_pattern ps in
        Some (make_tuple @@ List.map Option.get ts)
    | PRecord fields ->
        let sftyps = decomp_trecord p.pat_typ in
        assert (List.length fields = List.length sftyps);
        Some (make_record (List.map (Pair.map_snd @@ Option.get -| is_filled_pattern) fields) p.pat_typ)
    | PNone -> Some (make_none @@ option_typ p.pat_typ)
    | PSome p1 -> Some (make_some @@ Option.get @@ is_filled_pattern p1)
    | POr _ -> None
    | PWhen _ -> None
  with Option.No_value -> None


let subst_matched_var =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Match({desc=Var x}, pats) ->
        let aux (p,t1) =
          let t1' = tr.tr_term t1 in
          let sbst =
            match is_filled_pattern p with
            | None -> Fun.id
            | Some t' ->
                fun t0 ->
                  match t0 with
                  | {desc=Const True} -> t0
                  | _ when !Flag.Method.tupling -> make_label (InfoIdTerm(x, t')) t0
                  | _ -> subst x t' t0
          in
          p, sbst t1'
        in
        Match(make_var x, List.map aux pats)
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term


let rec get_rtyp_list rtyp typ =
  match rtyp, elim_tattr typ with
  | RT.Inter(_, rtyps), _ ->
     RT.Inter(typ, List.map (get_rtyp_list -$- typ) rtyps)
  | RT.Union(_, rtyps), _ ->
      RT.Union(typ, List.map (get_rtyp_list -$- typ) rtyps)
  (* TODO RT.Data *)
  | RT.Tuple[x, RT.Base(TInt, x', p_len); _, RT.Fun(y, RT.Base(TInt, y', p_i), typ2)], TApp(TList, [typ]) ->
      let p_len' = subst_var x' x p_len in
      let p_i' = subst_var y' y p_i in
      RT.List(x, p_len', y, p_i', get_rtyp_list typ2 typ)
  | RT.Tuple[x, RT.Base(TInt, x', p_len); _, RT.Inter(_, [])], TApp(TList, [typ]) ->
      let p_len' = subst_var x' x p_len in
      RT.List(x, p_len', Id.new_var typ_unknown, true_term, RT.Inter(typ, []))
  | RT.Tuple[x, RT.Base(TInt, x', p_len); _, RT.Inter(_, typs)], TApp(TList, [typ]) ->
      let typs' = List.map (fun typ -> RT.Tuple [x, RT.Base(TInt, x', p_len); Id.new_var typ_unknown, typ]) typs in
      get_rtyp_list (RT.Inter(typ_unknown, typs')) (make_tlist typ)
  | _, TApp(TList, [typ]) ->
      Format.eprintf "%a@." RT.print rtyp;
      raise (Fatal "not implemented get_rtyp_list")
  | RT.ADT(_,_,_), _ -> assert false
  | RT.Base(b,x,ps), _ -> RT.Base(b,x,ps)
  | RT.Fun(x,rtyp1,rtyp2), TFun(y,typ2) ->
      let rtyp1' = get_rtyp_list rtyp1 (Id.typ y) in
      let rtyp2' = get_rtyp_list rtyp2 typ2 in
      let rtyp2'' =
        match rtyp1' with
        | RT.List _ -> RT.replace_term Term.(fst (var x)) Term.(length (var x)) rtyp2'
        | _ -> rtyp2'
      in
      RT.Fun(x, rtyp1', rtyp2'')
  | RT.Tuple xrtyps, TTuple ys ->
      RT.Tuple (List.map2 (fun (x,rtyp) y -> x, get_rtyp_list rtyp (Id.typ y)) xrtyps ys)
  | RT.ExtArg(x,rtyp1,rtyp2), _ ->
      RT.ExtArg(x, rtyp1, get_rtyp_list rtyp2 typ)
  | RT.Exn(rtyp1,rtyp2), _ ->
      RT.Exn(get_rtyp_list rtyp1 typ, rtyp2)
  | _ ->
      Format.eprintf "rtyp:%a@.typ:%a@." RT.print rtyp Print.typ typ;
      assert false

let make_get_rtyp_list_of typed get_rtyp f =
  let typ = Trans.assoc_typ f typed in
  let rtyp = get_rtyp f in
  let rtyp' = get_rtyp_list rtyp typ in
  if !!Flag.Debug.print_ref_typ
  then Format.printf "LIST: %a: @[@[%a@]@ ==>@ @[%a@]@]@." Id.print f RT.print rtyp RT.print rtyp';
  rtyp'


let make_tl n t =
  let x = Id.new_var Ty.int in
  Term.(pair (fst t - int n) (fun_ x (snd t @ [var x + int n])))



let rec decomp_literal t =
  match t.desc with
  | Nil -> []
  | Cons(t1,t2) -> t1 :: decomp_literal t2
  | _ -> raise (Invalid_argument "decomp_literal")

let is_literal t =
 try
   ignore (decomp_literal t); true
 with Invalid_argument _ -> false

let encode_list = make_trans2 ()

let encode_list_typ post typ =
  match typ with
  | TVar({contents=None},_) -> fatal "Polymorphic types occur! (Encode_list.encode_list_typ)"
  | TApp(TList, [typ]) ->
      let l = Id.new_var ~name:"l" Ty.int in
      TTuple[l; Id.new_var @@ pureTFun(Id.new_var ~name:"i" Ty.int, encode_list.tr2_typ post typ)]
  | _ -> encode_list.tr2_typ_rec post typ

let print_bind fm bind =
  Format.fprintf fm "@[[";
  List.iter (fun (x,t) -> Format.fprintf fm "%a := %a;@ " Id.print x Print.term t) bind;
  Format.fprintf fm "]@]"

let add_bind bind t =
  let aux (x,t) t' =
    let x' =
      if Id.mem x @@ get_fv t then
        Id.new_var_id x
      else
        x
    in
    make_let_s [x',t] @@ subst_var x x' t'
  in
  List.fold_right aux bind t

let replace_simple_match_with_if =
  let tr = make_trans () in
  let rec get_subst t p =
    match p.pat_desc with
    | PAny -> Some Fun.id
    | PVar x -> Some (subst ~rename_if_captured:true x t)
    | PTuple ps ->
        let sbsts = List.mapi (fun i p -> get_subst Term.(proj i t) p) ps in
        List.fold_right Option.(fun sbst acc -> sbst >>= (fun x -> lift ((-|) x) acc)) sbsts (Some Fun.id)
    | _ -> None
  in
  let tr_desc desc =
    match desc with
    | Match(t, ({pat_desc=PWhen(p, cond)},t1)::pats) when Option.is_some @@ get_subst t p ->
        let t',bind =
          if has_no_effect t then
            t, Fun.id
          else
            let x = new_var_of_term t in
            Term.var x, Term.let_ [x,t]
        in
        let t2 = Term.(match_ ~typ:t1.typ t' pats) in
        let sbst = Option.get @@ get_subst t' p in
        let cond' = tr.tr_term @@ sbst cond in
        let t1' = tr.tr_term @@ sbst t1 in
        let t2' = tr.tr_term t2 in
        Term.(bind (if_ cond' t1' t2')).desc
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let rec encode_list_pat p =
  let pat_typ = encode_list.tr2_typ "" p.pat_typ in
  let pat_desc,bind =
    match p.pat_desc with
    | PAny -> PAny, []
    | PNondet -> PNondet, []
    | PVar x -> PVar (encode_list.tr2_var "" x), []
    | PAlias(p,x) ->
        let p',bind = encode_list_pat p in
        PAlias(p', encode_list.tr2_var "" x), bind
    | PConst t -> PConst t, []
    | PConstr(c,ps) ->
        let ps',binds = List.split_map encode_list_pat ps in
        PConstr(c,ps'), List.flatten binds
    | PNil ->
        let x = Id.new_var ~name:"xs" pat_typ in
        let cond = Term.(fst (var x) <= int 0) in
        PWhen(Pat.(var x), cond), []
    | PCons({pat_desc=PVar x1}, {pat_desc=PVar x2}) ->
        let x1' = encode_list.tr2_var "" x1 in
        let x2' = encode_list.tr2_var "" x2 in
        let x = Id.new_var ~name:"xs" pat_typ in
        let cond = Term.(fst (var x) > int 0) in
        let t1 = Term.(snd (var x) @ [int 0]) in
        let t2 =
          let i = Id.new_var Ty.int in
          Term.(pair (fst (var x) - int 1) (pfun i (snd (var x) @ [var i + int 1])))
        in
        let bind = [x1',t1; x2',t2] in
        PWhen(Pat.(var x), make_lets_s bind cond), bind
    | PCons _ -> assert false
    | PRecord fields ->
        let fields',binds =
          let aux (s,p) =
            let p',bind = encode_list_pat p in
            (s,p'), bind
          in
          List.split_map aux fields
        in
        PRecord fields', List.flatten binds
    | POr(p1,p2) ->
        let p1',bind1 = encode_list_pat p1 in
        let p2',bind2 = encode_list_pat p2 in
        if bind1 <> [] || bind2 <> [] then unsupported "POr";
        POr(p1', p2'), []
    | PTuple ps ->
        let ps',binds = List.split_map (encode_list_pat) ps in
        PTuple ps', List.flatten binds
    | PNone -> PNone, []
    | PSome p ->
        let p',bind = encode_list_pat p in
        PSome p', bind
    | PWhen(p, cond) ->
        let cond' = encode_list.tr2_term "" cond in
        let p',bind = encode_list_pat p in
        PWhen(p', make_lets_s bind cond'), bind
  in
  {pat_desc; pat_typ}, bind

let rec make_rand typ =
  match typ with
  | TApp(TList, [typ']) ->
      let l = Id.new_var ~name:"l" Ty.int in
      Term.(let_ [l, randi]
           (assume (int 0 <= var l)
           (pair (var l) (fun_ (Id.new_var Ty.int) (rand typ')))))
  | _ -> make_rand_unit typ

let encode_list_term post t =
  match t.desc with
  | App({desc=Const(Rand(TBase TInt,false)); attr}, t2) when List.mem AAbst_under attr -> (* for disproving termination  *)
      assert (t2 = [unit_term]);
      t
  | App({desc=Const(Rand(typ,false))}, t2) ->
      assert (t2 = [unit_term]);
      make_rand_unit @@ encode_list.tr2_typ post t.typ
  | App({desc=Var x}, [t1]) when Id.name x = "List.length" ->
      let t1' = encode_list.tr2_term post t1 in
      Term.(fst t1')
  | App({desc=Var x}, [t1; t2]) when Id.name x = "List.nth" ->
      let t1' = encode_list.tr2_term post t1 in
      let t2' = encode_list.tr2_term post t2 in
      Term.(snd t1' @ [t2'])
  | App({desc=Var x}, [t]) when is_length_var x -> make_fst @@ encode_list.tr2_term post t
  | Local(Decl_let bindings, t2) ->
      let aux (f,t) =
        let post' = "_" ^ Id.name f in
        encode_list.tr2_var post f, encode_list.tr2_term post' t
      in
      let bindings' = List.map aux bindings in
      make_let bindings' (encode_list.tr2_term post t2)
  | Nil ->
      let typ' = encode_list.tr2_typ post @@ list_typ t.typ in
      Term.(pair (int 0) (pfun (Id.new_var Ty.int) (bot typ')))
  | Cons _ ->
      let rec decomp_and_tr t =
        match t.desc with
        | Cons(t1,t2) ->
            let ts,t2' = decomp_and_tr t2 in
            let t1' = encode_list.tr2_term post t1 in
            t1'::ts, t2'
        | _ -> [], encode_list.tr2_term post t
      in
      let ts,t2 = decomp_and_tr t in
      let xs = List.map new_var_of_term ts in
      let bindings = List.rev @@ List.combine xs ts in
      let x = Id.new_var ~name:"i" Ty.int in
      let n = List.length ts in
      let _,t =
        let t0 = Term.(snd t2 @ [var x - int n]) in
        let aux y (i,t) =
          i-1, Term.(if_ (var x = int i) (var y) t)
        in
        List.fold_right aux xs (n-1, t0)
      in
      Term.(lets bindings (pair (int n + fst t2) (pfun x t)))
  | Match(t1,pats) ->
      let t1' = encode_list.tr2_term post t1 in
      let aux (p,t) =
        let p',bind = encode_list_pat p in
        let t' = encode_list.tr2_term post t in
        p', make_nonrec_lets_s bind t'
      in
      let pats' = List.map aux pats in
      Term.(match_ t1' pats')
  | _ -> encode_list.tr2_term_rec post t

let () = encode_list.tr2_term <- encode_list_term
let () = encode_list.tr2_typ <- encode_list_typ

let trans t =
  let t' =
    t
    |@> Debug.printf "[encode_list] input:@. @[%a@.@." Print.term'
    |> encode_list.tr2_term ""
    |@> Debug.printf "[encode_list] encode_list:@. @[%a@.@." Print.term_typ
    |> Trans.inline_var_const
    |@> Debug.printf "[encode_list] inline_var_const:@. @[%a@.@." Print.term_typ
    |> Trans.lift_pwhen
    |@> Debug.printf "[encode_list] lift_pwhen:@. @[%a@.@." Print.term_typ
    |> replace_simple_match_with_if
    |@> Debug.printf "[encode_list] replace_simple_match_with_if:@. @[%a@.@." Print.term_typ
  in
  let ty = encode_list.tr2_typ "" t.typ in
  Type_check.check t' ~ty;
  t', make_get_rtyp_list_of t





let make_list_eq typ =
  let f = Id.new_var ~name:"Primitive.list_eq" @@ pureTFun(Id.new_var ~name:"xs" @@ make_tlist typ, pureTFun(Id.new_var ~name:"xs" @@ make_tlist typ, Ty.bool)) in
  let xs = Id.new_var ~name:"xs'" @@ make_tlist typ in
  let ys = Id.new_var ~name:"ys'" @@ make_tlist typ in
  let t_eq =
    let pat_nil =
      let p1 = make_ppair (make_pnil typ) (make_pnil typ) in
      let t1 = true_term in
      p1, t1
    in
    let pat_cons =
      let x = Id.new_var ~name:"x" typ in
      let xs' = Id.new_var ~name:"xs'" @@ make_tlist typ in
      let y = Id.new_var ~name:"y" typ in
      let ys' = Id.new_var ~name:"ys'" @@ make_tlist typ in
      let p2 = make_ppair (make_pcons (make_pvar x) (make_pvar xs')) (make_pcons (make_pvar y) (make_pvar ys')) in
      let t2 = make_and (make_eq (make_var x) (make_var y)) (make_app (make_var f) [make_var xs'; make_var ys']) in
      p2, t2
    in
    let pat_any =
      let p3 = make_ppair (make_pany (make_tlist typ)) (make_pany (make_tlist typ)) in
      let t3 = false_term in
      p3, t3
    in
    make_match (make_pair (make_var xs) (make_var ys)) [pat_nil; pat_cons; pat_any]
  in
  f, make_funs [xs;ys] t_eq

(* TODO: support other types *)
let inst_list_eq = make_trans2 ()
let inst_list_eq_term map t =
  match t.desc with
  | BinOp(Eq, ({desc=Var(path)}), {desc=Nil; typ=TApp(TList, [typ])}) when path.Id.name = "path" ->
      (* XXX temporary measure
         path = nil
       *)
      let t1' = make_var @@ Id.set_typ path Ty.(pair int (fun_ int typ)) in
      Term.(fst t1' = int 0)
  | BinOp(Eq, t1, t2) ->
      let t1' = inst_list_eq.tr2_term map t1 in
      let t2' = inst_list_eq.tr2_term map t2 in
      begin
        match t1.typ with
        | TApp(TList, [TBase TInt|TData _ as typ]) when List.mem_assoc typ map ->
            if !Flag.Encode.abst_list_eq then
              (Flag.Encode.use_abst "List equality";
               randbool_unit_term)
            else
              make_app (make_var @@ List.assoc typ map) [t1'; t2']
        | TApp(TList, _) ->
            Flag.Encode.use_abst "List equality";
            randbool_unit_term
        | _ -> inst_list_eq.tr2_term_rec map t
      end
  | _ -> inst_list_eq.tr2_term_rec map t
let () = inst_list_eq.tr2_term <- inst_list_eq_term
let inst_list_eq t =
  let defs = List.map (Pair.add_right make_list_eq) [Ty.int; TData "string"] in(* TODO *)
  let map = List.map (Pair.map_snd fst) defs in
  let t' = inst_list_eq.tr2_term map t in
  let fv = get_fv t' in
  let defs' = List.filter (fun (_,(f,_)) -> Id.mem f fv) defs in
  if !Flag.Encode.abst_list_eq then
    t'
  else
    make_lets (List.map snd defs') t'




let rec get_rtyp_list_opt rtyp typ = raise (Fatal "not implemented get_rtyp_list_opt")

let get_rtyp_list_of typed f rtyp =
  let typ = Trans.assoc_typ f typed in
  let rtyp' = get_rtyp_list_opt rtyp typ in
  if !!Flag.Debug.print_ref_typ
  then Format.printf "LIST: %a: @[@[%a@]@ ==>@ @[%a@]@]@." Id.print f RT.print rtyp RT.print rtyp';
  rtyp'


let make_tl_opt n t =
  let x = Id.new_var ~name:"x" Ty.int in
  make_fun x (make_app t [make_add (make_var x) (make_int n)])


let encode_list_opt = make_trans ()

let encode_list_opt_typ typ =
  match typ with
  | TVar({contents=None},_) -> raise (Fatal "Polymorphic types occur! (Encode_list.encode_list_opt_typ)")
  | TApp(TList, [typ]) -> TFun(Id.new_var ~name:"i" Ty.int, opt_typ @@ encode_list_opt.tr_typ typ)
  | _ -> encode_list_opt.tr_typ_rec typ

let rec get_match_bind_cond_opt t p =
  match p.pat_desc with
  | PAny -> [], true_term
  | PVar x -> [encode_list_opt.tr_var x, t], true_term
  | PAlias(p,x) ->
      let bind,cond = get_match_bind_cond_opt t p in
      (encode_list_opt.tr_var x, t)::bind, cond
  | PConst {desc=Const Unit} -> [], true_term
  | PConst t' -> [], make_eq t t'
  | PConstr _ -> assert false
  | PNil -> [], make_is_none (make_app t [make_int 0])
  | PCons _ ->
      let rec decomp = function
          {pat_desc=PCons(p1,p2)} ->
          let ps,p = decomp p2 in
          p1::ps, p
        | p -> [], p
      in
      let ps,p' = decomp p in
      let rec aux bind cond i = function
          [] -> bind, cond
        | p::ps ->
            let bind',cond' = get_match_bind_cond_opt (make_get_val (make_app t [make_int i])) p in
            aux (bind'@bind) (make_and cond cond') (i+1) ps
      in
      let len = List.length ps in
      let bind, cond = get_match_bind_cond_opt (make_tl_opt len t) p' in
      aux bind (make_and (make_is_some (make_app t [make_int (len-1)])) cond) 0 ps
  | PTuple ps ->
      let binds,conds = List.split @@ List.mapi (fun i p -> get_match_bind_cond_opt (make_proj i t) p) ps in
      List.rev_flatten binds,
      List.fold_left make_and true_term conds
  | _ -> Format.eprintf "get_match_bind_cond_opt: %a@." Print.pattern p; assert false

let encode_list_opt_term t =
  let typ' = encode_list_opt.tr_typ t.typ in
  match t.desc with
  | App({desc=Var x}, [t1; t2]) when Id.name x = "List.nth" ->
      let t1' = encode_list_opt.tr_term t1 in
      let t2' = encode_list_opt.tr_term t2 in
      let t = make_app t1' [t2'] in
      let x = Id.new_var t.typ in
      make_let [x,t] @@ make_get_val @@ make_var x
  | Nil ->
      let el_typ = snd_typ @@ result_typ typ' in
      make_fun (Id.new_var Ty.int) (make_none el_typ)
  | Cons(t1,t2) ->
      let t1' = encode_list_opt.tr_term t1 in
      let t2' = encode_list_opt.tr_term t2 in
      let i = Id.new_var ~name:"i" Ty.int in
      let x = Id.new_var ~name:"x" t1'.typ in
      let xs = Id.new_var ~name:"xs" t2'.typ in
      let t11 = make_eq (make_var i) (make_int 0) in
      let t12 = make_some (make_var x) in
      let t13 = make_app (make_var xs) [make_sub (make_var i) (make_int 1)] in
      if true
      then
        Term.(lets [x,t1'; xs,t2'] (fun_ i (if_ t11 t12 t13)))
      else
        let cns = Id.new_var ~name:"cons" (TFun(x,TFun(xs,t2'.typ))) in
        Term.(let_ [cns, funs [x;xs;i] (if_ t11 t12 t13)] (var cns @ [t1'; t2']))
  | Match(t1,pats) ->
      let x = Id.new_var ~name:"xs" (encode_list_opt.tr_typ t1.typ) in
      let aux (p,t) t' =
        let bind,cond = get_match_bind_cond_opt (make_var x) p in
        make_if cond (add_bind bind (encode_list_opt.tr_term t)) t'
      in
      let t_pats = List.fold_right aux pats (make_bottom typ') in
      make_let [x, encode_list_opt.tr_term t1] t_pats
  | _ -> encode_list_opt.tr_term_rec t

let () = encode_list_opt.tr_typ <- encode_list_opt_typ
let () = encode_list_opt.tr_term <- encode_list_opt_term

let trans_opt t =
  let t' = encode_list_opt.tr_term t in
  let t' = Trans.inline_var_const t' in
(*
  let t' = Trans.subst_let_xy t' in
*)
  if false then Format.printf "encode_list::@. @[%a@.@." Print.term t';
  Type_check.check t';
  t', fun _ _ -> raise Not_found



let pr s t = Debug.printf "##[encode_list] %s:@.%a@.@." s Print.term t

let trans_term t =
  let tr =
    if !Flag.Encode.encode_list_opt then
      trans_opt
    else
      trans
  in
  t
  |@> Type_check.check ~ty:t.typ
  |> inst_list_eq
  |@> pr "inst_list_eq"
  |> Trans.decompose_match
  |> Trans.lift_pwhen
  |@> pr "decompose_match"
  |> subst_matched_var
  |@> pr "subst_matched_var"
  |@> Type_check.check ~ty:t.typ
  |*> Trans.remove_top_por
  |*@> pr "remove_top_por"
  |*@> Type_check.check ~ty:t.typ
  |> tr
  |@> (fun t -> Type_check.check t ~ty:t.typ) -| fst
  |@> pr "trans" -| fst
  |> Pair.map_fst Trans.eta_tuple
  |@> pr "eta_tuple" -| fst
  |> Pair.map_fst Trans.inline_var
  |@> pr "inline_var" -| fst

let trans_var x =
  if !Flag.Encode.encode_list_opt then
    encode_list_opt.tr_var x
  else
    encode_list.tr2_var "" x

let trans_typ typ =
  if !Flag.Encode.encode_list_opt then
    encode_list_opt.tr_typ typ
  else
    encode_list.tr2_typ "" typ

let rec trans_rty ty =
  let open Ref_type in
  match ty with
  | Base(base,x,t) -> Base(base, x, fst @@ trans_term t)
  | ADT(_,_,_) -> assert false
  | Fun(x,ty1,ty2) -> Fun(trans_var x, trans_rty ty1, trans_rty ty2)
  | Tuple xtys -> Tuple (List.map (Pair.map trans_var trans_rty) xtys)
  | Inter(sty,tys) -> Inter(trans_typ sty, List.map trans_rty tys)
  | Union(sty,tys) -> Union(trans_typ sty, List.map trans_rty tys)
  | ExtArg(x,ty1,ty2) -> ExtArg(trans_var x, trans_rty ty1, trans_rty ty2)
  | List(x,p_len,y,p_i,ty2) ->
      if !Flag.Encode.encode_list_opt then
        unsupported "encode_list_opt"
      else
        let p_len',_ = trans_term p_len in
        let p_i',_ = trans_term p_i in
        let ty2' = trans_rty ty2 in
        let ty_f = Fun(y, Base(TInt,y,p_i'), ty2') in
        let f = Id.new_var @@ to_simple ty_f in
        Tuple [x,Base(TInt,x,p_len'); f, ty_f]
  | App _ -> unsupported "Encode_list.trans_rty App"
  | Exn(ty1,ty2) -> Exn(trans_rty ty1, trans_rty ty2)

let trans_env env =
  List.map (Pair.map_snd trans_rty) env

let trans = Problem.map_on Focus.fst ~tr_env:trans_env trans_term
