open Util
open Type
open Type_util
open Syntax
open Term_util


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
    | PConstr(poly, c, ps) ->
        let ts = List.map is_filled_pattern ps in
        Some (make_construct ~poly c (List.map Option.get ts) p.pat_typ)
    | PNil -> Some (make_nil ~elem_typ:(list_typ p.pat_typ))
    | PCons(p1,p2) ->
        let t1 = Option.get @@ is_filled_pattern p1 in
        let t2 = Option.get @@ is_filled_pattern p2 in
        Some (make_cons t1 t2)
    | PTuple ps ->
        let ts = List.map is_filled_pattern ps in
        Some (make_tuple @@ List.map Option.get ts)
    | PRecord fields ->
        let sftyps = ValE'._TRecord p.pat_typ in
        assert (List.length fields = List.length sftyps);
        Some (make_record (List.map (Pair.map_snd @@ Option.get -| is_filled_pattern) fields) p.pat_typ)
    | PNone -> Some (make_none_enc @@ option_typ p.pat_typ)
    | PSome p1 -> Some (make_some_enc @@ Option.get @@ is_filled_pattern p1)
    | POr _ -> None
    | PWhen _ -> None
    | _ -> assert false
  with Option.No_value -> None


let subst_matched_var =
  let tr = Tr.make () in
  let tr_desc desc =
    match desc with
    | Match({desc=Var (LId x)}, pats) ->
        let aux (p,t1) =
          let t1' = tr.term t1 in
          let sbst =
            match is_filled_pattern p with
            | None -> Fun.id
            | Some t' ->
                fun t0 ->
                  match t0 with
                  | {desc=Const True} -> t0
                  | _ when !Flag.Method.tupling -> make_label (InfoIdTerm(x, t')) t0
                  | t0 -> subst x t' t0
          in
          p, sbst t1'
        in
        Match(make_var x, List.map aux pats)
    | _ -> tr.desc_rec desc
  in
  tr.desc <- tr_desc;
  tr.term


let rec get_rtyp_list rtyp typ =
  match rtyp, elim_tattr typ with
  | RT.Inter(_, rtyps), _ ->
     RT.Inter(typ, List.map (get_rtyp_list -$- typ) rtyps)
  | RT.Union(_, rtyps), _ ->
      RT.Union(typ, List.map (get_rtyp_list -$- typ) rtyps)
  (* TODO RT.Data *)
  | RT.Tuple[x, RT.Base(TInt, x', p_len); _, RT.Fun(y, RT.Base(TInt, y', p_i), typ2)], TConstr(c, [typ]) when Path.(c = C.list) ->
      let p_len' = subst_var x' x p_len in
      let p_i' = subst_var y' y p_i in
      RT.List(x, p_len', y, p_i', get_rtyp_list typ2 typ)
  | RT.Tuple[x, RT.Base(TInt, x', p_len); _, RT.Inter(_, [])], TConstr(c, [typ]) when Path.(c = C.list) ->
      let p_len' = subst_var x' x p_len in
      RT.List(x, p_len', Id.new_var typ_unknown, true_term, RT.Inter(typ, []))
  | RT.Tuple[x, RT.Base(TInt, x', p_len); _, RT.Inter(_, typs)], TConstr(c, [typ]) when Path.(c = C.list) ->
      let typs' = List.map (fun typ -> RT.Tuple [x, RT.Base(TInt, x', p_len); Id.new_var typ_unknown, typ]) typs in
      get_rtyp_list (RT.Inter(typ_unknown, typs')) (make_tlist typ)
  | _, TConstr(c, [_typ]) when c = C.list ->
      Format.eprintf "%a@." RT.print rtyp;
      failwith "not implemented get_rtyp_list"
  | RT.Constr(_,_,_,_), _ -> assert false
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
  then Format.fprintf !Flag.Print.target "LIST: %a: @[@[%a@]@ ==>@ @[%a@]@]@." Id.print f RT.print rtyp RT.print rtyp';
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

let encode_list = Tr2.make ()

let encode_list_typ post typ =
  match typ with
  | TVar(_,{contents=None},_) -> failwith "Polymorphic types occur! (%s)" __FUNCTION__
  | TConstr(c, [typ]) when c = C.list ->
      let l = Id.new_var ~name:"l" Ty.int in
      TTuple[l; Id.new_var @@ pureTFun(Id.new_var ~name:"i" Ty.int, encode_list.typ post typ)]
  | _ -> encode_list.typ_rec post typ

let print_bind fm bind =
  Format.fprintf fm "@[[";
  List.iter (fun (x,t) -> Format.fprintf fm "%a := %a;@ " Id.print x Print.term t) bind;
  Format.fprintf fm "]@]"

let add_bind bind t =
  let aux (x,t) t' =
    let x' =
      if occur_in x t then
        Id.new_var_id x
      else
        x
    in
    make_let_s [x',t] @@ subst_var x x' t'
  in
  List.fold_right aux bind t

let remove_palias =
  let tr = Tr.make () in
  let tr_pat p =
    match p.pat_desc with
    | PAlias _ -> unsupported "Encode_list.remove_palias"
    | _ -> tr.pat_rec p
  in
  let tr_desc desc =
    match desc with
    | Match(t, pats) ->
        let aux (p,t) =
          match p.pat_desc with
          | PWhen({pat_desc = PAlias({pat_desc=PVar x}, y)}, cond) ->
              let sbst = subst_var x y in
              Pat.(when_ (var y) (sbst cond)), sbst t
          | PAlias({pat_desc=PVar x}, y) ->
              let sbst = subst_var x y in
              Pat.(var y), sbst t
          | _ -> p, t
        in
        let pats' = List.map aux pats in
        Match(tr.term t, pats')
    | _ -> tr.desc_rec desc
  in
  tr.desc <- tr_desc;
  tr.pat <- tr_pat;
  tr.term

let remove_match =
  let tr = Tr.make () in
  let rec get_subst t p =
    match p.pat_desc with
    | PAny -> Some Fun.id
    | PVar x -> Some (subst x t)
    | PAlias({pat_desc=PVar x}, y) -> Some (subst x t -| subst y t)
    | PTuple ps ->
        let sbsts = List.mapi (fun i p -> get_subst Term.(proj i t) p) ps in
        List.fold_right Option.(fun sbst acc -> sbst >>= (fun x -> lift ((-|) x) acc)) sbsts (Some Fun.id)
    | _ -> None
  in
  let tr_desc desc =
    match desc with
    | Match(t, pats) ->
        begin
          match pats with
          | [{pat_desc=PVar x}, t1]
          | [{pat_desc=PAlias({pat_desc=PAny}, x)}, t1] ->
              let t = tr.term t in
              let t1 = tr.term t1 in
              Local(Decl_let [x,t], t1)
          | [{pat_desc=PAlias({pat_desc=PVar x}, y)}, t1] ->
              let t = tr.term t in
              let t1 = tr.term t1 in
              Term.(lets [x,t; y, var x] t1).desc
          | ({pat_desc=PWhen(p, cond)},t1)::pats when Option.is_some @@ get_subst t p ->
              let t',bind =
                if has_no_effect t then
                  t, Fun.id
                else
                  let x = new_var_of_term t in
                  Term.var x, Term.let_ [x,t]
              in
              let t2 = Term.match_ ~typ:t1.typ t' pats in
              let sbst = Option.get @@ get_subst t' p in
              let cond' = tr.term @@ sbst cond in
              let t1' = tr.term @@ sbst t1 in
              let t2' = tr.term t2 in
              (bind (Term.if_ cond' t1' t2')).desc
          | _ ->
              Format.eprintf "Match remains: %a@." Print.desc desc;
              assert false
        end
    | _ -> tr.desc_rec desc
  in
  tr.desc <- tr_desc;
  tr.term <- tr.term_rec |- set_afv_shallowly;
  tr.term

let rec encode_list_pat p =
  let pat_typ = encode_list.typ "" p.pat_typ in
  let pat_desc,bind =
    match p.pat_desc with
    | PAny -> PAny, []
    | PNondet -> PNondet, []
    | PVar x -> PVar (encode_list.var "" x), []
    | PAlias(p,x) ->
        let p',bind = encode_list_pat p in
        PAlias(p', encode_list.var "" x), bind
    | PConst t -> PConst t, []
    | PConstr(b,c,ps) ->
        let ps',binds = List.split_map encode_list_pat ps in
        PConstr(b,c,ps'), List.flatten binds
    | PNil ->
        let x = Id.new_var ~name:"xs" pat_typ in
        let cond = Term.(fst (var x) <= int 0) in
        PWhen(Pat.(var x), cond), []
    | PCons({pat_desc=PVar x1}, {pat_desc=PVar x2}) ->
        let x1' = encode_list.var "" x1 in
        let x2' = encode_list.var "" x2 in
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
        let cond' = encode_list.term "" cond in
        let p',bind = encode_list_pat p in
        PWhen(p', make_lets_s bind cond'), bind
    | PLazy p ->
        let p',bind = encode_list_pat p in
        PLazy p', bind
    | PEval _ -> assert false
  in
  make_pattern pat_desc pat_typ, bind

let make_rand typ =
  match typ with
  | TConstr(c, [typ']) when c = C.list ->
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
  | App({desc=Const(Rand(ty,false))}, t2::ts) ->
      assert (t2.desc = Const Unit);
      let ty' = encode_list.typ post ty in
      let ts' = List.map (encode_list.term post) ts in
      Term.(rand ty' @ ts')
  | App({desc=Var x}, [t1]) when is_length_var x ->
      let t1' = encode_list.term post t1 in
      Term.(fst t1')
  | App({desc=Var x}, [t1; t2]) when Lid.to_string x = "List.nth" ->
      let t1' = encode_list.term post t1 in
      let t2' = encode_list.term post t2 in
      Term.(snd t1' @ [t2'])
  | App({desc=Var x}, [t]) when is_length_var x -> make_fst @@ encode_list.term post t
  | Local(Decl_let bindings, t2) ->
      let aux (f,t) =
        let post' = "_" ^ Id.name f in
        encode_list.var post f, encode_list.term post' t
      in
      let bindings' = List.map aux bindings in
      make_let bindings' (encode_list.term post t2)
  | Nil ->
      let typ' = encode_list.typ post @@ list_typ t.typ in
      Term.(pair (int 0) (pfun (Id.new_var Ty.int) (bot typ')))
  | Cons _ ->
      let rec decomp_and_tr t =
        match t.desc with
        | Cons(t1,t2) ->
            let ts,t2' = decomp_and_tr t2 in
            let t1' = encode_list.term post t1 in
            t1'::ts, t2'
        | _ -> [], encode_list.term post t
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
      let t1' = encode_list.term post t1 in
      let aux (p,t) =
        let p',bind = encode_list_pat p in
        let t' = encode_list.term post t in
        p', make_nonrec_lets_s bind t'
      in
      let pats' = List.map aux pats in
      Term.(match_ t1' pats')
  | _ ->
      t
      |> encode_list.term_rec post
      |> set_afv_shallowly

let () = encode_list.term <- encode_list_term
let () = encode_list.typ <- encode_list_typ

let trans t =
  let t' =
    t
    |@> Debug.printf "[encode_list] input:@. @[%a@.@." Print.term'
    |> encode_list.term ""
    |@> Debug.printf "[encode_list] encode_list:@. @[%a@.@." Print.term_typ
    |> Trans.inline_var_const
    |@> Debug.printf "[encode_list] inline_var_const:@. @[%a@.@." Print.term_typ
    |> Trans.lift_pwhen
    |@> Debug.printf "[encode_list] lift_pwhen:@. @[%a@.@." Print.term_typ
    |> remove_palias
    |@> Debug.printf "[encode_list] remove_palias:@. @[%a@.@." Print.term_typ
    |> remove_match
    |@> Debug.printf "[encode_list] remove_match:@. @[%a@.@." Print.term_typ
  in
  let ty = encode_list.typ "" t.typ in
  Type_check.check t' ~ty;
  t', make_get_rtyp_list_of t





let make_list_eq typ =
  let f = Id.new_var ~name:"Primitive.list_eq" @@ pureTFun(Id.new_var ~name:"xs" @@ make_tlist typ, pureTFun(Id.new_var ~name:"xs" @@ make_tlist typ, Ty.bool)) in
  let xs = Id.new_var ~name:"xs'" @@ make_tlist typ in
  let ys = Id.new_var ~name:"ys'" @@ make_tlist typ in
  let t_eq =
    let pat_nil =
      let p1 = make_ppair (make_pnil ~elem_typ:typ) (make_pnil ~elem_typ:typ) in
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

let rec gen_eq (env_var,env_body as env) t1 t2 =
  match List.assoc_opt ~eq:Type.eq t1.typ env_var with
  | Some f -> env, [%term f `t1 `t2]
  | None ->
      match elim_tattr t1.typ with
      | TBase _ -> env, Term.(t1 = t2)
      | TTuple zs ->
          let x = Id.new_var ~name:"x" t1.typ in
          let y = Id.new_var ~name:"y" t2.typ in
          let env,ts =
            zs
            |> List.mapi (fun i _ -> [%term x ## i], [%term y ## i])
            |> List.fold_left_map (Fun.uncurry -| gen_eq) env
          in
          env, Term.(lets [x,t1; y,t2] (ands ts))
      | TConstr(c, [ty]) when c = C.list ->
          let f = Id.new_var ~name:"list_eq" Ty.(funs [list ty; list ty] bool) in
          let xs = Id.new_var ~name:"xs" (Ty.list ty) in
          let ys = Id.new_var ~name:"ys" (Ty.list ty) in
          let x = Id.new_var ~name:"x" ty in
          let y = Id.new_var ~name:"y" ty in
          let xs' = Id.new_var ~name:"xs'" (Ty.list ty) in
          let ys' = Id.new_var ~name:"ys'" (Ty.list ty) in
          let env_var = (t1.typ,f)::env_var in
          let env = env_var, env_body in
          let env,t_eq_xy = gen_eq env (Term.var x) (Term.var y) in
          let t_eq_xs'ys' = [%term f xs' ys'] in
          let t =
            let lty = Ty.list ty in
            let pty = Ty.(lty * lty) in
            [%term
                match xs, ys with
                | [] [@ty lty], [] [@ty lty] -> true
                | x::xs',       y::ys'       -> `t_eq_xy && `t_eq_xs'ys'
                | _ [@ty pty]                -> false]
          in
          let env_body = (t.typ, (f, [%term fun xs ys -> `t])) :: (snd env) in
          (fst env,env_body), [%term f `t1 `t2]
      | _ -> assert false

let inst_list_eq =
  let fld = Fold_tr.make () in
  let fld_desc env desc =
    match desc with
    | BinOp(Eq, t1, {desc=Nil})
    | BinOp(Eq, {desc=Nil}, t1) ->
        let env, t1' = fld.term env t1 in
        env, BinOp(Leq, Term.length t1', Term.int 0)
    | BinOp(Eq, ({typ=TConstr(c,_)} as t1), t2) when c = C.list ->
        let env,t1' = fld.term env t1 in
        let env,t2' = fld.term env t2 in
        let env,t = gen_eq env t1' t2' in
        env, t.desc
    | _ -> fld.desc_rec env desc
  in
  fld.desc <- fld_desc;
  fun t ->
    let (_,env_body),t' = fld.term ([],[]) t in
    let defs =
      let make =
        if !Flag.Abstract.list_eq then
          fun (ty,(eq,_)) ->
            Flag.Abstract.use "List equality";
            let x = Id.new_var ~name:"u" (Ty.list ty) in
            let y = Id.new_var ~name:"u" (Ty.list ty) in
            eq, [%term fun x y -> randb]
        else
          snd
      in
      List.map make env_body
    in
    make_let defs t'

let get_rtyp_list_opt _rtyp _typ = failwith "not implemented get_rtyp_list_opt"

let get_rtyp_list_of typed f rtyp =
  let typ = Trans.assoc_typ f typed in
  let rtyp' = get_rtyp_list_opt rtyp typ in
  if !!Flag.Debug.print_ref_typ
  then Format.fprintf !Flag.Print.target "LIST: %a: @[@[%a@]@ ==>@ @[%a@]@]@." Id.print f RT.print rtyp RT.print rtyp';
  rtyp'


let make_tl_opt n t =
  let x = Id.new_var ~name:"x" Ty.int in
  make_fun x (make_app t [make_add (make_var x) (make_int n)])


let encode_list_opt = Tr.make ()

let encode_list_opt_typ typ =
  match typ with
  | TVar(_,{contents=None},_) -> failwith "Polymorphic types occur! (Encode_list.encode_list_opt_typ)"
  | TConstr(c, [typ]) when c = C.list -> TFun(Id.new_var ~name:"i" Ty.int, opt_typ_enc @@ encode_list_opt.typ typ)
  | _ -> encode_list_opt.typ_rec typ

let rec get_match_bind_cond_opt t p =
  match p.pat_desc with
  | PAny -> [], true_term
  | PVar x -> [encode_list_opt.var x, t], true_term
  | PAlias(p,x) ->
      let bind,cond = get_match_bind_cond_opt t p in
      (encode_list_opt.var x, t)::bind, cond
  | PConst {desc=Const Unit} -> [], true_term
  | PConst t' -> [], make_eq t t'
  | PConstr _ -> assert false
  | PNil -> [], make_is_none_enc (make_app t [make_int 0])
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
      aux bind (make_and (make_is_some_enc (make_app t [make_int (len-1)])) cond) 0 ps
  | PTuple ps ->
      let binds,conds = List.split @@ List.mapi (fun i p -> get_match_bind_cond_opt (make_proj i t) p) ps in
      List.rev_flatten binds,
      List.fold_left make_and true_term conds
  | _ -> Format.eprintf "get_match_bind_cond_opt: %a@." Print.pattern p; assert false

let encode_list_opt_term t =
  let typ' = encode_list_opt.typ t.typ in
  match t.desc with
  | App({desc=Var x}, [t1; t2]) when Lid.to_string x = "List.nth" ->
      let t1' = encode_list_opt.term t1 in
      let t2' = encode_list_opt.term t2 in
      let t = make_app t1' [t2'] in
      let x = Id.new_var t.typ in
      make_let [x,t] @@ make_get_val @@ make_var x
  | Nil ->
      let el_typ = snd_typ @@ snd @@ ValE'._TFun typ' in
      make_fun (Id.new_var Ty.int) (make_none_enc el_typ)
  | Cons(t1,t2) ->
      let t1' = encode_list_opt.term t1 in
      let t2' = encode_list_opt.term t2 in
      let i = Id.new_var ~name:"i" Ty.int in
      let x = Id.new_var ~name:"x" t1'.typ in
      let xs = Id.new_var ~name:"xs" t2'.typ in
      let t11 = make_eq (make_var i) (make_int 0) in
      let t12 = make_some_enc (make_var x) in
      let t13 = make_app (make_var xs) [make_sub (make_var i) (make_int 1)] in
      if true
      then
        Term.(lets [x,t1'; xs,t2'] (fun_ i (if_ t11 t12 t13)))
      else
        let cns = Id.new_var ~name:"cons" (TFun(x,TFun(xs,t2'.typ))) in
        Term.(let_ [cns, funs [x;xs;i] (if_ t11 t12 t13)] (var cns @ [t1'; t2']))
  | Match(t1,pats) ->
      let x = Id.new_var ~name:"xs" (encode_list_opt.typ t1.typ) in
      let aux (p,t) t' =
        let bind,cond = get_match_bind_cond_opt (make_var x) p in
        make_if cond (add_bind bind (encode_list_opt.term t)) t'
      in
      let t_pats = List.fold_right aux pats (make_bottom typ') in
      make_let [x, encode_list_opt.term t1] t_pats
  | _ -> encode_list_opt.term_rec t

let () = encode_list_opt.typ <- encode_list_opt_typ
let () = encode_list_opt.term <- encode_list_opt_term

let trans_opt t =
  let t' = encode_list_opt.term t in
  let t' = Trans.inline_var_const t' in
(*
  let t' = Trans.subst_let_xy t' in
*)
  if false then Format.fprintf !Flag.Print.target "encode_list::@. @[%a@.@." Print.term t';
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
  |@> pr "decompose_match"
  |> Trans.lift_pwhen
  |@> pr "lift_pwhen"
  |> subst_matched_var
  |@> pr "subst_matched_var"
  |@> Type_check.check ~ty:t.typ
  |*> Trans.remove_por
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
    encode_list_opt.var x
  else
    encode_list.var "" x

let trans_typ typ =
  if !Flag.Encode.encode_list_opt then
    encode_list_opt.typ typ
  else
    encode_list.typ "" typ

let rec trans_rty ty =
  let open Ref_type in
  match ty with
  | Base(base,x,t) -> Base(base, x, fst @@ trans_term t)
  | Constr(_,_,_,_) -> [%unsupported]
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
  | Exn(ty1,ty2) -> Exn(trans_rty ty1, trans_rty ty2)
  | Variant _ -> assert false
  | Record _ -> assert false

let trans =
  let tr_env (x,ty) = x, trans_rty ty in
  Problem.map_on Focus.fst ~tr_env trans_term
