open Util
open Syntax
open Term_util
open Type

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type env = (string * (typ * bool * typ)) list
  (* string -- 's' of 'TData s'
     typ    -- type before encoding
     bool   -- whether recursive or not
     typ    -- type after encoding
   *)
let abst_recdata : env trans2 = make_trans2 ()

let make_ty ty_top ty_f =
  let open Flag.Encode.RecData in
  match !additional with
  | Nothing -> ty_f
  | Top -> Ty.(ty_top * ty_f)
  | Unit_top -> Ty.(tuple [unit; ty_top; ty_f])
let make_term top t_f =
  let open Flag.Encode.RecData in
  match !additional with
  | Nothing -> t_f
  | Top -> Term.(pair top t_f)
  | Unit_top -> Term.(tuple [unit; top; t_f])
let get_top_ty ty =
  let open Flag.Encode.RecData in
  match !additional with
  | Nothing -> ty
  | Top -> Type.fst_typ ty
  | Unit_top -> Type.proj_typ 1 ty
let get_element pos t_f =
  let open Flag.Encode.RecData in
  match !additional with
  | Nothing ->
      Term.(t_f @ [pos])
  | Top ->
      if pos.desc = Nil then
        Term.(fst t_f)
      else
        Term.(snd t_f @ [pos])
  | Unit_top ->
      if pos.desc = Nil then
        Term.(proj 1 t_f)
      else
        Term.(proj 2 t_f @ [pos])

(* Example:
     type tree = Leaf of int | Node of tree * tree
   i.e.,
     s = "tree",
     ty = TVariant(false, [ ("Leaf", int)
                          ; ("Node", TData "tree" * TData "tree")])
   is encoded into
     unit * ty_elem * (path:int list -> ty_elem)
   where
     ty_elem = Leaf of int | Node of () * ()
  *)
let encode_recdata_typ env s ty =
  match ty with
  | TVariant(false,labels) when List.mem s @@ get_tdata ty ->
      let ty =
        let aux ty =
          match ty with
          | TData s' when s' = s -> Ty.unit
          | _ when get_tdata ty = [] -> abst_recdata.tr2_typ env ty
          | _ -> unsupported "encode_variant: non-simple recursion"
        in
        TVariant(false, List.map (Pair.map_snd @@ List.map aux) labels)
      in
      make_ty ty Ty.(pfun ~name:"path" (list int) ty)
  | _ -> abst_recdata.tr2_typ env ty

let abst_recdata_typ env typ =
  match typ with
  | TRecord fields -> unsupported "abst_recdata_typ TRecord"
  | TAttr(attr, ty) ->
      let attr' = List.filter (function TARefPred _ -> false | _ -> true) attr in
      _TAttr attr' @@ abst_recdata.tr2_typ_rec env ty
  | _ -> abst_recdata.tr2_typ_rec env typ

let is_rec_type env ty =
  match elim_tattr ty with
  | TData s when not @@ List.mem s prim_base_types ->
      begin
        try Triple.snd @@ List.assoc s env
        with Not_found -> assert false
      end
  | _ -> false

let expand_typ env ty =
  match ty with
  | TData s when not @@ List.mem s prim_base_types ->
      begin
        try Triple.fst @@ List.assoc s env
        with Not_found -> assert false
      end
  | _ -> ty

let expand_enc_typ env ty =
  match ty with
  | TData s when not @@ List.mem s prim_base_types ->
      begin
        try Triple.trd @@ List.assoc s env
        with Not_found -> assert false
      end
  | _ -> ty
let expand_enc_typ_term env t = {t with typ = expand_enc_typ env t.typ}

let term_of_path xs =
  make_list ~typ:Ty.int @@ List.map Term.int xs

let rec abst_recdata_pat_rec env x path p0 =
  match p0.pat_desc with
  | PConstr(c,ps) ->
      let aux i p =
        if p0.pat_typ = p.pat_typ then
          let path' = i::path in
          let p',bind = abst_recdata_pat_rec env x path p in
          let t =
            let top = get_element (term_of_path path') x in
            let j = Id.new_var ~name:"path" Ty.(list int) in
            Term.(make_term top (pfun j (get_element (cons (int i) (var j)) x)))
          in
          Pat.__ Ty.unit, (t,p')::bind
        else
          abst_recdata_pat env p
      in
      let ps',binds = List.split @@ List.mapi aux ps in
      let pat_typ = get_top_ty @@ expand_enc_typ env @@ abst_recdata.tr2_typ env p0.pat_typ in
      {pat_desc=PConstr(c,ps'); pat_typ}, List.flatten binds
  | _ ->
      abst_recdata_pat env p0

and abst_recdata_pat env p =
  let pat_typ =
    match abst_recdata.tr2_typ env p.pat_typ with
    | TData s when not @@ List.mem s prim_base_types ->
        assert (List.mem_assoc s env);
        Triple.trd @@ List.assoc s env
    | typ -> typ
  in
  let pat_desc,bind =
    match p.pat_desc with
    | PAny -> PAny, []
    | PNondet -> PNondet, []
    | PVar x -> PVar (abst_recdata.tr2_var env x), []
    | PAlias(p,x) ->
        let p',bind = abst_recdata_pat env p in
        PAlias(p', abst_recdata.tr2_var env x), bind
    | PConst t -> PConst t, []
    | PConstr(c,ps) when is_rec_type env p.pat_typ ->
        let x = Id.new_var pat_typ in
        let p',bind = abst_recdata_pat_rec env (Term.var x) [] p in
        let t = get_element (term_of_path []) (Term.var x) in
        PVar x, (t,p')::bind
    | PConstr(c,ps) ->
        let ps',binds = List.split_map (abst_recdata_pat env) ps in
        PConstr(c,ps'), List.flatten binds
    | PNil -> PNil, []
    | PCons(p1,p2) ->
        let p1',bind1 = abst_recdata_pat env p1 in
        let p2',bind2 = abst_recdata_pat env p2 in
        PCons(p1',p2'), bind1@bind2
    | PRecord fields ->
        let fields',binds =
          let aux (s,p) =
            let p',bind = abst_recdata_pat env p in
            (s,p'), bind
          in
          List.split_map aux fields
        in
        PRecord fields', List.flatten binds
    | POr(p1,p2) ->
        let p1',bind1 = abst_recdata_pat env p1 in
        let p2',bind2 = abst_recdata_pat env p2 in
        if bind1 <> [] || bind2 <> [] then unsupported "POr";
        POr(p1', p2'), []
    | PTuple ps ->
        let ps',binds = List.split_map (abst_recdata_pat env) ps in
        PTuple ps', List.flatten binds
    | PNone -> PNone, []
    | PSome p ->
        let p',bind = abst_recdata_pat env p in
        PSome p', bind
    | PWhen(p, cond) ->
        let cond' = abst_recdata.tr2_term env cond in
        let p',bind = abst_recdata_pat env p in
        PWhen(p', cond'), bind
  in
  {pat_desc; pat_typ}, bind

let abst_recdata_term_rec env x_top path t =
  let ty_orig = t.typ in
  let bind,t_no_effect =
    let tr = make_tr_col2 [] (@) in
    let tr_term _ t =
      if has_no_effect t then
        [], t
      else
        match t.desc with
        | Constr(s,ts) ->
            let binds,ts' = List.split_map (tr.tr_col2_term ()) ts in
            let desc = Constr(s,ts) in
            List.flatten binds, {t with desc}
        | _ ->
            let t' = abst_recdata.tr2_term env t in
            let x = new_var_of_term t' in
            [x, t'], Term.var x
    in
    tr.tr_col2_term <- tr_term;
    tr.tr_col2_term () t
  in
  let paths =
    let rec aux ix t1 =
      if ty_orig <> t1.typ then
        []
      else
        match t1.desc with
        | Constr(s,ts) ->
            (ix, None) :: List.flatten_mapi (fun i t -> aux (i::ix) t) ts
        | _ ->
            let tl = Id.new_var Ty.(list int) in
            [ix, Some tl]
    in
    aux [] t_no_effect
  in
  let rec proj ix tail t1 =
    if ty_orig <> t1.typ then
      abst_recdata.tr2_term env t1
    else
      match ix, t1.desc with
      | [], Constr(s1,ts1) ->
          let ts1' =
            let aux t2 =
              if ty_orig = t2.typ then
                Term.unit
              else
                abst_recdata.tr2_term env t2
            in
            List.map aux ts1
          in
          let typ = get_top_ty @@ expand_enc_typ env @@ abst_recdata.tr2_typ env t1.typ in
          {desc=Constr(s1, ts1'); typ; attr=[]}
      | [], _ ->
          let t1' = expand_enc_typ_term env @@ abst_recdata.tr2_term env t1 in
          let tl = Option.get tail in
          get_element (Term.var tl) t1'
      | i::ix', Constr(s1,ts1) ->
          proj ix' tail (List.nth ts1 i)
      | _ -> assert false
  in
  let proj' (ix,tail) t1 =
    if ix = [] then
      Term.var x_top
    else
      proj ix tail t1
  in
  let pat_of_path (ix,tail) =
    let tl =
      match tail with
      | None -> Pat.nil Ty.int
      | Some tl -> Pat.var tl
    in
    List.fold_right Pat.cons (List.map Pat.int ix) tl
  in
  let pats = List.map (fun path -> pat_of_path path, proj' path t_no_effect) paths in
  let top = proj [] None t_no_effect in
  bind@[x_top,top], pats

let abst_recdata_term (env: env) t =
  let typ = elim_tattr t.typ in
  match t.desc with
  | Constr _ when is_rec_type env typ ->
      let x_top = Id.new_var (get_top_ty @@ expand_enc_typ env @@ abst_recdata.tr2_typ env t.typ) in
      let path = Id.new_var Ty.(list int) in
      let bind,pats = abst_recdata_term_rec env x_top path t in
      Term.(lets bind (make_term (var x_top) (pfun path (match_ (var path) pats))))
  | Match(t1,pats) ->
      let x = new_var_of_term t1 in
      let t1' = abst_recdata.tr2_term env t1 in
      let aux (p,t) t_acc =
        let t_acc' =
          let p',bind = abst_recdata_pat env p in
          let t' = abst_recdata.tr2_term env t in
          let pat_acc =
            match t_acc with
            | None -> []
            | Some t -> [Pat.(__ t'.typ), t]
          in
          if bind = [] then
            Term.(match_ (var x) ((p',t')::pat_acc))
          else
            let ts,ps = List.split bind in
            let tp = Term.tuple ts in
            let pp = Pat.tuple ps in
            match p'.pat_desc with
            | PVar y ->
                subst_var y x @@ Term.(match_ tp ((pp,t')::pat_acc))
            | _ ->
                let cond = Term.(match_ tp [pp, Term.true_; Pat.(__ pp.pat_typ), Term.false_]) in
                let t'' = Term.(match_ tp [pp, t']) in
                Term.(match_ (var x) ((Pat.when_ p' cond, t'')::pat_acc))
        in
        Some t_acc'
      in
      make_let [x,t1'] @@ Option.get @@ List.fold_right aux pats None
  | Local(Decl_type [s,ty], t) ->
      let ty' = encode_recdata_typ env s ty in
      let env' = (s, (ty, List.mem s @@ get_tdata ty, ty')) :: env in
      subst_tdata s ty' @@ abst_recdata.tr2_term env' t
  | Local(Decl_type decls, t1) ->
      (* TODO *)
      unsupported "encode_rec: Decl_type"
  | _ -> abst_recdata.tr2_term_rec env t

let () =
  abst_recdata.tr2_term <- abst_recdata_term;
  abst_recdata.tr2_typ <- abst_recdata_typ

let pr s t = Debug.printf "##[encode_rec] %a:@.%a@.@." Color.s_red s Print.term_typ t
let pr' s t = Debug.printf "##[encode_rec] %a:@.%a@.@." Color.s_red s Print.term' t

let trans_typ = abst_recdata.tr2_typ []
let trans_term t =
  let ty = trans_typ t.typ in
  t
  |@> pr "input"
  |> Trans.abst_ext_recdata
  |@> pr "abst_ext_rec"
  |@> Type_check.check ~ty
  |> abst_recdata.tr2_term []
  |@> pr "abst_rec"
  |@> pr' "abst_rec with type"
  |@> Type_check.check ~ty
  |> Trans.simplify_match
  |> Trans.reconstruct
  |> Trans.inline_var
  |> Trans.elim_singleton_tuple
  |@> pr "simplify1"
  |> Trans.inline_var
  |@> pr "simplify3"
  |> Trans.inst_randval
  |@> pr "inst_randval"
  |@> Type_check.check ~ty

(******************************************************************************
 * Encode in refinement type enviroment
 ******************************************************************************)

let gather_env : Syntax.term -> env =
  let rec go env t = match t.desc with
    | Local(Decl_type [s,ty], t) ->
        let ty' = encode_recdata_typ env s ty in
        let env' = (s, (ty, List.mem s @@ get_tdata ty, ty')) :: env in
        go env' t
    (*| Local(_, t) -> go env t*) (* can be ignored because of Preprocess.Lift_type_decl *)
    | _ -> env
  in
    go []

let subst_all_tdata : env -> _ =
  subst_tdata_map -| List.map (Pair.map_snd Triple.trd)

type sym_env = (string * (term * (int, term) Map.t)) list

let trans_pred =
  let tr = make_trans2 () in
  let term (x, sym_env) t =
    match t.desc with
    | Match({desc=Var(y)}, ps) when Id.(x=y) ->
        let labels = List.map fst sym_env in
        let preds =
          snd @@ List.Labels.fold_right ps ~init:(labels,[]) ~f:(
            fun (p, t) (remain, arms) ->
              match p.pat_desc with
              | PConstr(c, ps) when not (List.mem c remain) ->
                  (* already matched (would it be better to raise an error?) *)
                  (remain, List.snoc arms false_term)
              | PConstr(c, ps) ->
                  let is_c, map = try List.assoc c sym_env with _ -> assert false in
                  let remain' = List.remove remain c in
                  let sbst = List.Labels.filter_map (List.mapi Pair.pair ps) ~f:(
                    fun (j, p) ->
                      match p.pat_desc with
                      | PAny -> None
                      | PVar(x) -> (try Some (x, Map.find j map)
                                    with Not_found -> None)
                          (* TODO assert x is not in FV(t) when Not_found *)
                      | _ -> assert false
                  ) in
                  let t' = subst_map sbst t in
                  (remain', List.snoc arms (make_and is_c t'))
              | PVar(y) ->
                  let match_ = make_ors @@
                    try List.Labels.map (fun l -> fst @@ List.assoc l sym_env) remain
                    with Not_found -> assert false
                  in
                  let t' = subst y (make_var x) t in
                  ([], List.snoc arms (make_and match_ t'))
              | PAny ->
                  let match_ = make_ors @@
                    try List.Labels.map (fun l -> fst @@ List.assoc l sym_env) remain
                    with Not_found -> assert false
                  in
                  ([], List.snoc arms (make_and match_ t))
              | _ -> assert false
          )
        in make_ors preds
    | _ -> tr.tr2_term_rec (x,sym_env) t
  in
  tr.tr2_term <- term;
  term

(* e.g.1:
      type foo = Foo of (int * string) | Bar of (bool * int)
        => foo = ((bool * (int * string)) * (bool * (bool * int))) * unit
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
      [ Foo, ([int, string], [int, string]);
        Bar, ([int, string], [int, string]);
      ]
  e.g.2:
      type tree = Leaf of int | Node of tree * int * bool * tree
        => tree = unit * (int list -> ((bool * (int)) * (bool * (int * bool))) * unit)
                                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
      [ Leaf, ([int], [int]);
        Node, ([tree, int, bool, tree], [int, bool]);
      ]
*)
type lts = (string * (typ list * typ list)) list

let mk_sym_env s t (lts:lts) =
  List.Labels.mapi lts ~f:(
    fun i (l,(tys,tys')) ->
      let t_base = Term.(proj i t) in
      let is_l = Term.(fst t_base) in
      let map : (int, term) Map.t =
        (* i: index in tys
           j: index in tys' *)
        let rec go m i j tys tys' =
          match tys, tys' with
          | _, [] -> m
          | ty::tys, _ when ty = TData s ->
              go m (i+1) j tys tys'
          | _::tys, ty'::tys' ->
              let m' = Map.add i Term.(proj j (snd t_base)) m in
              go m' (i+1) (j+1) tys tys'
          | _ -> assert false
        in go Map.empty 0 0 tys tys'
      in
      (l, (is_l, map))
  )

let trans_rty_rec_data (s,x,t) (ty_before: typ) (ty_after: typ) =
  begin match ty_before, ty_after with
  | TVariant(false,ts), TTuple([{Id.typ=ty1};{Id.typ=ty2}]) ->
      assert (ty1 = Ty.unit);
      (* ty_after should is the form of [unit * (int list -> t_variant * unit)]
         where t_variant = (bool * _) * (bool * _) * ...
      *)
      let t_variant =
        let arg, ret_ty = decomp_tfun ty2 in
        assert (List.length arg = 1 && Id.typ (List.hd arg) = Ty.(list int));
        match decomp_ttuple ret_ty with
        | [t_variant; t_unit] -> assert (t_unit = Ty.unit); t_variant
        | _ -> assert false
      in
      let v = Id.new_var t_variant in
      let lts = List.Labels.map2 ts (decomp_ttuple t_variant) ~f:(
        fun (l,tys) x -> (l,(tys, decomp_ttuple (snd_typ x)))
      ) in
      let sym_env : sym_env= mk_sym_env s (make_var v) lts in
      let path = Id.new_var ~name:"path" Ty.(list int) in
      let u = Id.new_var Ty.unit in
      let t' = Term.(var path <> nil Ty.int || trans_pred (x,sym_env) t) in
      Type_check.check ~ty:Ty.bool t';
      let rty =
        Ref_type.(Tuple(
          [ v, of_simple t_variant;
            u, Base(TUnit, u, t')
          ]))
      in
      let x = Ref_type.Fun(path, Ref_type.of_simple Ty.(list int), rty) in
      unsupported "Encode_rec.trans_rty_rec_data";
      Ref_type.Ty.(tuple [unit(); x])
  | _ -> assert false
  end

let trans_rty_nonrec_data (s,x,t) (ty_before: typ) (ty_after: typ) =
  match ty_before, ty_after with
  | TVariant(false,ts), TTuple([{Id.typ=ty1};{Id.typ=ty2}]) ->
      let xs = match ty1 with TTuple(xs) -> xs | _ -> assert false in
      assert (ty2 = Ty.unit);
      let v = Id.new_var ty1 in
      let lts = List.Labels.map2 ts xs ~f:(
        fun (l,tys) x -> (l,(tys, decomp_ttuple (snd_typ @@ Id.typ x)))
      ) in
      let sym_env = mk_sym_env s (make_var v) lts in
      let u = Id.new_var Ty.unit in
      let t' = trans_pred (x,sym_env) t in
      Type_check.check ~ty:Ty.bool t';
      Ref_type.(Tuple(
        [ v, of_simple ty1;
          u, Base(TUnit, u, t')
        ]))
  | _, _ -> assert false

let rec trans_rty env =
  let tr = make_trans() in
  tr.tr_typ <- expand_enc_typ env;
  let open Ref_type in
  function
  | ADT(s,x,t) ->
      let ty_before = expand_typ env (TData s) in
      let ty_after = expand_enc_typ env (TData s) in
      if is_rec_type env (TData s)
      then trans_rty_rec_data (s,x,t) ty_before ty_after
      else trans_rty_nonrec_data (s,x,t) ty_before ty_after
  | Base(base,x,t) -> Base(base, tr.tr_var x, tr.tr_term t)
  | Fun(x,ty1,ty2) -> Fun(tr.tr_var x, trans_rty env ty1, trans_rty env ty2)
  | Tuple xtys -> Tuple(List.map (Pair.map tr.tr_var (trans_rty env)) xtys)
  | Inter(sty,tys) -> Inter(tr.tr_typ sty, List.map (trans_rty env) tys)
  | Union(sty,tys) -> Union(tr.tr_typ sty, List.map (trans_rty env) tys)
  | ExtArg(x,ty1,ty2) -> ExtArg(tr.tr_var x, trans_rty env ty1, trans_rty env ty2)
  | List(x,p_len,y,p_i,ty2) -> List(tr.tr_var x,
                                    tr.tr_term p_len,
                                    tr.tr_var y,
                                    tr.tr_term p_i,
                                    trans_rty env ty2)
  | App _ -> unsupported "Encode_rec_variant.trans_rty: App"
  | Exn(ty1,ty2) -> Exn(trans_rty env ty1, trans_rty env ty2)

let trans_rid = abst_recdata.tr2_var

let trans_env : env -> (Syntax.id * Ref_type.t) list -> (Syntax.id * Ref_type.t) list = fun env renv ->
  List.map (Pair.map (trans_rid env) (trans_rty env)) renv

(* TODO: support records in refinement types *)
let trans p =
  let env = gather_env @@ Problem.term p in
  let p = Problem.map ~tr_env:(trans_env env) trans_term p in
  let t = Problem.(p.term) in
  Type_check.check t ~ty:t.typ;
  p
