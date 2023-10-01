open Util
open Type
open Syntax
open Type_util
open Term_util

module Dbg_ty = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".ty") end)
module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ ||| Dbg_ty.check end)

type env = (constr * (typ * bool * typ)) list
  (* constr -- 's' of 'TConstr(s, ...)'
     typ    -- type before encoding
     bool   -- whether recursive or not
     typ    -- type after encoding
   *)

let abst_recdata : env Tr2.t = Tr2.make ()

let make_ty ty_top ty_f =
  let open Flag.Encode.RecData in
  match !additional with
  | Nothing -> ty_f
  | Top ->
      if !share_predicate then
        let ty_top1,ty_top2 = copy_for_pred_share true ty_top in
        let ty_f' =
          match ty_f with
          | TAttr([TAPureFun], TFun(path, ty_top')) ->
              assert (ty_top = ty_top');
              TAttr([TAPureFun], TFun(path, ty_top2))
          | _ -> assert false
        in
        Ty.tuple [ty_top1; ty_f']
      else
        Ty.tuple [ty_top; ty_f]
  | Unit_top -> unsupported "Flag.Encode.RecData.Unit_top"
let make_term top t_f =
  let open Flag.Encode.RecData in
  match !additional with
  | Nothing -> t_f
  | Top -> Term.(pair top t_f)
  | Unit_top -> unsupported "Flag.Encode.RecData.Unit_top"
let get_elem_ty ty =
  let open Flag.Encode.RecData in
  match !additional with
  | Nothing -> ty
  | Top -> fst_typ ty
  | Unit_top -> unsupported "Flag.Encode.RecData.Unit_top"
let get_elem pos f =
  let t =
    let open Flag.Encode.RecData in
    match !additional, pos.desc with
    | Nothing, _ -> Term.(var f @ [pos])
    | Top, Nil -> Term.(fst (var f))
    | Top, _ -> Term.(snd (var f) @ [pos])
    | Unit_top, _ -> unsupported "Flag.Encode.RecData.Unit_top"
  in
  let r = new_var_of_term t in
  let num = List.length (decomp_ttuple t.typ) in
  let ns = List.fromto 0 num in
  let proj' i = Term.(fst (proj i (var r))) in
  let cond1 =
    let indices =
      Combination.product ns ns
      |> List.filter (Fun.uncurry (<))
    in
    Term.ands @@ List.map Term.(fun (i,j) -> not (proj' i && proj' j)) indices
  in
  let cond2 = Term.ors @@ List.map proj' ns in
  Term.(let_ [r, t]
       (assume (cond1 && cond2)
       (var r)))


let check_row_ret row = if row.row_ret <> None then unsupported "%s GADT" __MODULE__

(** [encode_recdata_typ] translates recursive type definitions *)
(* Example for Flag.Encode.RecData.Top:
     type tree = Leaf of int | Node of tree * tree
   i.e.,
     s = "tree",
     ty = TVariant(false, [ ("Leaf", int)
                          ; ("Node", TData "tree" * TData "tree")])
   is encoded into
     ty_elem * (path:int list -> ty_elem)
   where
     ty_elem = bool * (int * )
  *)
let encode_recdata_typ env (s:Type.constr) ty =
  match ty with
  | TVariant(VPoly _, _) -> invalid_arg "%s" __FUNCTION__
  | TVariant(VNonPoly,rows) when List.mem_assoc ~eq:Path.eq (LId s) @@ get_tconstr_typ ty ->
      let ty_elem =
        rows
        |> List.map (fun row ->
               check_row_ret row;
               let tys =
                 row.row_args
                 |> List.filter_map (function
                        | TConstr(s',_) when Path.(s' = LId s) -> None
                        | ty' ->
                            if List.mem_assoc ~eq:Path.eq (Type.LId s) (get_tconstr_typ ty') then
                              let () = Flag.Debug.print "ty: %a@." Print.typ ty in
                              let () = Flag.Debug.print "ty': %a@." Print.typ ty' in
                              unsupported "%s: non-simple recursion (use -data-to-int, -ignore-data-arg, etc.)" __MODULE__
                            else
                              Some (abst_recdata.typ env ty'))
               in
               Ty.(bool * tuple tys))
        |> Ty.tuple
      in
      make_ty ty_elem Ty.(pfun ~name:"path" (list int) ty_elem)
  | _ -> abst_recdata.typ env ty

(** [abst_recdata_typ] translates non-recursive type definitions *)
(* e.g.
     type foo = Foo of int | Bar of bool * string
       => (bool * (int)) * (bool * (bool * string))
                  ^^^^^ single element tuple
*)
let abst_recdata_typ env typ =
  match typ with
  | TConstr(LId s, []) ->
      begin match Id.List.assoc_opt s env with
      | None -> typ
      | Some (_, _, ty) -> ty
      end
  | TRecord _fields -> unsupported "abst_recdata_typ TRecord"
  | TVariant(VPoly _, _) -> invalid_arg "%s" __FUNCTION__
  | TVariant(VNonPoly,rows) ->
      let aux row =
        check_row_ret row;
        Ty.(bool * tuple (List.map (abst_recdata.typ env) row.row_args))
      in
      Ty.(tuple (List.map aux rows))
  | TAttr(attr, ty) ->
      let attr' = List.filter (function TARefPred _ | TARaise _ -> false | _ -> true) attr in
      _TAttr attr' @@ abst_recdata.typ_rec env ty
  | _ -> abst_recdata.typ_rec env typ

let is_rec_type env ty =
  match elim_tattr ty with
  | TConstr(LId s,_) when not (is_prim_constr (LId s)) ->
      begin
        try Triple.snd @@ Id.List.assoc s env
        with Not_found -> assert false
      end
  | _ -> false

let expand_typ env ty =
  match ty with
  | TConstr(LId s,_) when not (is_prim_constr (LId s)) ->
      begin
        try Triple.fst @@ Id.List.assoc s env
        with Not_found -> assert false
      end
  | _ -> ty

let expand_enc_typ env ty =
  match ty with
  | TConstr(LId s, _) when not (is_prim_constr (LId s)) ->
      begin
        try Triple.trd @@ Id.List.assoc s env
        with Not_found -> assert false
      end
  | _ -> ty

let make_add_bind bind =
  List.fold_right (fun (t,p) t' -> Term.match_ t [p, t']) bind

let get_c ty =
  ty
  |> Val'._TConstr
  |> Option.map fst

let rec abst_recdata_pat env p =
  let path = get_c p.pat_typ in
  let typ = abst_recdata.typ env p.pat_typ in
  let desc,cond,bind =
    match p.pat_desc with
    | PAny -> PAny, true_term, []
    | PNondet -> PNondet, true_term, []
    | PVar x -> PVar (abst_recdata.var env x), true_term, []
    | PAlias(p,x) ->
        let p',cond,bind = abst_recdata_pat env p in
        PAlias(p', abst_recdata.var env x), cond, bind
    | PConst t -> PConst t, true_term, []
    | PConstr(true,_,_) -> unsupported "%s (poly)" __MODULE__
    | PConstr(false, LId c, ps) when not (is_rec_type env p.pat_typ) ->
        let p', cond, bind =
          let ps,cond,bind =
            List.L.fold_right ps
              ~init:([],true_term,[])
              ~f:(fun p (ps, cond, bind) ->
                  let p', cond', bind' = abst_recdata_pat env p in
                  p'::ps, Term.(cond' && cond), bind'@bind)
          in
          Pat.tuple ps, cond, bind
        in
        let ps' =
          expand_typ env p.pat_typ
          |> ValE'._TVariant
          |> snd
          |> List.map (fun row ->
               check_row_ret row;
               if Id.(c = row.row_constr) then
                 Pat.(true_ * p')
               else
                 let ty = Ty.tuple @@ List.map (abst_recdata.typ env) row.row_args in
                 Pat.(false_ * __ ty))
        in
        PTuple ps', cond, bind
    | PConstr(false, LId c, ps) ->
        let f = Id.new_var typ in
        (* [c] is [constr_ix]-th constructor of type TConstr s *)
        let constr_ix,_ =
          expand_typ env p.pat_typ
          |> ValE'._TVariant
          |> snd
          |> assoc_row_with_pos ~sort:false c
        in
        Dbg.printf "p: %a@." Print.pattern p;
        Dbg.printf "p.pat_type: %a@." Print.typ p.pat_typ;
        Dbg.printf "f: %a@." Print.id_typ f;
        let pcbs = List.map (abst_recdata_pat env) ps in

        let binds,_,_ =
          (* i: index of non-recursive types
             j: index of recursive types
             e.g.,
                type tree = Node of tree * int * tree * int
                                    _      0     _       1   <- i
                                    0      _     1       _   <- j
                match t: tree with
                | Node(p1,p2,p3,p4) as p -> ...
              =>
                p1 path = top, snd p (0::path)
                p2      = proj 0 @@ snd @@ proj constr_ix @@ fst @@ snd p []
                p3 path = top, snd p (1::path)
                p4      = proj 1 @@ snd @@ proj constr_ix @@ fst @@ snd p []

             TODO refactor
           *)
          let make_bind (acc,i,j) p (p',_,_) =
            let i',j',t' =
              if Eq.(option ~eq:path) path (get_c p.pat_typ) then
                let () = Dbg.printf "%a has rec type %a@." Print.pattern p Print.typ p.pat_typ in
                let path = Id.new_var ~name:"path" Ty.(list int) in
                let top = Term.(get_elem (cons (int j) (nil ~elem_typ:Ty.int)) f) in
                let t = make_term top Term.(pfun path (get_elem (cons (int j) (var path)) f)) in
                Dbg.printf "make_bind top: @[%a@." Print.term' top;
                Dbg.printf "make_bind t: @[%a@." Print.term' t;
                i, j+1, t
              else
                let () = Dbg.printf "%a has non-rec type %a@." Print.pattern p Print.typ p.pat_typ in
                let t = Term.(proj i (snd (proj constr_ix (get_elem (nil ~elem_typ:Ty.int) f)))) in
                i+1, j, t
            in
            List.snoc acc (t', p'), i', j'
          in
          List.fold_left2 make_bind ([],0,0) ps pcbs
        in
        Dbg.printf "binds = %a@."
          Print.(list (
            fun fm (x,p) ->
              triple pattern typ term fm (p, x.typ, x)
          ))
          binds;
        let cond =
          let cond0 = Term.(fst (proj constr_ix (get_elem (nil ~elem_typ:Ty.int) f))) in
          let conds' =
            let make_cond (t,pt) (p,cond,_) =
              match pt.pat_desc with
              | PAny
              | PVar _ -> cond
              | _ ->
                  Term.match_ t
                    [pt, cond;
                     Pat.__ p.pat_typ, Term.false_]
            in
            List.map2 make_cond binds pcbs
          in
          Term.ands (cond0 :: conds')
        in
        Dbg.printf "cond: %a@." Print.term cond;
        let bind = binds @ List.flatten_map Triple.trd pcbs in
        PVar f, cond, bind
    | PConstr(_, _, _) -> assert false
    | PNil -> PNil, true_term, []
    | PCons(p1,p2) ->
        let p1',cond1,bind1 = abst_recdata_pat env p1 in
        let p2',cond2,bind2 = abst_recdata_pat env p2 in
        PCons(p1',p2'), make_and cond1 cond2, bind1@bind2
    | PRecord fields ->
        let aux (_,p) (ps, cond, bind) =
          let p', cond', bind' = abst_recdata_pat env p in
          p'::ps, make_and cond' cond, bind'@bind
        in
        let ps,cond,bind = List.fold_right aux fields ([],true_term,[]) in
        PTuple ps, cond, bind
    | POr({pat_desc=PConst _},_)
    | POr(_,{pat_desc=PConst _}) -> p.pat_desc, true_term, []
    | POr(p1,p2) ->
        let p1',cond1,bind1 = abst_recdata_pat env p1 in
        let p2',cond2,bind2 = abst_recdata_pat env p2 in
        if bind2 <> [] then unsupported "Encode_rec POr";
        let get_bind_map p1' p2' =
          match p1'.pat_desc, p2'.pat_desc with
          | PVar x1, PVar x2 -> [x2, x1]
          | PTuple _, PTuple _ ->
              Format.eprintf"%a,%a@." Print.pattern p1' Print.pattern p2';
              unsupported "POr1"
          | _ ->
              Format.eprintf"%a,%a@." Print.pattern p1' Print.pattern p2';
              unsupported "POr2"
        in
        let map = get_bind_map p1' p2' in
        let cond2' = List.fold_right (Fun.uncurry subst_var) map cond2 in
        p1'.pat_desc, make_or cond1 cond2', bind1
    | PTuple ps ->
        let aux p (ps,cond,bind) =
          let p',cond',bind' = abst_recdata_pat env p in
          p'::ps, make_and cond' cond, bind' @ bind
        in
        let ps',cond,bind = List.fold_right aux ps ([],true_term,[]) in
        PTuple ps', cond, bind
    | PNone -> PNone, true_term, []
    | PSome p ->
        let p',cond,bind = abst_recdata_pat env p in
        PSome p', cond, bind
    | PWhen(p,c) ->
        let p',cond,bind = abst_recdata_pat env p in
        let c' = make_add_bind bind @@ abst_recdata.term env c in
        p'.pat_desc, Term.(c' && cond), bind
    | PLazy p ->
        let p',cond,bind = abst_recdata_pat env p in
        PLazy p', cond, bind
    | PEval _ -> assert false
  in
  make_pattern desc typ,
  cond,
  bind


let abst_recdata_term (env: env) t =
  let typ = elim_tattr t.typ in
  match t.desc with
  | Constr(true,_,_) -> unsupported "encode_rec: polymorphic variant"
  | Constr(false, LId c, ts) when not (is_rec_type env typ) ->
      let aux row =
        check_row_ret row;
        if Id.(c = row.row_constr) then
          let t = Term.tuple @@ List.map (abst_recdata.term env) ts in
          [%term true, `t]
        else
          let t =
            List.map (abst_recdata.typ env) row.row_args
            |> Ty.tuple
            |> Term.rand
          in
          [%term false, `t]
      in
      let ts' = List.map aux @@ snd @@ ValE'._TVariant @@ expand_typ env typ in
      Term.tuple ts'
  | Constr(false, LId c, ts) ->
      let ts' = List.map (abst_recdata.term env) ts in
      let xtys = List.map2 (fun t' t -> Id.new_var @@ expand_enc_typ env t'.typ, t.typ) ts' ts in
      let _,rows = ValE'._TVariant @@ expand_typ env typ in
      let path = Id.new_var ~name:"path" Ty.(list int) in
      let top =
        let make_return ts' =
          rows
          |> List.map (fun row ->
                 check_row_ret row;
                 if Id.(c = row.row_constr) then
                   Term.(pair true_ (tuple ts'))
                 else
                   let tys' = List.filter_out (Type.eq typ) row.row_args in
                   let ty = make_ttuple @@ List.map (abst_recdata.typ env) tys' in
                   Term.(pair false_ (rand ty)))
          |> Term.tuple
        in
        List.combine ts xtys
        |> List.filter_out (fun (t',_) -> Type.eq typ t'.typ)
        |> List.map (snd |- fst |- make_var)
        |> make_return
      in
      let pat0 = Pat.nil ~elem_typ:Ty.int, top in
      let make_pat (i,acc) (x,ty) =
        if Type.eq ty typ then
          let path' = Id.new_var ~name:"path'" Ty.(list int) in
          let t = get_elem (Term.var path') x in
          i+1, acc @ [Pat.(cons (int i) (var path')), t]
        else
          i, acc
      in
      let _,pats = List.fold_left make_pat (0,[]) xtys in
      let defs = List.map2 (fun (x,_) t -> x, t) xtys ts' in
      Term.(lets defs (make_term top (pfun path (match_ (var path) (pat0::pats)))))
  | Match(t1,pats) ->
      let t1' = abst_recdata.term env t1 in
      let pats' =
        List.L.map pats ~f:(fun (p,t) ->
          let p',c,bind = abst_recdata_pat env p in
          let t' = abst_recdata.term env t in
          let add_bind = make_add_bind bind in
          Pat.when_ p' (add_bind c),
          add_bind t')
      in
      Term.match_ t1' pats'
  | Record [] -> assert false
  | Record fields ->
      if List.exists (fun (_,(f,_)) -> f = Mutable) @@ ValE'._TRecord typ
      then unsupported "Mutable records"
      else Term.tuple @@ List.map (abst_recdata.term env -| snd) fields
  | Field(t,s) ->
      let fields = ValE'._TRecord typ in
      begin match Id.List.assoc_opt s fields with
      | None -> assert false
      | Some (Mutable, _) -> unsupported "Mutable records"
      | _ -> Term.proj (List.find_pos (fun _ (s',_) -> Id.(s = s')) fields) @@ abst_recdata.term env t
      end
  | SetField _ -> assert false
  | Local(Decl_type [s,(params,ty)], t) ->
      if params <> [] then unsupported "Encode_rec";
      let ty' = encode_recdata_typ env s ty in
      Dbg.printf "s: %a@." Print.tconstr s;
      Dbg.printf "ty': %a@.@." Print.typ ty';
      let env' = (s, (ty, List.mem_assoc ~eq:Path.eq (Type.LId s) @@ get_tconstr_typ ty, ty')) :: env in
      subst_tconstr_with_copy s ([],ty') @@ abst_recdata.term env' t
  | Local(Decl_type _decls, _t1) ->
      Format.eprintf "ABST_RECDATA_TERM: %a@." Print.term t;
      (* TODO *)
      unsupported "encode_rec: Decl_type"
  | _ -> set_afv_shallowly @@ abst_recdata.term_rec env t

let () =
  abst_recdata.term <- abst_recdata_term;
  abst_recdata.typ <- abst_recdata_typ

let pr s t =
  let pr_term = if !!Dbg_ty.check then Print.term' else Print.term in
  Dbg.printf "##[encode_rec] %a:@.%a@.@." Color.s_red s pr_term t;
  if !!Dbg.check then Check.assert_check_afv t

let trans_typ = abst_recdata.typ []
let trans_term ?(check=true) t =
  let ty = trans_typ t.typ in
  t
  |@> pr "input"
  |> Trans.abst_ext_recdata
  |@> pr "abst_ext_rec"
  |@check&> Type_check.check ~ty:t.typ
  |> Trans.remove_por
  |> abst_recdata.term []
  |@> pr "abst_rec"
  |@check&> Type_check.check ~ty
  |> Trans.simplify_match
  |@> pr "simplify1.1"
  |> Trans.inline_var
  |@> pr "simplify1.2"
  |> Trans.elim_singleton_tuple
  |@> pr "simplify1.3"
  |> Trans.inline_var
  |@> pr "simplify2"
  |> Trans.lift_assume
  |> Trans.elim_unused_let
  |@> pr "simplify3"
  |> Trans.remove_obstacle_type_attribute_for_pred_share
  |@check&> Type_check.check ~ty

(******************************************************************************
 * Encode in refinement type enviroment
 ******************************************************************************)

let gather_env : Syntax.term -> env =
  let rec go env t = match t.desc with
    | Local(Decl_type [s,(params,ty)], t) ->
        if params <> [] then unsupported "Encode_rec";
        let ty' = encode_recdata_typ env s ty in
        let env' = (s, (ty, List.exists (fst |- Path.(=) (LId s)) @@ get_tconstr_typ ty, ty')) :: env in
        go env' t
    (*| Local(_, t) -> go env t*) (* can be ignored because of Preprocess.Lift_type_decl *)
    | _ -> env
  in
    go []

(*
type sym_env = (string * (term * (int, term) Map.t)) list
 *)

let trans_pred =
  let tr = Tr2.make () in
  let term (x, sym_env) t =
    match t.desc with
    | Match({desc=Var (LId y)}, pats) when Id.(x = y) ->
        let labels = List.map fst sym_env in
        let _,preds =
          List.Labels.fold_right pats ~init:(labels,[]) ~f:(
            fun (p, t) (remain, arms) ->
              match p.pat_desc with
              | PConstr(true,_,_) -> unsupported "encode_rec: polymorphic variant"
              | PConstr(false,LId c, _) when not (List.mem c remain) ->
                  (* already matched (would it be better to raise an error?) *)
                  (remain, List.snoc arms false_term)
              | PConstr(false, LId c, ps) ->
                  let is_c, map = try Id.List.assoc c sym_env with _ -> assert false in
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
                    try List.map (fun l -> fst @@ Id.List.assoc l sym_env) remain
                    with Not_found -> assert false
                  in
                  let t' = subst y (make_var x) t in
                  ([], List.snoc arms (make_and match_ t'))
              | PAny ->
                  let match_ = make_ors @@
                    try List.map (fun l -> fst @@ Id.List.assoc l sym_env) remain
                    with Not_found -> assert false
                  in
                  ([], List.snoc arms (make_and match_ t))
              | _ -> assert false
          )
        in make_ors preds
    | _ -> tr.term_rec (x,sym_env) t
  in
  tr.term <- term;
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
        => tree = unit * (int list -> ((bool * (int * )) * (bool * (int * bool))) * unit)
                                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
      [ Leaf, ([int], [int]);
        Node, ([tree, int, bool, tree], [int, bool]);
      ]
*)
type lts = (constr * (typ list * typ list)) list

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
          | TConstr(s',_)::tys, _ when Path.(s' = s) ->
              go m (i+1) j tys tys'
          | _::tys, _ty'::tys' ->
              let m' = Map.add i Term.(proj j (snd t_base)) m in
              go m' (i+1) (j+1) tys tys'
          | _ -> assert false
        in go Map.empty 0 0 tys tys'
      in
      (l, (is_l, map))
  )

let trans_rty_rec_data (_s,_x,_t) (_ty_before: typ) (_ty_after: typ) =
  unsupported "Encode_rec.trans_rty_rec_data"
(*
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
      Ref_type.Ty.(tuple [unit(); x])
  | _ -> assert false
  end
 *)

let trans_rty_nonrec_data (s,x,t) (ty_before: typ) (ty_after: typ) =
  match ty_before, ty_after with
  | TVariant(VNonPoly,rows), TTuple([{Id.typ=ty1};{Id.typ=ty2}]) ->
      let xs = match ty1 with TTuple(xs) -> xs | _ -> assert false in
      assert (ty2 = Ty.unit);
      let v = Id.new_var ty1 in
      let lts = List.L.map2 rows xs ~f:(fun row x ->
                    check_row_ret row;
                    (row.row_constr,(row.row_args, decomp_ttuple (snd_typ @@ Id.typ x)))
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

(* TODO: refine predicates *)
let make_trans_env {Problem.term} =
  let map =
    let declss,_ = split_type_decl_and_body term in
    let decls = List.flatten declss in
    let xs = List.map (fun (s,_) -> Id.new_var (TConstr(LId s,[]))) decls in
    let _,body =
      List.fold_right Term.type_ declss Term.(tuple (vars xs))
      |> trans_term ~check:false
      |> split_type_decl_and_body
    in
    match body.desc with
    | Tuple ts ->
        ts
        |> List.map (ValE._Var |- Lid.typ |- Ref_type.of_simple)
        |> List.combine (List.map fst decls)
    | Var x ->
        let s,_ = List.get decls in
        [s, Ref_type.of_simple @@ Lid.typ x]
    | _ -> assert false
  in
  let sbst =
    let f _ rty =
      match rty with
      | Ref_type.Constr(LId s,_,_,_) -> Id.List.assoc_opt s map
      | _ -> None
    in
    Ref_type.make_trans f
  in
  fun (x,rty) ->
    let rty' = sbst rty in
    Id.set_typ x (Ref_type.to_simple rty'),
    rty'


let trans p =
  let tr_env = make_trans_env p in
  let p = Problem.map ~tr_env trans_term p in
  let t = p.term in
  Type_check.check t ~ty:t.typ;
  p
