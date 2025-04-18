open Util
open Type
open Type_util
open Syntax
open Term_util

module Debug = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

let mutable_record_term =
  let tr = Tr2.make () in
  let rec assoc env ty =
    match ty with
    | TConstr (s, [ ty1 ]) when s = C.ref ->
        let label = label_of_string "contents" in
        [ (label, (Mutable, ty1)) ]
    | TConstr (s, tys) -> (
        try List.assoc ~eq:Path.eq s env |> apply_tconstr -$- tys |> assoc env
        with Not_found ->
          Format.eprintf "TConstr %a@." Print.path s;
          Format.eprintf "env: %a@." Print.(list (path * (list typ * typ))) env;
          assert false)
    | TRecord fields -> fields
    | _ -> assert false
  in
  tr.pat <-
    (fun env p ->
      match p.pat_desc with
      | PRecord fields ->
          let tfields = assoc env p.pat_typ in
          let aux (f, p) =
            match Id.List.assoc f tfields with
            | Immutable, _ -> (f, tr.pat env p)
            | Mutable, ty ->
                let p' = tr.pat env p in
                let ty' = tr.typ env ty in
                let x = Id.new_var (Ty.ref ty') in
                let p'' = Pat.eval x Term.(!(var x)) p' in
                (f, p'')
          in
          let fields' = List.map aux fields in
          let pat_typ = tr.typ env p.pat_typ in
          make_pattern (PRecord fields') pat_typ
      | _ -> tr.pat_rec env p);
  tr.term <-
    (fun env t ->
      match t.desc with
      | Record fields ->
          let tys = assoc env t.typ in
          let fields' =
            List.L.map2 fields tys ~f:(fun (s, t) (_, (f, _)) ->
                let t' = tr.term env t in
                (s, if f = Mutable then Term.ref t' else t'))
          in
          make_record fields' @@ tr.typ env t.typ
      | SetField (t1, s, t2) ->
          let t1' = tr.term env t1 in
          let t2' = tr.term env t2 in
          Term.(field ~ty:(Ty.ref t2'.typ) t1' s := t2')
      | Field (t1, s) ->
          let t1' = tr.term env t1 in
          let f, ty =
            try Id.List.assoc s @@ assoc env t1.typ
            with Not_found ->
              Format.eprintf "t: %a@." Print.term t;
              Format.eprintf "t1.typ: %a@." Print.typ t1.typ;
              Format.eprintf "fields: %a@." Print.(list (label * (__ * typ))) (assoc env t1.typ);
              assert false
          in
          let ty' = tr.typ env ty in
          if f = Mutable then Term.(!(field ~ty:(Ty.ref ty') t1' s)) else Term.field ~ty:ty' t1' s
      | Local (Decl_type decls, _) ->
          let env' = Fmap.(list (fst Path._LId)) decls @ env in
          set_afv_shallowly @@ tr.term_rec env' t
      | _ -> set_afv_shallowly @@ tr.term_rec env t);
  tr.typ <-
    (fun env typ ->
      match typ with
      | TRecord fields ->
          let aux (s, (f, typ)) =
            let typ' = tr.typ env typ in
            let typ'' = if f = Mutable then Ty.ref typ' else typ' in
            (s, (Immutable, typ''))
          in
          TRecord (List.map aux fields)
      | _ -> tr.typ_rec env typ);
  tr.term []
  |@- Debug.printf "ENCODE_MUTABLE_RECORD: @[%a@." Print.term
  |- Trans.remove_por
  |- Trans.remove_peval

(* TODO: support records in refinement types *)
let mutable_record = Problem.map mutable_record_term

let abst_ref_term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t' = tr.term_rec t in
      match t'.desc with
      | Ref t1 -> make_use t1 Term.unit
      | Deref t1 ->
          Flag.Abstract.over "References";
          Term.(seq t1 (rand t'.typ))
      | SetRef (t1, t2) -> make_use Term.(seq t1 t2) Term.unit
      | Match _ -> Trans.trans_match_with_recover_pat_bv ~tr_desc_rec:tr.desc_rec ~tr_typ:tr.typ t
      | _ -> t');
  tr.typ <-
    (fun typ -> match typ with TConstr (c, _) when c = C.ref -> Ty.unit | _ -> tr.typ_rec typ);
  tr.pat <-
    (fun p ->
      match p.pat_desc with
      | PRecord [ ({ name = "contents" }, _) ] ->
          (* TODO: Support shadowing *)
          Pat.nondet @@ tr.typ p.pat_typ
      | _ -> tr.pat_rec p);
  tr.term |- set_afv |- Trans.elim_unused_let
(* |- Trans.inst_randval *)

let abst_ref_ref_typ =
  Ref_type.make_trans (fun _ rty ->
      match rty with Constr (c, _, _, _) when c = C.ref -> Some !!Ref_type.Ty.unit | _ -> None)

let abst_ref = Problem.map ~tr_ref:abst_ref_ref_typ abst_ref_term

let array_term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Var (LId x) when PrimId.is_array_of_list x ->
          let xs, ty_ret = decomp_tfun (Id.typ x) in
          let ty_ret = ty_ret |> (ValE'._TConstr |- snd) |> _TConstr C.array |> tr.typ in
          let x = xs |> List.get |> Id.typ |> tr.typ |> Id.new_var ~name:"xs" in
          Fun (x, Term.rand ty_ret)
      | App ({ desc = Var (LId x) }, [ t1 ]) when PrimId.is_array_of_list x && is_list_literal t1 ->
          let ts = t1 |> decomp_list |> Option.get |> List.map tr.term in
          let n = List.length ts in
          let i = Id.new_var ~name:"i" Ty.int in
          let ti = make_var i in
          let ty = tr.typ @@ list_typ t1.typ in
          let its = List.mapi Pair.pair ts in
          let r =
            List.fold_right
              (fun (j, x) t -> [%term if `ti = int j then `x else `t])
              its (Term.bot ty)
          in
          [%term
            ref
              ( int n,
                fun i ->
                  assert (0 <= `ti && `ti < int n);
                  `r )]
            .desc
      | Var (LId x) when PrimId.is_list_of_array x ->
          let xs, ty_ret = decomp_tfun (Id.typ x) in
          let ty_ret = ty_ret |> (ValE'._TConstr |- snd) |> _TConstr C.list |> tr.typ in
          let x = xs |> List.get |> Id.typ |> tr.typ |> Id.new_var ~name:"xs" in
          Fun (x, Term.rand ty_ret)
      | _ -> tr.desc_rec desc);
  tr.typ <-
    (fun typ ->
      match typ with
      | TConstr (c, [ ty ]) when c = C.array ->
          let ty' = tr.typ ty in
          Ty.(ref (int * fun_ int ty'))
      | _ -> tr.typ_rec typ);
  tr.term

let encode_array_ref_typ =
  let open Ref_type in
  make_trans (fun tr ty ->
      match ty with
      | Constr (c, [ ty' ], _, _) when C.is_array c -> Some Ty.(ref (!!int * fun_ !!int (tr ty')))
      | _ -> None)

let array = Problem.map ~tr_ref:encode_array_ref_typ array_term

let record_term =
  let tr = Tr.make () in
  tr.typ <-
    (fun typ ->
      match typ with
      | TRecord fields ->
          make_ttuple
          @@ List.map
               (fun (_, (f, typ)) ->
                 if f = Mutable then unsupported "mutable record";
                 tr.typ typ)
               fields
      | _ -> tr.typ_rec typ);
  tr.pat <-
    (fun p ->
      match p.pat_desc with
      | PRecord [ ({ name = "contents" }, _) ] ->
          (* TODO: Support shadowing *)
          tr.pat_rec p
      | PRecord fields ->
          let ps =
            ValE'._TRecord p.pat_typ
            |> List.map (fun (f, (_, ty)) ->
                   match Id.List.assoc_opt f fields with
                   | None -> Pat.any @@ tr.typ ty
                   | Some p -> tr.pat p)
          in
          let typ = tr.typ p.pat_typ in
          make_pattern (PTuple ps) typ
      | _ -> tr.pat_rec p);
  tr.term <-
    (fun t ->
      match (t.desc, t.typ) with
      | Record fields, _ ->
          if is_mutable_record t.typ then unsupported "Mutable records";
          make_tuple @@ List.map (tr.term -| snd) fields
      | Local (Decl_type decls, _), _ ->
          let tys =
            List.concat_map (snd |- snd |- get_tconstr_typ |- List.map (fst |- Path.id_of)) decls
          in
          let check (s, (_, ty)) = match ty with TRecord _ -> List.mem s tys | _ -> false in
          if List.exists check decls then unsupported "recursive record types";
          tr.term_rec t
      | Field (t1, _), _ when is_mutable_record t1.typ -> unsupported "Mutable records"
      | Field (t1, s), _ ->
          let fields = ValE'._TRecord t1.typ in
          let t1' = tr.term t1 in
          make_proj (List.find_pos (fun _ (s', _) -> s = s') fields) t1'
      | SetField _, _ -> unsupported "Mutable records"
      | _ -> tr.term_rec t);
  tr.term -| Trans.complete_precord

let encode_record_ref_typ =
  let open Ref_type in
  make_trans (fun tr ty ->
      match ty with
      | Record fields ->
          let aux (_, (f, typ)) =
            if f = Mutable then unsupported "mutable record";
            tr typ
          in
          Some (Ty.tuple @@ List.map aux fields)
      | _ -> None)

let record = Problem.map ~tr_ref:encode_record_ref_typ record_term

let rec is_enum_variant env typ =
  match typ with
  | TVariant (_, rows) ->
      if List.exists (row_ret |- ( <> ) None) rows then unsupported "%s" __FUNCTION__;
      List.for_all (row_args |- ( = ) []) rows
  | TConstr (s, _) ->
      List.assoc_opt ~eq:Path.eq s env |> Option.map snd |> Option.exists (is_enum_variant env)
  | _ -> false

let rec position env c typ =
  match typ with
  | TVariant (_, rows) -> (
      try
        rows
        |> List.sort (Compare.on (row_constr |- Id.name))
        |> List.find_pos (fun _ row -> Id.(c = row.row_constr))
      with Not_found ->
        Format.eprintf {|label "%a" is not found in the type "%a"@.|} Print.label c Print.typ typ;
        assert false)
  | TConstr (s, _) when List.mem_assoc ~eq:Path.eq s env ->
      position env c @@ snd @@ List.assoc ~eq:Path.eq s env
  | _ -> invalid_arg "position"

let enum_variant_term =
  let tr = Tr2.make () in
  tr.typ <- (fun env typ -> if is_enum_variant env typ then Ty.int else tr.typ_rec env typ);
  tr.pat <-
    (fun env p ->
      match p.pat_desc with
      | PConstr (_, LId c, []) when is_enum_variant env p.pat_typ ->
          Pat.int @@ position env c p.pat_typ
      | _ -> tr.pat_rec env p);
  tr.term <-
    (fun env t ->
      match t.desc with
      | Constr (_, LId c, []) when is_enum_variant env t.typ -> Term.int @@ position env c t.typ
      | Local (Decl_type decls, _) ->
          let env' = List.map (Pair.map_fst Path._LId) decls @ env in
          tr.term_rec env' t
      | _ -> tr.term_rec env t);
  tr.term []

(* TODO: support variants in refinement types *)
let enum_variant = Problem.map enum_variant_term

let is_nonrec_variant typ =
  match typ with
  | TVariant (_, rows) ->
      if List.exists (row_ret |- ( <> ) None) rows then unsupported "%s" __FUNCTION__;
      List.for_all (row_args |- ( = ) []) rows
  | _ -> false

(** Assuming that Trans.inline_simple_types is preceded (* non-recursive variants must be inlined *) *)
let nonrec_variant_term =
  let tr = Tr.make () in
  let sort_and_tr_rows rows =
    let rows' = List.sort (Compare.on (row_constr |- Id.name)) rows in
    List.map (fun row -> { row with row_args = List.map tr.typ row.row_args }) rows'
  in
  tr.typ <-
    (fun typ ->
      match typ with
      | TVariant (VNonPoly, rows) ->
          rows
          |> sort_and_tr_rows
          |> List.map (fun row -> Ty.(bool * tuple row.row_args))
          |> Ty.tuple
      | TVariant (VPoly _, _) -> [%invalid_arg]
      | _ -> tr.typ_rec typ);
  tr.pat <-
    (fun p ->
      match p.pat_desc with
      | PConstr (_, LId c, ps) when Type.Is'._TVariant p.pat_typ ->
          let ps' = List.map tr.pat ps in
          let ps_rows =
            Type.ValE'._TVariant p.pat_typ
            |> snd
            |> sort_and_tr_rows
            |> List.map (fun row ->
                   let ty = Ty.tuple row.row_args in
                   if Id.(c = row.row_constr) then Pat.(const Term.tt * tuple ps')
                   else Pat.(const Term.ff * __ ty))
          in
          Pat.tuple ps_rows
      | _ -> tr.pat_rec p);
  tr.term <-
    (fun t ->
      match t.desc with
      | Constr (_, LId c, ts) when Type.Is'._TVariant t.typ ->
          let rows = Type.ValE'._TVariant t.typ |> snd |> sort_and_tr_rows in
          let pos, _ =
            try Type.ValE'._TVariant t.typ |> snd |> assoc_row_with_pos ~sort:true c
            with Not_found ->
              Format.eprintf "c: %a@." Print.constr c;
              assert false
          in
          let ts' = List.map tr.term ts in
          let make i row =
            if i = pos then Term.(pair tt (tuple ts'))
            else Term.(pair ff (dummy (Ty.tuple row.row_args)))
          in
          Term.tuple @@ List.mapi make rows
      | Local (Decl_type decls, t1) ->
          let decls' = Fmap.(list (snd (snd tr.typ_rec))) decls in
          let t1' = tr.term t1 in
          let ty = tr.typ t.typ in
          make ~attr:t.attr (Local (Decl_type decls', t1')) ty
      | _ -> tr.term_rec t);
  tr.term |- Trans.null_tuple_to_unit |- Trans.elim_singleton_tuple

(* TODO: support variants in refinement types *)
let nonrec_variant = Problem.map nonrec_variant_term

(* Support only records without type parameters *)
let abst_rec_record_term =
  let tr = Tr2.make () in
  tr.term <-
    (fun recs t ->
      match t.desc with
      | Local (Decl_type decls, t1) ->
          let recs' =
            let cs =
              List.rev_flatten_map
                (snd |- snd |- get_tconstr_typ |- List.filter_map (fst |- Type.Val._LId))
                decls
            in
            let check (c, (params, ty)) =
              if params <> [] then [%unsupported];
              Type.Is._TRecord ty && Id.List.mem c cs
            in
            decls |> List.filter check |> List.map (fun (s, _) -> TConstr (LId s, []))
          in
          Debug.printf "decls: %a@." Print.(decls) [ Decl_type decls ];
          Debug.printf "recs': %a@.@." Print.(list typ) recs';
          let is_rec s = List.mem ~eq:Type.eq (TConstr (LId s, [])) recs' in
          let decls' =
            List.map (fun (s, (_, ty)) -> (s, ([], if is_rec s then Ty.int else ty))) decls
          in
          let t1' = tr.term (recs' @ recs) t1 in
          make_local (Decl_type decls') t1'
      | Record fields when List.mem ~eq:Type.eq t.typ recs ->
          Flag.Abstract.over "Recursive records";
          let bindings =
            fields
            |> List.map snd
            |> List.map (tr.term recs)
            |> List.map (Pair.add_left new_var_of_term)
          in
          make_lets bindings randint_unit_term
      | SetField (t1, _, t2) when List.mem ~eq:Type.eq t1.typ recs ->
          Flag.Abstract.over "Recursive records";
          let t1' = tr.term recs t1 in
          let t2' = tr.term recs t2 in
          make_seq t1' t2'
      | Field (t1, _) when List.mem ~eq:Type.eq t1.typ recs ->
          Flag.Abstract.over "Recursive records";
          let t1' = tr.term recs t1 in
          let ty = tr.typ recs t.typ in
          Term.(seq t1' (rand ty))
      | Match (_, pats) ->
          let t1', pats' =
            match tr.desc_rec recs t.desc with
            | Match (t', pats') -> (t', pats')
            | _ -> assert false
          in
          let pats'' =
            List.map2
              (fun before after -> Trans.recover_pat_bv ~tr_typ:(tr.typ recs) ~before ~after)
              pats pats'
          in
          make_match t1' pats''
      | _ -> t |> tr.term_rec recs |> set_afv_shallowly);
  tr.pat <-
    (fun recs p ->
      match p.pat_desc with
      | PRecord _ when List.mem ~eq:Type.eq p.pat_typ recs -> make_pnondet Ty.int
      | _ -> set_afv_abv_pat @@ tr.pat_rec recs p);
  tr.typ <- (fun recs ty -> if List.mem ty recs then Ty.int else tr.typ_rec recs ty);
  Trans.lift_pwhen |- Trans.split_type_decls |- tr.term []

(* TODO: support records in refinement types *)
let abst_rec_record = Problem.map abst_rec_record_term

let abst_poly_comp_term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t' = tr.term_rec t in
      match t'.desc with
      | BinOp ((Eq | Lt | Gt | Leq | Geq), t1, t2) -> (
          match elim_tattr t1.typ with TBase _ -> t' | _ -> Term.(seqs [ t1; t2 ] randb))
      | _ -> t');
  tr.term

let abst_poly_comp = Problem.map abst_poly_comp_term

let option_term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t' = tr.term_rec t in
      match t'.desc with
      | TNone -> make_none_enc @@ get_opt_typ_enc t'.typ
      | TSome t -> make_some_enc t
      | _ -> t');
  tr.typ <-
    (fun ty ->
      match ty with
      | TConstr (c, [ ty' ]) when C.is_option c -> opt_typ_enc @@ tr.typ ty'
      | _ -> tr.typ_rec ty);
  tr.pat <-
    (fun p ->
      let p' = tr.pat_rec p in
      match p'.pat_desc with
      | PNone ->
          let ty = get_opt_typ_enc p'.pat_typ in
          Pat.(tuple [ const none_flag; __ ty ])
      | PSome p -> Pat.(tuple [ const some_flag; p ])
      | _ -> p');
  tr.term

let option = Problem.map option_term

(** [ignore_constr_arg (check_constr, check_arg)] removes the arguments of constructors that satisfy both of the below:
    check_constr : condition on constructors
    check_arg : condition on argument types
    changed : type constructors whose definitions are changed
 *)
let ignore_constr_arg : (bool -> path -> bool) * (typ -> bool) -> term -> term =
  let tr = Tr2.make () in
  let will_be_changed (check_constr, check_arg, changed) ty =
    col_constrs ty |> List.exists (Type.ValE._LId |- Id.List.mem -$- changed)
    ||
    match ty with
    | TVariant (kind, rows) ->
        rows
        |> List.exists (fun row ->
               check_constr (kind <> VNonPoly) (Type.LId row.row_constr)
               && List.exists check_arg row.row_args)
    | _ -> false
  in
  tr.term <-
    (fun ((check_constr, check_arg, _) as env) t ->
      match t.desc with
      | Constr (b, s, ts) when check_constr b s ->
          let ts1, ts2 = ts |> List.map (tr.term env) |> List.partition (Syntax.typ |- check_arg) in
          let ty = tr.typ env t.typ in
          Term.(seqs ts1 (constr s ts2 ty))
      | Match _ ->
          Trans.trans_match_with_recover_pat_bv ~tr_desc_rec:(tr.desc_rec env) ~tr_typ:(tr.typ env)
            t
      | BinOp ((Eq | Lt | Gt | Leq | Geq), t1, t2) when will_be_changed env t1.typ ->
          let t1' = tr.term env t1 in
          let t2' = tr.term env t2 in
          Term.(seqs [ t1'; t2' ] randb)
          (* TODO: Refine this by using type definitions *)
      | Local (Decl_type decl, t) ->
          let decl' = tr.decl env (Decl_type decl) |> ValE._Decl_type in
          let changed' =
            List.filter_map
              (fun (c, (_, ty)) -> if will_be_changed env ty then Some c else None)
              decl
          in
          Term.type_ decl' @@ tr.term (check_constr, check_arg, changed') t
      | _ -> set_afv_shallowly @@ tr.term_rec env t);
  tr.typ <-
    (fun ((check_constr, check_arg, _) as env) ty ->
      match ty with
      | TVariant (kind, rows) ->
          let rows' =
            rows
            |> List.map (fun row ->
                   if row.row_ret <> None then unsupported "%s" __FUNCTION__;
                   let b = check_constr (kind <> VNonPoly) (Type.LId row.row_constr) in
                   let row_args =
                     row.row_args |> List.map (tr.typ env) |> b ^> List.filter_out check_arg
                   in
                   { row with row_args })
          in
          TVariant (kind, rows')
      | _ -> tr.typ_rec env ty);
  tr.pat <-
    (fun ((check_constr, check_arg, _) as env) p ->
      let p' = tr.pat_rec env p in
      let desc =
        match p'.pat_desc with
        | PConstr (b, s, ps) when check_constr b s ->
            let ps' = List.filter_out (fun p -> check_arg p.pat_typ) ps in
            PConstr (b, s, ps')
        | desc -> desc
      in
      make_pattern desc p'.pat_typ);
  fun (c1, c2) t -> tr.term (c1, c2, []) @@ Trans.make_bind_for_PAlias ~force:true t

let ignore_data_arg = ignore_constr_arg (Fun.const2 true, Fun.const true)

let make_ignore_check rows =
  let constrs = List.map (Type.row_constr |- Path._LId) rows in
  fun _poly p -> List.mem ~eq:Path.eq p constrs

let ignore_exn_arg t =
  match find_exn_typ t with
  | Some (TVariant (_, rows)) -> ignore_constr_arg (make_ignore_check rows, Fun.const true) t
  | _ -> t

let ignore_exn_fun_arg t =
  match find_exn_typ t with
  | Some (TVariant (_, rows)) -> ignore_constr_arg (make_ignore_check rows, is_fun_typ) t
  | _ -> t

let ignore_rec_exn_arg t =
  match find_exn_typ t with
  | Some (TVariant (_, rows)) -> ignore_constr_arg (make_ignore_check rows, Type.eq Ty.exn) t
  | _ -> t

let lazy_term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | Lazy t1 -> Term.fun_ (Id.new_var Ty.unit) @@ tr.term t1
      | _ -> tr.term_rec t);
  tr.typ <-
    (fun ty ->
      match ty with
      | TConstr (c, [ ty ]) when C.is_lazy c ->
          let ty' = tr.typ ty in
          Ty.(fun_ unit ty')
      | _ -> tr.typ_rec ty);
  tr.pat <-
    (fun p ->
      match p.pat_desc with
      | PLazy p1 ->
          let x = Id.new_var @@ tr.typ p.pat_typ in
          let desc = PEval (x, Term.(var x @@ [ unit ]), tr.pat p1) in
          make_pattern ~attr:p1.pat_attr desc p1.pat_typ
      | _ -> tr.pat_rec p);
  tr.term

let lazy_ = Problem.map lazy_term

let abst_obj_term =
  let tr = Tr.make () in
  let tr_typ ty = match ty with TConstr (c, []) when C.is_obj c -> Ty.int | _ -> tr.typ_rec ty in
  tr.typ <- tr_typ;
  tr.term

let abst_obj = Problem.map abst_obj_term

let ignore_mutual_data_arg t =
  let cs =
    t
    |> Trans.split_type_decls
    |> col_type_decl
    |> List.filter (List.length |- ( <= ) 2)
    |> List.flatten_map
         (List.flatten_map (fun (_, (_, ty)) ->
              match ty with TVariant (VNonPoly, labels) -> List.map row_constr labels | _ -> []))
  in
  let check_constr _ (s : path) = match s with LId c -> Id.List.mem c cs | _ -> false in
  t |> ignore_constr_arg (check_constr, Fun.const true) |> Trans.split_type_decls

(** Assuming that [nonrec_variant] is preceded? *)
let recdata p =
  match !Flag.Encode.RecData.dest with
  | Tuple -> Encode_rec.trans p
  | Variant -> Encode_rec_variant.trans p

let list = Encode_list.trans
let pr s t = Debug.printf "##[Encode] %s: %a@." s Problem.print t

let all t =
  t
  |@> pr "INPUT"
  |> mutable_record
  |@> pr "MUTABLE_RECORD"
  |> record
  |@> pr "RECORD"
  |> !Flag.Abstract.ignore_data_arg ^> Problem.map ignore_data_arg
  |@> !Flag.Abstract.ignore_data_arg @> pr "IGNORE_DATA_ARG"
  |> !Flag.Abstract.ignore_exn_arg ^> Problem.map ignore_exn_arg
  |@> !Flag.Abstract.ignore_exn_arg @> pr "IGNORE_EXN_ARG"
  |> Problem.map ignore_exn_fun_arg
  |@> pr "IGNORE_EXN_FUN_ARG"
  |> Problem.map ignore_mutual_data_arg
  |@> pr "IGNORE_MUTUAL_DATA_ARG"
  |> Flag.Encode.RecData.(!dest <> Variant) ^> enum_variant
  |@> Flag.Encode.RecData.(!dest <> Variant) @> pr "ENUM_VARIANT"
  |> lazy_
  |@> pr "LAZY"
  |> nonrec_variant
  |@> pr "NONREC_VARIANT"
  |> recdata
  |@> pr "RECDATA"
  |> option
  |@> pr "OPTION"
  |> (list |- fst)
  |@> pr "LIST"
  |> array
  |@> pr "ARRAY"
  |> abst_ref
  |@> pr "ABST_REF"
  |> abst_obj
  |@> pr "ABST_OBJ"

let typ_of f typ =
  typ |> Id.new_var |> make_var |> Problem.safety |> f |> Problem.term |> Syntax.typ
