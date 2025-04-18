open Util
open Type
open Syntax
open Problem
module IdMap = Map.Make (ID)

type typ_declares = (constr, typ list * typ) Map.t
type typ_bindings = typ IdMap.t
type env = { decls : typ_declares; binds : typ_bindings }

(* TODO: BUGGY (constructors' labels must be unique) *)
let mk_env t : env =
  let typ_declares =
    let rec go decls t =
      match t.desc with
      | Local (Decl_type new_decls, t) ->
          let f decls (s, (_params, ty)) =
            match ty with
            | TVariant (VNonPoly, rows) ->
                List.L.fold_left rows ~init:decls ~f:(fun decls row ->
                    Map.add row.row_constr (row.row_args, TConstr (LId s, [])) decls)
            | _ -> decls
          in
          let decls' = List.fold_left f decls new_decls in
          go decls' t
      | _ -> decls
    in
    go Map.empty t
  in
  { decls = typ_declares; binds = IdMap.empty }

let trans_term =
  let tr = Tr2.make () in
  let type_pat env pat_ty (pat, ret) =
    match pat.pat_desc with
    | PConstr (true, _, _) -> unsupported "Ref_type_preg_typing.trans_term"
    | PConstr (false, l, ps) ->
        let l = match l with LId l -> l | _ -> assert false in
        let tys, ty =
          try Map.find l env.decls
          with Not_found ->
            Format.eprintf "Unknown constructor %a@." Print.constr l;
            assert false
        in
        if not (pat_ty = ty) then (
          Format.eprintf "Type error: constructor %a does not have type %a@." Print.constr l
            Print.typ pat_ty;
          assert false);
        let ps', binds' =
          try
            List.fold_left
              (fun (ps', binds') (p, ty) ->
                match p.pat_desc with
                | PVar x ->
                    (List.snoc ps' (Term_util.make_pvar @@ Id.set_typ x ty), IdMap.add x ty binds')
                | PAny -> (List.snoc ps' (Term_util.make_pany ty), binds')
                | _ -> assert false)
                (* nesting pattern is currently unsupported in spec_parser.mly *)
              ([], env.binds) (List.combine ps tys)
          with Invalid_argument e ->
            Format.eprintf "%s@." e;
            Format.eprintf "wrong number of arguments for constructor %a.@." Print.constr l;
            Format.eprintf "ps  = %a@." Print.(list pattern) ps;
            Format.eprintf "tys = %a@." Print.(list typ) tys;
            assert false
        in
        let env' = { env with binds = binds' } in
        (make_pattern (PConstr (false, LId l, ps')) pat_ty, tr.term env' ret)
    | _ -> (make_pattern pat.pat_desc pat_ty, tr.term env ret)
  in
  tr.term <-
    (fun env t ->
      match t.desc with
      (* Assumption: if t.typ = TData "???" then t = Match(_,_) *)
      | Var (LId x) when Id.typ x = Type_util.Ty.unknown -> (
          try
            let ty = IdMap.find x env.binds in
            make (Var (LId (Id.set_typ x ty))) ty
          with Not_found ->
            Format.eprintf "unbound variable %a found in SPEC@." Print.id_typ x;
            assert false)
      | Match (t1, cases) ->
          let t1' = tr.term env t1 in
          let match_sty = t1'.typ in
          let cases' = List.map (type_pat env match_sty) cases in
          let whole_ty = typ @@ snd @@ List.hd cases' in
          make (Match (t1', cases')) whole_ty
      | _ -> tr.term_rec env t);
  tr.term

let trans_rtype env rty =
  let open Ref_type in
  let term = trans_term env in
  let rec rtype rty =
    match rty with
    | Var _ -> [%unsupported]
    | Base (base, x, p) -> Base (base, x, term p)
    | Constr (s, [], x, p) -> Constr (s, [], x, term p)
    | Constr _ -> unsupported "Ref_type_pred_typing.trans_rtype Constr"
    | Fun (arg, argty, retty) -> Fun (arg, rtype argty, rtype retty)
    | Tuple xts -> Tuple (List.map (Pair.map_snd rtype) xts)
    | Inter (sty, rts) -> Inter (sty, List.map rtype rts)
    | Union (sty, rts) -> Union (sty, List.map rtype rts)
    | ExtArg (arg, argty, retty) -> ExtArg (arg, rtype argty, rtype retty)
    | List (i, p_i, len, p_len, rty) -> List (i, term p_i, len, term p_len, rtype rty)
    | Exn (rty1, rty2) -> Exn (rtype rty1, rtype rty2)
    | Variant _ -> unsupported "Ref_type_pred_typing.trans_rtype Variant"
    | Record _ -> unsupported "Ref_type_pred_typing.trans_rtype Record"
  in
  rtype rty

let ref_type_pred_typing p =
  match p.kind with
  | Safety -> p
  | Ref_type_check renv ->
      let env = mk_env p.term in
      (*Format.fprintf !Flag.Print.target "%a@." *)
      let renv = List.map (Pair.map_snd (trans_rtype env)) renv in
      { p with kind = Ref_type_check renv }
