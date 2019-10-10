open Util
open Type
open Syntax
open Problem

module IdMap = Map.Make(ID)
type typ_declares = (string, typ list * typ) Map.t
type typ_bindings = typ IdMap.t
type env = {decls: typ_declares;
            binds: typ_bindings}

let mk_env t: env =
  let typ_declares =
    let rec go decls t = match t.desc with
      | Local(Decl_type new_decls, t) ->
          let f decls (s,ty) = match ty with
            | TVariant(false,ts) ->
                List.Labels.fold_left ts ~init:decls ~f:(
                  fun decls (l,tys) -> Map.add l (tys, TData s) decls
                )
            | _  -> decls
          in
          let decls' = List.fold_left f decls new_decls in
          go decls' t
      | _ -> decls
    in
      go Map.empty t
  in
    {decls=typ_declares; binds = IdMap.empty}

let trans_term =
  let tr = make_trans2 () in
  let type_pat env pat_ty (pat,ret) =
    match pat.pat_desc with
    | PConstr(l,ps) ->
        let (tys, ty) =
          try
            Map.find l env.decls
          with Not_found ->
            Format.eprintf "Unknown constructor %s@." l;
            assert false
        in
        if not (pat_ty = ty) then begin
          Format.eprintf "Type error: constructor %s does not have type %a@."
            l
            Print.typ pat_ty;
          assert false
        end;
        let ps', binds' =
          try
            List.fold_left
              begin fun (ps', binds') (p,ty) -> match p.pat_desc with
              | PVar(x) ->
                  List.snoc ps' { pat_desc=PVar(Id.set_typ x ty); pat_typ=ty },
                  IdMap.add x ty binds'
              | PAny ->
                  List.snoc ps' { pat_desc=PAny; pat_typ=ty },
                  binds'
              | _ -> assert false
              (* nesting pattern is currently unsupported in spec_parser.mly *)
              end
              ([], env.binds)
              (List.combine ps tys)
          with Invalid_argument(e) ->
            Format.eprintf "%s@." e;
            Format.eprintf "wrong number of arguments for constructor %s.@." l;
            Format.eprintf "ps  = %a@." Print.(list pattern) ps;
            Format.eprintf "tys = %a@." Print.(list typ) tys;
            assert false
        in
        let env' = { env with binds = binds' } in
        {pat_desc = PConstr(l,ps'); pat_typ = pat_ty},
        tr.tr2_term env' ret
    | _ ->
        {pat with pat_typ = pat_ty},
        tr.tr2_term env ret
  in
  let tr_term env t = match t.desc with
    (* Assumption: if t.typ = TData "???" then t = Match(_,_) *)
    | Var(x) when Id.typ x = typ_unknown ->
        begin try
          let ty = IdMap.find x env.binds in
          {t with desc = Var (Id.set_typ x ty);
                  typ  = ty}
        with Not_found ->
          Format.eprintf "unbound variable %a found in SPEC@." Print.id_typ x;
          assert false
        end
    | Match(t1,cases) ->
        let t1' = tr.tr2_term env t1 in
        let match_sty = t1'.typ in
        let cases' = List.map (type_pat env match_sty) cases in
        let whole_ty = typ @@ snd @@ List.hd cases' in
        {t with desc = Match(t1',cases');
                typ  = whole_ty}
    | _ -> tr.tr2_term_rec env t
  in
  tr.tr2_term <- tr_term;
  tr_term

let trans_rtype env rty =
  let open Ref_type in
  let term = trans_term env in
  let rec rtype rty = match rty with
    | Base(base, x, p) -> Base(base, x, term p)
    | ADT(s, x, p) -> ADT(s, x, term p)
    | Fun(arg, argty, retty) -> Fun(arg, rtype argty, rtype retty)
    | Tuple(xts) -> Tuple(List.map (Pair.map_snd rtype) xts)
    | Inter(sty, rts) -> Inter(sty, List.map rtype rts)
    | Union(sty, rts) -> Union(sty, List.map rtype rts)
    | ExtArg(arg, argty, retty) -> ExtArg(arg, rtype argty, rtype retty)
    | List(i, p_i, len, p_len, rty) -> List(i, term p_i, len, term p_len, rtype rty)
    | App _ -> unsupported "Ref_type_pred_typing.trans_rtype: App"
    | Exn(rty1, rty2) -> Exn(rtype rty1, rtype rty2)
  in
  rtype rty

let ref_type_pred_typing p =
  match p.kind with
  | Safety -> p
  | Ref_type_check(renv) ->
      let env = mk_env p.term in
      (*Format.printf "%a@." *)
      let renv = List.map (Pair.map_snd (trans_rtype env)) renv in
      { p with kind = Ref_type_check(renv) }
