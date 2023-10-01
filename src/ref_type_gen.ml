open Util
open Ref_type

module S = Syntax
module SU = Term_util
module T = Type
module TU = Type_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let comment s t =
  if !!Debug.check then
    SU.add_comment s t
  else
    t

let rec generate_check typ_exn make_fail genv cenv x typ =
  Debug.printf "Ref_type_gen.generate_check: %a : %a@." Id.print x print typ;
  match typ with
  | Base(_, y, p) ->
      genv, cenv, SU.subst_var y x p
  | Constr(_, [], y, p) ->
      genv, cenv, SU.subst_var y x p
  | Constr _ -> unsupported "Ref_type_gen.generate_check"
  | Fun(y, typ1, Exn(typ2, typ3)) ->
      begin
        match typ_exn with
        | None ->
            generate_check typ_exn make_fail genv cenv x (Fun(y, typ1, typ2))
        | Some typ_exn' ->
            let genv',cenv',t_typ1 = generate typ_exn make_fail genv cenv typ1 in
            let z = SU.new_var_of_term t_typ1 in
            let e = Id.new_var ~name:"e" typ_exn' in
            let typ2' = subst_var y z typ2 in
            let typ3' = subst_var y z typ3 in
            let r = Id.new_var ~name:"r" @@ to_simple ~with_pred:true typ2 in
            let genv'',cenv'',t_typ2' = generate_check typ_exn make_fail genv' cenv' r typ2' in
            let genv''',cenv''',t_typ3' = generate_check typ_exn make_fail genv'' cenv'' e typ3' in
            let t' = SU.Term.(let_ [r, var x @ [var z]] t_typ2') in
            genv''', cenv''', SU.Term.(let_ [z,t_typ1] (trywith_h t' (fun_ e t_typ3')))
      end
  | Fun(y,typ1,typ2) ->
      let genv',cenv',t_typ1 = generate typ_exn make_fail genv cenv typ1 in
      let z = Id.new_var t_typ1.S.typ in
      let t_typ2 = SU.Term.(var x @ [var z]) in
      let r = Id.new_var ~name:"r" t_typ2.S.typ in
      let genv'',cenv'',t_typ2' =
        let typ2' = subst_var y z typ2 in
        generate_check typ_exn make_fail genv' cenv' r typ2'
      in
      genv'', cenv'', SU.make_lets [z,t_typ1; r,t_typ2] t_typ2'
  | Tuple xtyps ->
      let xs' = List.map (fun (x,typ) -> Id.new_var ~name:(Id.name x) @@ to_simple ~with_pred:true typ) xtyps  in
      let typs = List.fold_right2 (fun x' (x,typ) acc -> typ :: List.map (subst_var x x') acc) xs' xtyps [] in
      let genv',cenv',ts =
        let aux x' typ (genv,cenv,ts) =
          let genv',cenv',t = generate_check typ_exn make_fail genv cenv x' typ in
          genv', cenv', t::ts
        in
        List.fold_right2 aux xs' typs (genv,cenv,[])
      in
      genv', cenv', SU.make_lets (List.mapi (fun i x' -> x', SU.Term.(proj i (var x))) xs') @@ SU.make_ands ts
  | List(l,p_len,y,p_i,typ1) when p_i.S.desc = S.Const S.True && not @@ occur y typ1 ->
      let styp = to_simple ~with_pred:true typ in
      let atyp1 = to_abst_typ typ1 in
      let atyp = to_abst_typ typ in
      let l' = Id.new_var ~name:"l" TU.Ty.int in
      let add_len t =
        let t' = SU.Term.(t && (l |-> var l') p_len) in
        if t' = SU.true_term
        then SU.true_term
        else SU.Term.(let_ [l', length (var x)] t')
      in
      let typ1' = subst_var l l' typ1 in
      let genv',cenv',t =
        if List.mem_assoc ~eq:same typ cenv
        then
          let f,_ = List.assoc ~eq:same typ cenv in
          genv, cenv, SU.Term.(var f @ [var x])
        else
          let zs = Id.new_var ~name:"xs" atyp in
          let f = Id.new_var ~name:("check_" ^ TU.to_id_string styp) @@ T.TFun(zs,TU.Ty.bool) in
          let z = Id.new_var ~name:"x" atyp1 in
          let zs' = Id.new_var ~name:"xs'" atyp in
          let genv',cenv',t_b1 = generate_check typ_exn make_fail genv cenv z typ1' in
          if t_b1 = SU.true_term
          then
            genv', cenv', SU.true_term
          else
            let t_body =
              let pat_nil = SU.make_pnil ~elem_typ:styp, SU.true_term in
              let pat_cons =
                let t_b2 = SU.Term.(var f @ [var zs']) in
                SU.Pat.(cons (var z) (var zs')), SU.Term.(t_b1 && t_b2)
              in
              SU.make_match (SU.make_var zs) [pat_nil; pat_cons]
            in
            let def = f, SU.make_fun zs @@ comment (Format.asprintf "CHECK: %a" print typ) t_body in
            Debug.printf "CHECK: %a: %a@." print typ (Pair.print Print.id Print.term) def;
            let t = SU.Term.(var f @ [var x]) in
            if List.Set.supset ~eq:Id.eq [zs;SU.make_length_var TU.Ty.unknown;f] @@ S.get_fv t_body
            then genv'@[typ,def], cenv', t
            else genv', cenv', SU.make_let [def] t
      in
      genv', cenv', add_len t
  | Inter(_, typs) ->
      let aux (genv',cenv',ts) typ =
        let genv'',cenv'',t = generate_check typ_exn make_fail genv' cenv' x typ in
        genv'', cenv'', ts@[t]
      in
      let genv'',cenv'',ts = List.fold_left aux (genv,cenv,[]) typs in
      Debug.printf "generate_check typ: %a@." (List.print print) typs;
      Debug.printf "generate_check ts: %a@." (List.print  Print.term) ts;
      genv'', cenv'', SU.make_ands ts
  | Union(_, typs) ->
      let aux (genv',cenv',ts) typ =
        let genv'',cenv'',t = generate_check typ_exn make_fail genv' cenv' x typ in
        let t' =
          match typ_exn with
          | None -> t
          | Some typ_exn' ->
              let e = Id.new_var ~name:"e" typ_exn' in
              SU.Term.(trywith_h t (fun_ e false_))
        in
        genv'', cenv'', t'::ts
      in
      let genv'',cenv'',ts = List.fold_left aux (genv,cenv,[]) typs in
      genv'', cenv'', SU.make_ors ts
  | Exn(typ1, typ2) when is_bottom' typ2 -> generate_check typ_exn make_fail genv cenv x typ1
  | Exn _ ->
      Format.eprintf "typ: %a@." print typ;
      unsupported "Ref_type_gen.generate_check Exn"
  | ExtArg _ ->
      Format.eprintf "typ: %a@." print typ;
      unsupported "Ref_type_gen.generate_check ExtArg"
  | List _ ->
      Format.eprintf "typ: %a@." print typ;
      unsupported "Ref_type_gen.generate_check List"
  | Variant _ ->
      Format.eprintf "typ: %a@." print typ;
      unsupported "Ref_type_gen.generate_check Variant"
  | Record _ ->
      Format.eprintf "typ: %a@." print typ;
      unsupported "Ref_type_gen.generate_check Record"

and generate typ_exn make_fail genv cenv typ =
  Debug.printf "Ref_type_gen.generate: %a@." print typ;
  let genv',cenv',t =
    match typ with
    | Base(T.TInt, _, _) ->
        let x' = Id.new_var TU.Ty.int in
        let genv',cenv',t_check = generate_check typ_exn make_fail genv cenv x' typ in
        genv', cenv', SU.Term.(let_ [x',randi] (assume t_check (var x')))
    | Base(T.TBool, _, _) ->
        let x' = Id.new_var TU.Ty.bool in
        let genv',cenv',t_check = generate_check typ_exn make_fail genv cenv x' typ in
        genv', cenv', SU.Term.(let_ [x',randb] (assume t_check (var x')))
    | Base(T.TUnit, x, _) ->
        let genv',cenv',t_check = generate_check typ_exn make_fail genv cenv x typ in
        genv', cenv', SU.Term.(assume t_check unit)
    | Constr(c, [], _, _) when TU.is_base_prim c ->
        let typ' = to_simple ~with_pred:true typ in
        let x' = Id.new_var typ' in
        let genv',cenv',t_check = generate_check typ_exn make_fail genv cenv x' typ in
        genv', cenv', SU.Term.(let_ [x',rand typ'] (assume t_check (var x')))
    | Constr(_, [], x, t) ->
        let uns() = unsupported "Ref_type_gen.generate ADT" in
        let sty = to_simple ~with_pred:true typ in
        let x' = Id.new_var sty in
        let bindings =
          let open Syntax in
          match t.desc with
          | Const _ -> assert false
          | Match({desc=Var y}, ps) when Lid.(LId x = y) ->
              let bindings =
                let aux (p,t) =
                  let s', xs =
                    match p.pat_desc with
                    | PConstr(false, s, ps) ->
                        let aux' p =
                          match p.pat_desc with
                          | PAny -> Id.new_var p.pat_typ
                          | PVar x -> x
                          | _ -> uns()
                        in
                        s, List.map aux' ps
                    | PAny -> TU.lid_of_string "_", []
                    | _ -> uns()
                  in
                  s', (xs, t)
                in
                List.map aux ps
              in
              if List.length (List.map fst bindings) <> List.length (List.unique @@ List.map fst bindings) then uns();
              bindings
          | Match _ -> uns();
          | _ -> [TU.lid_of_string "_", ([], t)]
        in
        let ts =
          let aux (s,(xs,t)) =
            if s = TU.lid_of_string "_" then
              SU.Term.(let_ [x', rand sty] (assume t (var x')))
            else
              let defs = List.map (fun x -> x, SU.Term.rand @@ Id.typ x) xs in
              let t_s = S.(make (Constr(false, s, List.map SU.Term.var xs)) sty) in
              SU.Term.(lets defs (assume t t_s))
          in
          List.map aux bindings
        in
        genv, cenv, SU.Term.brs ts
    | Constr(_, _, _, _) -> unsupported "Ref_type_gen.generate Constr"
    | Fun(x,typ1,typ2) ->
        let x' = Id.new_var @@ to_abst_typ ~with_pred:true typ1 in
        let typ2' = subst_var x x' typ2 in
        let genv',cenv',t_typ1 = generate_check typ_exn make_fail genv cenv x' typ1 in
        Debug.printf "Ref_type_gen.generate t_typ1: %a@." Print.term t_typ1;
        let t1 = SU.Term.(randb || t_typ1) in
        let genv'',cenv'',t2 = generate typ_exn make_fail genv' cenv' typ2' in
        let t3 = make_fail @@ to_simple ~with_pred:true typ2' in
        let cmt = Format.asprintf "GEN FUN: %a" print typ2' in
        genv'', cenv'', SU.Term.(fun_ x' (comment cmt (if_ t1 t2 t3)))
    | Tuple xtyps ->
        let xs' = List.map (fun (x,typ) -> Id.new_var ~name:(Id.name x) @@ to_simple ~with_pred:true typ) xtyps  in
        let typs = List.fold_right2 (fun x' (x,typ) acc -> typ :: List.map (subst_var x x') acc) xs' xtyps [] in
        let genv',cenv',ts =
          let aux typ (genv,cenv,ts) =
            let genv',cenv',t = generate typ_exn make_fail genv cenv typ in
            genv',cenv',t::ts
          in
          List.fold_right aux typs (genv,cenv,[])
        in
        genv', cenv', SU.Term.(lets (List.combine xs' ts) (tuple (vars xs')))
    | Inter(styp, []) -> genv, cenv, make_fail styp
    | Inter(_, [typ]) -> generate typ_exn make_fail genv cenv typ
    | Inter(_, Base(base,x,p)::typs) ->
        let p' =
          let aux p typ =
            match typ with
            | Base(base', x', p') ->
                assert (base = base');
                SU.Term.(p && (x' |-> var x) p')
            | _ -> assert false
          in
          List.fold_left aux p typs
        in
        generate typ_exn make_fail genv cenv @@ Base(base, x, p')
    | Inter(_, ((Fun(_,atyp,rtyp))::_ as typs)) when !Flag.Modular.use_ref_typ_gen_method_in_esop2017 ->
        Flag.Method.fail_as_exception := true;
        let rec wrap typ (genv,cenv,v) =
          match typ with
          | Base(_,x,p) ->
              genv, cenv, SU.Term.(assume ((x |-> v) p) v)
          | Fun(x,typ1,typ2) ->
              let f = SU.new_var_of_term v in
              let genv',cenv',t_check = generate_check typ_exn make_fail genv cenv x typ1 in
              let t_app = SU.Term.(var f @ [var x]) in
              let r = SU.new_var_of_term t_app in
              let genv'',cenv'',t_wrap = wrap typ2 (genv', cenv', SU.make_var r) in
              let genv''',cenv''',t_gen = generate typ_exn make_fail genv'' cenv'' typ2 in
              let handler = SU.make_fun (Id.new_var ~name:"u" @@ Option.get typ_exn) t_gen in
              genv''',
              cenv''',
              SU.Term.(fun_ x
                        (let_ [f,v]
                           (if_
                              (randb || t_check)
                              (trywith_h (let_ [r,t_app] t_wrap) handler)
                              t_app)))
          | Tuple xtyps ->
              let xttyps =
                let aux i (x,typ) =
                  let t = SU.make_proj i v in
                  let x' = Id.set_typ x t.S.typ in
                  x', t, typ
                in
                List.mapi aux xtyps
              in
              let genv',cenv',ts =
                let aux (x,_,typ) (genv,cenv,ts) =
                  let genv',cenv',t = wrap typ (genv, cenv, SU.make_var x) in
                  genv',cenv',t::ts
                in
                List.fold_right aux xttyps (genv,cenv,[])
              in
              let t =
                List.fold_right (fun (x,t,_) -> SU.make_let [x,t]) xttyps (SU.make_tuple ts)
              in
              genv', cenv', t
          | Inter(_,typs) ->
              List.fold_right wrap typs (genv,cenv,v)
          | Exn(typ1,typ2) ->
              let genv',cenv',t1 = wrap typ1 (genv,cenv,v) in
              let e = Id.new_var ~name:"e" @@ Option.get typ_exn in
              let genv'',cenv'',t2 = wrap typ2 (genv',cenv',SU.make_var e) in
              let handler = SU.make_fun e t2 in
              genv'', cenv'', SU.Term.trywith_h t1 handler
          | _ ->
              Format.eprintf "%a@." print typ;
              unsupported "Ref_type_gen.wrap"
        in
        let v0 =
          let arg_styp = to_simple ~with_pred:true atyp in
          let ret_styp = to_simple ~with_pred:true rtyp in
          SU.make_fun (Id.new_var ~name:"u" arg_styp) @@ make_fail ret_styp
        in
        List.fold_right wrap typs (genv,cenv,v0)
    | Inter(_, ((Fun _)::_ as typs)) ->
        Flag.Method.fail_as_exception := true;
        let bss = Combination.take_each @@ List.map (Fun.const [true;false]) typs in
        Debug.printf "GEN bss: %a@." (List.print @@ List.print Format.pp_print_bool) bss;
        let x =
          match typs with
          | Fun(_,typ1,_)::_ -> Id.new_var @@ to_abst_typ typ1
          | _ -> assert false
        in
        let typs1,typs2 = List.split_map (function Fun(y,typ1,typ2) -> typ1, subst_var y x typ2 | _ -> assert false) typs in
        Debug.printf "GEN typs1: %a@." (List.print print) typs1;
        Debug.printf "GEN typs2: %a@." (List.print print) typs2;
        let xs = List.map (fun _ -> Id.new_var TU.Ty.bool) typs in
        Debug.printf "GEN xs: %a@." (List.print Id.print) xs;
        let genv',cenv',tbs =
          let aux typ1 (genv,cenv,tbs) =
            let genv', cenv', tb = generate_check typ_exn make_fail genv cenv x typ1 in
            let tb' =
              let e = Id.new_var ~name:"e" @@ Option.default TU.Ty.exn typ_exn in
              SU.Term.(randb || trywith tb e [SU.make_pany (Id.typ e), false_])
              |*> comment @@ Format.asprintf "GEN INTER: beta(%a)" print typ1
            in
            genv', cenv', tb'::tbs
          in
          List.fold_right aux typs1 (genv,cenv,[])
        in
        Debug.printf "GEN tbs: %a@." (List.print Print.term) tbs;
        let tcs =
          let aux bs =
            xs
            |> List.map SU.make_var
            |> List.filter_map2 (Option.some_if -| Fun.const) bs
            |> SU.make_ands
          in
          List.map aux bss
        in
        Debug.printf "GEN tcs: %a@." (List.print Print.term) tcs;
        let rstyp = to_simple ~with_pred:true @@ List.hd typs2 in
        let genv'',cenv'',trs =
          let aux bs (genv,cenv,trs) =
            let typ =
              typs2
              |> List.filter_map2 (Option.some_if -| Fun.const) bs
              |> inter rstyp
            in
            Debug.printf "GEN typ: %a@." print typ;
            let genv',cenv',tr = generate typ_exn make_fail genv cenv typ in
            genv', cenv', tr::trs
          in
          List.fold_right aux bss (genv',cenv',[])
        in
        Debug.printf "GEN trs: %a@." (List.print Print.term) trs;
        let t =
          SU.make_bottom rstyp
          |> List.fold_right2 SU.make_if tcs trs
          |> SU.make_lets @@ List.map2 (fun x tb -> x, tb) xs tbs
          |> SU.make_fun x
        in
        Debug.printf "GEN t: %a@."  Print.term t;
        genv'', cenv'', t
    | Inter(_, ((Exn _)::_ as typs)) ->
        let typs1,typs2 = List.split_map (function Exn(typ1,typ2) -> typ1,typ2 | _ -> assert false) typs in
        let inter' typs = inter (to_simple ~with_pred:true @@ List.hd typs) typs in
        let typ' = Exn(inter' typs1, inter' typs2) in
        generate typ_exn make_fail genv cenv typ'
    | Inter(_, _) ->
        Format.eprintf "INTER: %a@." print typ;
        unsupported "Ref_type_gen.generate: Inter"
    | Union(styp, []) -> [], [], SU.make_bottom styp
    | Union(_, [typ]) -> generate typ_exn make_fail genv cenv typ
    (*
    | Union(_, ((Tuple _)::_ as typs)) ->
        let genv',cenv',ts =
          let aux typ (genv,cenv,ts) =
            let genv',cenv',t = generate typ_exn make_fail genv cenv typ in
            genv',cenv',t::ts
          in
          List.fold_right aux typs (genv,cenv,[])
        in
        genv', cenv', List.fold_left SU.make_br (List.hd ts) (List.tl ts)
     *)
    | Union(_, typs) ->
        let genv',cenv',ts =
          let aux typ (genv,cenv,ts) =
            let genv',cenv',t = generate typ_exn make_fail genv cenv typ in
            genv',cenv',t::ts
          in
          List.fold_right aux typs (genv,cenv,[])
        in
        genv', cenv', List.fold_left SU.make_br (List.hd ts) (List.tl ts)
    | ExtArg(_x,_typ1,_typ2) -> unsupported "Ref_type_gen.generate: ExtArg"
    | List(x,p_len,y,p_i,typ') ->
        if p_i.S.desc <> S.Const S.True || occur y typ' then
          unsupported "Ref_type_gen.generate"
        else
          let styp = to_simple ~with_pred:true typ in
          let l = Id.new_var ~name:"l" TU.Ty.int in
          let p_len' = SU.subst_var x l p_len in
          let genv',cenv',t =
            if List.mem_assoc ~eq:same typ genv
            then
              let f,_ = List.assoc ~eq:same typ genv in
              let t = SU.make_app (SU.make_var f) [SU.make_var l] in
              genv, cenv, t
            else
              let n = Id.new_var TU.Ty.int in
              let f = Id.new_var ~name:("make_r_" ^ TU.to_id_string styp) @@ T.TFun(n, to_abst_typ typ) in
              let t_nil = SU.make_nil2 ~list_typ:styp in
              let genv',cenv',t_typ' = generate typ_exn make_fail genv cenv typ' in
              let t_cons = SU.make_cons t_typ' @@ SU.make_app (SU.make_var f) [SU.make_sub (SU.make_var n) (SU.make_int 1)] in
              let t_b = SU.make_leq (SU.make_var n) (SU.make_int 0) in
              let def = f, SU.make_fun n @@ comment (Format.asprintf "GEN LIST: %a" print typ) @@ SU.make_if t_b t_nil t_cons in
              let t = SU.make_app (SU.make_var f) [SU.make_var l] in
              Debug.printf "GEN: %a: %a@." print typ (Pair.print Print.id Print.term) def;
              if List.Set.supset ~eq:Id.eq [n] @@ S.get_fv @@ snd def
              then genv'@[typ,def], cenv', t
              else genv', cenv', SU.make_let [def] t
          in
          genv', cenv', SU.make_let [l,SU.randint_unit_term] @@ SU.make_assume p_len' t
    | Exn(typ1,typ2) ->
        let genv',cenv',t_typ1 = generate typ_exn make_fail genv cenv typ1 in
        let genv'',cenv'',t_typ2 = generate typ_exn make_fail genv' cenv' typ2 in
        genv'', cenv'', SU.make_br t_typ1 @@ SU.make_raise t_typ2 ~typ:t_typ1.S.typ
    | Variant _ ->
        Format.eprintf "typ: %a@." print typ;
        unsupported "Ref_type_gen.generate Variant"
    | Record _ ->
        Format.eprintf "typ: %a@." print typ;
        unsupported "Ref_type_gen.generate Record"
  in
  Debug.printf "Ref_type_gen.generate: %a@." print typ;
  let ty = to_abst_typ ~with_pred:true typ in
  genv', cenv', S.(make t.desc ty)

let generate_check typ_exn ?(make_fail=SU.make_fail ?loc:None ~force:true) genv cenv x typ = generate_check typ_exn make_fail genv cenv x typ
let generate typ_exn ?(make_fail=SU.make_fail ?loc:None ~force:true) genv cenv typ = generate typ_exn make_fail genv cenv typ
