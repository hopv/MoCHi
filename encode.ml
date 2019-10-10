open Util
open Syntax
open Term_util
open Type


module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)


let mutable_record_term =
  let tr = make_trans2 () in
  let rec decomp env ty =
    match ty with
    | TData s when List.mem_assoc s env -> decomp env @@ List.assoc s env
    | TData s -> assert false
    | TRecord fields -> fields
    | _ -> assert false
  in
  let tr_pat env p =
    match p.pat_desc with
    | PRecord _ when List.exists (fun (_,(f,_)) -> f = Mutable) @@ decomp env p.pat_typ ->
        unsupported "Pattern matching for mutable record (tr_pat)"
    | _ -> tr.tr2_pat_rec env p
  in
  let tr_term env t =
    match t.desc with
    | Record fields ->
        let aux (s,t) (_,(f,_)) =
          let t' = tr.tr2_term env t in
          s, if f = Mutable then make_ref t' else t'
        in
        let fields' = List.map2 aux fields @@ decomp env t.typ in
        make_record fields' @@ tr.tr2_typ env t.typ
    | SetField(t1,s,t2) ->
        let t1' = tr.tr2_term env t1 in
        let t2' = tr.tr2_term env t2 in
        make_setref (make_field ~ty:(make_tref t2'.typ) t1' s) t2'
    | Field(t1,s) ->
        let t1' = tr.tr2_term env t1 in
        let f,ty = List.assoc s @@ decomp env t1.typ in
        let ty' = tr.tr2_typ env ty in
        if f = Mutable then
          make_deref @@ make_field ~ty:(make_tref ty') t1' s
        else
          make_field ~ty:ty' t1' s
    | Local(Decl_type decls, _) -> tr.tr2_term_rec (decls@env) t
    | _ -> tr.tr2_term_rec env t
  in
  let tr_typ env typ =
    match typ with
    | TRecord fields ->
        let aux (s,(f,typ)) =
          let typ' = tr.tr2_typ env typ in
          let typ'' = if f = Mutable then make_tref typ' else typ' in
          s, (Immutable, typ'')
        in
        TRecord (List.map aux fields)
    | _ -> tr.tr2_typ_rec env typ
  in
  tr.tr2_typ <- tr_typ;
  tr.tr2_term <- tr_term;
  tr.tr2_pat <- tr_pat;
  tr.tr2_term []

(* TODO: support records in refinement types *)
let mutable_record = Problem.map mutable_record_term


let abst_ref_term =
  let tr = make_trans () in
  let tr_term t =
    let t' = tr.tr_term_rec t in
    match t'.desc with
    | Ref t1 ->
        Term.ignore t1
    | Deref t1 ->
        Flag.Encode.use_abst "References";
        Term.(seq t1 (rand t'.typ))
    | SetRef(t1, t2) ->
        Term.(seqs [t1;t2] unit)
    | _ -> t'
  in
  let tr_typ typ =
    match typ with
    | TApp(TRef, _) -> Ty.unit
    | _ -> tr.tr_typ_rec typ
  in
  tr.tr_term <- tr_term;
  tr.tr_typ <- tr_typ;
  tr.tr_term |- Trans.inst_randval

(* TODO: support references in refinement types *)
let abst_ref = Problem.map abst_ref_term


let array_term =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | App({desc=Var x}, [t1]) when Id.name x = "Array.of_list" && is_list_literal t1 ->
        let ts =
          t1
          |> decomp_list
          |> Option.get
          |> List.map tr.tr_term
        in
        let n = List.length ts in
        let i = Id.new_var ~name:"i" Ty.int in
        let ti = make_var i in
        let ty = tr.tr_typ @@ list_typ t1.typ in
        let its = List.mapi Pair.pair ts in
        let r = List.fold_right (fun (j,x) t -> Term.(if_ (ti = int j) x t)) its (Term.bot ty) in
        Term.(ref (pair (int n)
                     (fun_ i
                        (seq (assert_ (int 0 <= ti && ti < int n)) r)))).desc
    | _ -> tr.tr_desc_rec desc
  in
  let tr_typ typ =
    match typ with
    | TApp(TArray, [ty]) ->
        let ty' = tr.tr_typ ty in
        Ty.(ref (int * (fun_ int ty')))
    | _ -> tr.tr_typ_rec typ
  in
  tr.tr_desc <- tr_desc;
  tr.tr_typ <- tr_typ;
  tr.tr_term

(* TODO: support array in refinement types *)
let array = Problem.map array_term



let record_term =
  let tr = make_trans () in
  let rec tr_typ typ =
    match typ with
    | TRecord fields ->
        make_ttuple @@ List.map (fun (s,(f,typ)) -> if f = Mutable then unsupported "mutable record"; tr_typ typ) fields
    | _ -> tr.tr_typ_rec typ
  in
  let rec tr_pat p =
    match p.pat_desc with
    | PRecord fields ->
        let ps = List.map (snd |- tr.tr_pat) fields in
        let typ = tr.tr_typ p.pat_typ in
        {pat_desc=PTuple ps; pat_typ=typ}
    | _ -> tr.tr_pat_rec p
  in
  let tr_term t =
    match t.desc, t.typ with
    | Record fields, _ ->
        if is_mutable_record t.typ then
          unsupported "Mutable records";
        make_tuple @@ List.map (tr.tr_term -| snd) fields
    | Local(Decl_type decls, _), _ ->
        let tys = List.flatten_map (snd |- get_tdata) decls in
        let check (s,ty) =
          match ty with
          | TRecord _ -> List.mem s tys
          | _ -> false
        in
        if List.exists check decls then unsupported "recursive record types";
        tr.tr_term_rec t
    | Field(t,s), _ ->
        let fields = decomp_trecord t.typ in
        if is_mutable_record t.typ then
          unsupported "Mutable records";
        let t' = tr.tr_term t in
        make_proj (List.find_pos (fun _ (s',_) -> s = s') fields) t'
    | SetField _, _ -> unsupported "Mutable records"
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_pat <- tr_pat;
  tr.tr_typ <- tr_typ;
  tr.tr_term -| Trans.complete_precord

let record = Problem.map record_term



let rec is_simple_variant env typ =
  match typ with
  | TVariant(_,labels) -> List.for_all (snd |- (=) []) labels
  | TData s when List.mem_assoc s env -> is_simple_variant env @@ List.assoc s env
  | _ -> false

let rec position env c typ =
  match typ with
  | TVariant(_,labels) -> List.find_pos (fun _ (c',_) -> c = c') labels
  | TData s when List.mem_assoc s env -> position env c @@ List.assoc s env
  | _ -> invalid_arg "position"

let simple_variant_term =
  let tr = make_trans2 () in
  let tr_typ env typ =
    if is_simple_variant env typ then
      Ty.int
    else
      tr.tr2_typ_rec env typ
  in
  let tr_pat env p =
    match p.pat_desc with
    | PConstr(c, []) when is_simple_variant env p.pat_typ ->
        Pat.int @@ position env c p.pat_typ
    | _ -> tr.tr2_pat_rec env p
  in
  let tr_term env t =
    match t.desc with
    | Constr(c, []) when is_simple_variant env t.typ ->
        make_int @@ position env c t.typ
    | Local(Decl_type decls, _) ->
        tr.tr2_term_rec (decls@env) t
    | _ -> tr.tr2_term_rec env t
  in
  tr.tr2_term <- tr_term;
  tr.tr2_pat <- tr_pat;
  tr.tr2_typ <- tr_typ;
  tr.tr2_term []

(* TODO: support variants in refinement types *)
let simple_variant = Problem.map simple_variant_term


let abst_rec_record_term =
  let tr = make_trans2 () in
  let tr_term recs t =
    match t.desc with
    | Local(Decl_type decls, t1) ->
        let recs' =
          let tys = List.flatten_map (snd |- get_tdata) decls in
          let check (s,ty) =
            match ty with
            | TRecord _ -> List.exists (List.mem -$- tys) @@ get_tdata ty
            | _ -> false
          in
          List.map (fun (s,_) -> TData s) @@ List.filter check decls
        in
        let decls' = List.map (fun (s,ty) -> s, if List.mem (TData s) recs' then Ty.int else ty) decls in
        let t1' = tr.tr2_term (recs'@recs) t1 in
        make_local (Decl_type decls') t1'
    | Record fields when List.mem t.typ recs ->
        Flag.Encode.use_abst "Recursive records";
        let bindings =
          fields
          |> List.map snd
          |> List.map (tr.tr2_term recs)
          |> List.map (Pair.add_left new_var_of_term)
        in
        make_lets bindings randint_unit_term
    | SetField(t1,_,t2) when List.mem t1.typ recs ->
        Flag.Encode.use_abst "Recursive records";
        let t1' = tr.tr2_term recs t1 in
        let t2' = tr.tr2_term recs t2 in
        make_seq t1' t2'
    | Field(t1,_) when List.mem t1.typ recs ->
        Flag.Encode.use_abst "Recursive records";
        let t1' = tr.tr2_term recs t1 in
        let ty = tr.tr2_typ recs t.typ in
        Term.(seq t1' (rand ty))
    | Match(t1, pats) ->
        let t1',pats' =
          match tr.tr2_desc_rec recs t.desc with
          | Match(t',pats') -> t', pats'
          | _ -> assert false
        in
        let pats'' =
          let aux (p1,_) (p2,t) =
            let make x =
              let ty = tr.tr2_typ recs @@ Id.typ x in
              Id.set_typ x ty, make_rand_unit ty
            in
            let t' =
              get_bv_pat p1
              |> List.unique ~eq:Id.eq
              |> List.Set.diff ~eq:Id.eq -$- (get_bv_pat p2)
              |> List.map make
              |> make_lets -$- t
            in
            p2, t'
          in
          List.map2 aux pats pats'
        in
        make_match t1' pats''
    | _ -> tr.tr2_term_rec recs t
  in
  let tr_pat recs p =
    match p.pat_desc with
    | PRecord _ when List.mem p.pat_typ recs -> {pat_desc=PNondet; pat_typ=Ty.int}
    | _ -> tr.tr2_pat_rec recs p
  in
  let tr_typ recs ty =
    if List.mem ty recs then
      Ty.int
    else
      tr.tr2_typ_rec recs ty
  in
  tr.tr2_term <- tr_term;
  tr.tr2_typ <- tr_typ;
  tr.tr2_pat <- tr_pat;
  tr.tr2_term []

(* TODO: support records in refinement types *)
let abst_rec_record = Problem.map abst_rec_record_term


let abst_poly_comp_term =
  let tr = make_trans () in
  let tr_term t =
    let t' = tr.tr_term_rec t in
    match t'.desc with
    | BinOp((Eq | Lt | Gt | Leq | Geq), t1, t2) ->
        begin
          match elim_tattr t1.typ with
          | TBase _ -> t'
          | _ -> Term.(seqs [t1;t2] randb)
        end
    | _ -> t'
  in
  tr.tr_term <- tr_term;
  tr.tr_term
let abst_poly_comp = Problem.map abst_poly_comp_term


let option_term =
  let tr = make_trans () in
  let tr_term t =
    let t' = tr.tr_term_rec t in
    match t'.desc with
    | TNone -> make_none @@ get_opt_typ t'.typ
    | TSome t -> make_some t
    | _ -> t'
  in
  let tr_typ ty =
    match ty with
    | TApp(TOption, [ty']) -> opt_typ @@ tr.tr_typ ty'
    | _ -> tr.tr_typ_rec ty
  in
  let tr_pat p =
    let p' = tr.tr_pat_rec p in
    match p'.pat_desc with
    | PNone ->
        let ty = option_typ p.pat_typ in
        Pat.(tuple [const none_flag; __ ty])
    | PSome p ->
        Pat.(tuple [const some_flag; p])
    | _ -> p'
  in
  tr.tr_term <- tr_term;
  tr.tr_typ <- tr_typ;
  tr.tr_pat <- tr_pat;
  tr.tr_term
let option = Problem.map option_term



let recdata p =
  let open Flag.Encode.RecData in
  match !dest with
  | Tuple -> Encode_rec.trans p
  | Variant -> Encode_rec_variant.trans p
let list = Encode_list.trans


let pr s t =
  Debug.printf "##[Encode] %s: %a@." s Problem.print t

let all t =
  t
  |@> pr "INPUT"
  |> mutable_record
  |@> pr "MUTABLE_RECORD"
  |> record
  |@> pr "RECORD"
  |&!Flag.Method.ignore_exn_arg&> Trans_problem.ignore_exn_arg
  |@!Flag.Method.ignore_exn_arg&> pr "IGNORE_EXN_ARG"
  |&Flag.Encode.RecData.(!dest <> Variant)&> simple_variant
  |@Flag.Encode.RecData.(!dest <> Variant)&> pr "SIMPLE_VARIANT"
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


let typ_of f typ =
  typ
  |> Id.new_var
  |> make_var
  |> Problem.safety
  |> f
  |> Problem.term
  |> Syntax.typ
