open Util
open Syntax
open Type

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let get_fv = Syntax.get_fv

let occur_in x t =
  Id.mem x @@ get_fv t

(*** TERM CONSTRUCTORS ***)

let typ_result = TData "X"
let typ_event = Ty.(fun_ unit unit)
let typ_event' = Ty.(fun_ unit typ_result)
let typ_event_cps = Ty.(funs [unit; fun_ unit typ_result] typ_result)
let typ_exn = TData "exn"

let abst_var = Id.make (-1) "v" [] typ_unknown
let abst_var_int = Id.set_typ abst_var Ty.int
let abst_var_bool = Id.set_typ abst_var Ty.bool

let make_attr ?(attrs=const_attr) ts =
  let check a = List.for_all (fun {attr} -> List.mem a attr) ts in
  let make a = if check a then Some a else None in
  List.filter_map make attrs

let rec is_value t =
  match t.desc with
  | Const _ -> true
  | Var _ -> true
  | Fun _ -> true
  | Nil -> true
  | Cons(t1,t2) -> is_value t1 && is_value t2
  | Tuple ts -> List.for_all is_value ts
  | _ -> false

let has_safe_attr t = List.Set.subset safe_attr t.attr
let has_pure_attr t = List.Set.subset pure_attr t.attr
let add_attr attr t = {t with attr=attr::t.attr}
let add_attrs attrs t = List.fold_right add_attr attrs t
let add_comment s t = add_attr (AComment s) t
let add_id id t = add_attr (AId id) t
let remove_attr attr t = {t with attr = List.filter_out ((=) attr) t.attr}
let replace_id id1 id2 t = add_id id2 @@ remove_attr (AId id1) t

let end_of_definitions = {desc=End_of_definitions; typ=Ty.unit; attr=[]}
let unit_term = {desc=Const Unit; typ=Ty.unit; attr=const_attr}
let true_term = {desc=Const True; typ=Ty.bool; attr=const_attr}
let false_term = {desc=Const False; typ=Ty.bool; attr=const_attr}
let cps_result = {desc=Const CPS_result; typ=typ_result; attr=const_attr}
let fail_term = {desc=Event("fail",false); typ=typ_event; attr=[]}
let fail_term_cps = {desc=Event("fail",true); typ=typ_event_cps; attr=[]}
let make_bool b = if b then true_term else false_term
let make_bottom typ = {desc=Bottom; typ; attr=[]}
let make_event s = {desc=Event(s,false); typ=typ_event; attr=[]}
let make_event_cps s = {desc=Event(s,true); typ=typ_event_cps; attr=[]}
let make_var x = {desc=Var x; typ=Id.typ x; attr=pure_attr}
let make_int n = {desc=Const(Int n); typ=Ty.int; attr=pure_attr}
let make_string s = {desc=Const(String s); typ=TData "string"; attr=pure_attr}
let rec make_app t ts =
  let check typ1 typ2 =
    if not (Flag.Debug.check_typ => Type.can_unify typ1 typ2) then
      begin
        Format.eprintf "make_app:@[@ %a@ <=/=>@ %a@." Print.typ typ1 Print.typ typ2;
        Format.eprintf "fun: %a@." Print.term t;
        Format.eprintf "arg: %a@." Print.term @@ List.hd ts;
        assert false
      end
  in
  let ty = tfuns_to_tfun @@ elim_tattr t.typ in
  let attr =
    if List.mem TAPureFun @@ fst @@ decomp_tattr t.typ &&
         List.for_all has_pure_attr (t::ts)
    then
      pure_attr
    else
      []
  in
  match t.desc, ty, ts with
  | _, _, [] -> t
  | App(t1,ts1), TFun(x,typ), t2::ts2 ->
      check (Id.typ x) t2.typ;
      make_app {desc=App(t1,ts1@[t2]); typ; attr} ts2
  | App(t1,ts1), typ, t2::ts2 when typ = typ_unknown || is_tvar typ ->
      make_app {desc=App(t1,ts1@[t2]); typ; attr} ts2
  | _, TFun(x,typ), t2::ts ->
      check (Id.typ x) t2.typ;
      make_app {desc=App(t,[t2]); typ; attr} ts
  | _, typ, t2::ts when typ = typ_unknown || is_tvar typ ->
      make_app {desc=App(t,[t2]); typ; attr} ts
  | _ when not Flag.Debug.check_typ -> {desc=App(t,ts); typ=typ_unknown; attr}
  | _ ->
      Format.eprintf "Untypable(make_app): %a@." Print.term' {desc=App(t,ts);typ=typ_unknown; attr=[]};
      assert false
let make_app_raw t ts =
  let t' = make_app t ts in
  {t' with desc=App(t,ts)}
let make_local decl t =
  if decl = Decl_type [] || decl = Decl_let [] then
    t
  else
    let ts =
      match decl with
      | Decl_let defs -> List.map snd defs
      | Decl_type _ -> []
    in
    let attr = make_attr (t :: ts) in
    {desc=Local(decl,t); typ=t.typ; attr}
let make_let bindings t2 =
  make_local (Decl_let bindings) t2
(* remove unused bindings without changing semantics *)
(* DO NOT USE FOR MUTUAL RECURSIONS *)
let make_let_s bindings t2 =
  let bindings' = List.filter (fun (f,t1) -> occur_in f t2 || not (has_pure_attr t1) || List.exists (snd |- occur_in f) bindings) bindings in
  make_let bindings' t2
let make_lets_s bindings t2 =
  List.fold_right (make_let_s -| List.singleton) bindings t2
let make_let_type decls t2 =
  make_local (Decl_type decls) t2
let make_lets_type decls t2 =
  List.fold_right (make_let_type -| List.singleton) decls t2
let make_lets bindings t2 =
  List.fold_right (make_let -| List.singleton) bindings t2
let make_seq t1 t2 =
  if is_value t1 || has_pure_attr t1 then
    t2
  else
    make_let [Id.new_var ~name:"u" t1.typ, t1] t2
let make_ignore t =
  if t.typ = Ty.unit then
    t
  else
    make_seq t unit_term
let make_fail_unit loc =
  let t = make_app fail_term [unit_term] in
  match loc with
  | None -> t
  | Some loc -> add_attr (ALoc loc) t
let make_fail ?loc ?(force=false) typ =
  let t2 = make_bottom typ in
  if !Flag.Method.only_specified && not force then
    t2
  else
    make_seq (make_fail_unit loc) t2
let make_fun x t = {desc=Fun(x,t); typ=TFun(x,t.typ); attr=pure_attr}
let make_pure_fun x t = {desc=Fun(x,t); typ=pureTFun(x,t.typ); attr=pure_attr}
let make_funs = List.fold_right make_fun
let make_not t =
  match t.desc with
  | Const True -> false_term
  | Const False -> true_term
  | Not t -> t
  | _ -> {desc=Not t; typ=(TBase TBool); attr=make_attr[t]}
let make_and t1 t2 =
  if t1 = false_term then
    false_term
  else if t1 = true_term then
    t2
  else if t2 = true_term then
    t1
  else if t2 = false_term && has_safe_attr t1 then
    false_term
  else
    {desc=BinOp(And, t1, t2); typ=TBase TBool; attr=make_attr[t1;t2]}
let make_ands ts = List.fold_right make_and ts true_term
let make_or t1 t2 =
  if t1 = true_term then
    true_term
  else if t1 = false_term then
    t2
  else if t2 = false_term then
    t1
  else if t2 = true_term && has_safe_attr t1 then
    true_term
  else
    {desc=BinOp(Or, t1, t2); typ=TBase TBool; attr=make_attr[t1;t2]}
let make_ors ts = List.fold_right make_or ts false_term
let make_add t1 t2 =
  if t2.desc = Const (Int 0) then
    t1
  else if t1.desc = Const (Int 0) then
    t2
  else
    {desc=BinOp(Add, t1, t2); typ=TBase TInt; attr=make_attr[t1;t2]}
let make_sub t1 t2 =
  if t2.desc = Const (Int 0) then
    t1
  else
    {desc=BinOp(Sub, t1, t2); typ=TBase TInt; attr=make_attr[t1;t2]}
let make_mul t1 t2 =
  if t1.desc = Const (Int 0) && has_safe_attr t2 then
    make_int 0
  else if t2.desc = Const (Int 0) && has_safe_attr t1 then
    make_int 0
  else if t2.desc = Const (Int 1) then
    t1
  else if t1.desc = Const (Int 1) then
    t2
  else
    {desc=BinOp(Mult, t1, t2); typ=TBase TInt; attr=make_attr[t1;t2]}
let make_div t1 t2 = {desc=BinOp(Div, t1, t2); typ=TBase TInt; attr=make_attr[t1;t2]}
let make_neg t = make_sub (make_int 0) t
let make_if_ t1 t2 t3 =
  assert (Flag.Debug.check_typ => Type.can_unify t1.typ (TBase TBool));
  assert (Flag.Debug.check_typ => Type.can_unify t2.typ t3.typ);
  match t1.desc with
  | Const True -> t2
  | Const False -> t3
  | _ ->
      let typ =
        match has_pred t2.typ, has_pred t3.typ with
        | _, false -> t2.typ
        | false, true -> t3.typ
        | true, true ->
            if t2.typ <> t3.typ
            then warning @@ Format.asprintf " @[<hv 2>if-branches have different types@ %a and@ %a@]" Print.typ t2.typ Print.typ t3.typ;
            t2.typ
      in
      {desc=If(t1, t2, t3); typ; attr=make_attr[t1;t2;t3]}
let make_eq t1 t2 =
  assert (Flag.Debug.check_typ => Type.can_unify t1.typ t2.typ);
  match t1.desc, t2.desc with
  | Const c1, Const c2 -> make_bool (c1 = c2)
  | _ ->
      if t1.typ = Ty.unit && has_safe_attr t1 && has_safe_attr t2 then
        true_term
      else
        {desc=BinOp(Eq, t1, t2); typ=TBase TBool; attr=make_attr[t1;t2]}
let make_neq t1 t2 =
  make_not (make_eq t1 t2)
let make_lt t1 t2 =
  {desc=BinOp(Lt, t1, t2); typ=(TBase TBool); attr=make_attr[t1;t2]}
let make_gt t1 t2 =
  {desc=BinOp(Gt, t1, t2); typ=TBase TBool; attr=make_attr[t1;t2]}
let make_leq t1 t2 =
  {desc=BinOp(Leq, t1, t2); typ=TBase TBool; attr=make_attr[t1;t2]}
let make_geq t1 t2 =
  {desc=BinOp(Geq, t1, t2); typ=TBase TBool; attr=make_attr[t1;t2]}
let make_binop op =
  match op with
  | Eq -> make_eq
  | Lt -> make_lt
  | Gt -> make_gt
  | Leq -> make_leq
  | Geq -> make_geq
  | And -> make_and
  | Or -> make_or
  | Add -> make_add
  | Sub -> make_sub
  | Mult -> make_mul
  | Div -> make_div
let make_proj i t = {desc=Proj(i,t); typ=proj_typ i t.typ; attr=make_attr[t]}
let make_tuple ts =
  let attr = make_attr ts in
  {desc=Tuple ts; typ=make_ttuple@@List.map Syntax.typ ts; attr}
let make_fst t = {desc=Proj(0,t); typ=proj_typ 0 t.typ; attr=t.attr}
let make_snd t = {desc=Proj(1,t); typ=proj_typ 1 t.typ; attr=t.attr}
let make_pair t1 t2 = make_tuple [t1;t2]
let make_nil typ = {desc=Nil; typ=TApp(TList, [typ]); attr=const_attr}
let make_nil2 typ = {desc=Nil; typ; attr=const_attr}
let make_cons t1 t2 =
  assert (Flag.Debug.check_typ => Type.can_unify (TApp(TList, [t1.typ])) t2.typ);
  let attr = make_attr [t1;t2] in
  {desc=Cons(t1,t2); typ=t2.typ; attr}
let rec make_list ?typ ts =
  match ts, typ with
  | [], None -> make_nil typ_unknown
  | [], Some ty -> make_nil ty
  | [t1], _ -> make_cons t1 @@ make_nil t1.typ
  | t1::ts', _ -> make_cons t1 @@ make_list ts'
let make_pany typ = {pat_desc=PAny; pat_typ=typ}
let make_pvar x = {pat_desc=PVar x; pat_typ=Id.typ x}
let make_pconst t = {pat_desc=PConst t; pat_typ=t.typ}
let make_ppair p1 p2 = {pat_desc=PTuple[p1;p2]; pat_typ=make_tpair p1.pat_typ p2.pat_typ}
let make_ptuple ps = {pat_desc=PTuple ps; pat_typ=make_ttuple @@ List.map (fun p -> p.pat_typ) ps}
let make_pnil typ = {pat_desc=PNil; pat_typ=make_tlist typ}
let make_pnil2 typ = {pat_desc=PNil; pat_typ=typ}
let make_pcons p1 p2 = {pat_desc=PCons(p1,p2); pat_typ=p2.pat_typ}
let make_pwhen p t =
  if t.desc = Const True then
    p
  else
    match p.pat_desc with
    | PWhen(p', t') ->
        let cond = make_and t t' in
        {pat_desc=PWhen(p,cond); pat_typ=p.pat_typ}
    | _ -> {pat_desc=PWhen(p,t); pat_typ=p.pat_typ}
let make_label_aux info t = {desc=Label(info,t); typ=t.typ; attr=[]}
let make_label ?(label="") info t =
  t
  |> make_label_aux info
  |& (label <> "") &> make_label_aux (InfoString label)
let make_ref t = {desc=Ref t; typ=make_tref t.typ; attr=[]}
let make_deref t = {desc=Deref t; typ=ref_typ t.typ; attr=[]}
let make_setref r t = {desc=SetRef(r, t); typ=TBase TUnit; attr=[]}
let make_construct c ts typ =
  {desc=Constr(c,ts); typ; attr=[]}
let make_record fields typ =
  {desc=Record fields; typ; attr=[]}
let make_field ?ty t s =
  let typ =
    match ty with
    | None ->
        t.typ
        |> decomp_trecord
        |> List.assoc s
        |> snd
    | Some ty -> ty
  in
  {desc=Field(t,s); typ; attr=[]}
let make_event_unit s = make_app (make_event s) [unit_term]
let make_raise t typ = {desc=Raise t; typ; attr=[]}

let make_imply t1 t2 = make_or (make_not t1) t2

let make_eq_dec t1 t2 =
  assert (Flag.Debug.check_typ => Type.can_unify t1.typ t2.typ);
  let aux t =
    match t.desc with
    | Var x -> make_var x, Fun.id
    | _ ->
        let x = Id.new_var t.typ in
        make_var x, make_let [x,t]
  in
  let rec make t1 t2 =
    match t1.typ with
    | TBase _ -> make_eq t1 t2
    | TTuple xs ->
        let n = List.length xs in
        List.fromto 0 n
        |> List.map (fun i -> make (make_proj i t1) (make_proj i t2))
        |> List.fold_left make_and true_term
    | _ -> assert false
  in
  let t1',k1 = aux t1 in
  let t2',k2 = aux t2 in
  k1 @@ k2 @@ make t1' t2'

let is_length_var x = Id.name x = "List.length"
let make_length_var typ =
  let x = Id.make (-1) "l" [] typ in
  Id.make (-1) "List.length" [] (TFun(x, Ty.int))
let make_length t =
  {(make_app (make_var @@ make_length_var t.typ) [t]) with attr=safe_attr}

let make_module decls =
  let decls' = List.filter_out (fun decl -> decl = Decl_type [] || decl = Decl_let []) decls in
  let typ =
    let aux decl =
      match decl with
      | Decl_let defs -> List.map (fun (x,_) -> Id.name x, Id.typ x) defs
      | _ -> []
    in
    TModule(List.flatten_map aux decls')
  in
  {desc=Module decls'; typ; attr=[]}

let make_rand typ = {desc=Const(Rand(typ,false)); typ=Ty.(fun_ unit typ); attr=[]}

let rec make_rand_unit typ =
  match typ with
  | TBase TUnit -> unit_term
  | TBase TBool -> make_eq (make_rand_unit Ty.int) (make_int 0)
  | TTuple [] -> make_tuple []
  | TTuple tys -> make_tuple @@ List.map (Id.typ |- make_rand_unit) tys
  | TFun(x,ty) -> make_fun x @@ make_rand_unit ty
  | TAttr(_,ty) -> make_rand_unit ty
  | _ -> {desc=App(make_rand typ, [unit_term]); typ; attr=safe_attr}

let make_rand_cps typ =
  {desc=Const(Rand(typ,true)); typ=Ty.(funs [unit; fun_ typ typ_result] typ_result); attr=[]}

let make_randint_cps b =
  let attr = if b then [AAbst_under] else [] in
  {(make_rand_cps Ty.int) with attr}

let randint_term = make_rand Ty.int
let randint_unit_term = make_rand_unit Ty.int
let randbool_unit_term = make_rand_unit Ty.bool

let rec make_term typ =
  match elim_tattr typ with
  | TBase TUnit -> unit_term
  | TBase TBool -> true_term
  | TBase TInt -> make_int 0
  | TFun(x,typ) -> make_fun x (make_term typ)
  | TTuple xs -> make_tuple @@ List.map (make_term -| Id.typ) xs
  | TData "X" -> cps_result
  | TData "char" -> {desc=Const(Char '\000'); typ; attr=[]}
  | TData "string" -> {desc=Const(String ""); typ; attr=[]}
  | TData "float" -> {desc=Const(Float 0.); typ; attr=[]}
  | TApp(TList, [typ']) -> make_nil typ'
  | _ -> Format.eprintf "ERROR: %a@." Print.typ typ; assert false


let none_flag = false_term
let some_flag = true_term
(*
let none_flag = make_int 0
let some_flag = make_int 1
 *)
let opt_typ typ = TTuple [Id.new_var none_flag.typ; Id.new_var typ]
let get_opt_typ typ = snd_typ typ
let is_none t =
  match t.desc with
  | Tuple [t1;t2] -> t1 = none_flag
  | _ -> false
let decomp_some t =
  match t.desc with
  | Tuple [t1;t2] when t1 = some_flag -> Some t2
  | _ -> None
let make_none typ = make_pair none_flag (make_term typ)
let make_some t = make_pair some_flag t
let make_is_none t = make_eq (make_fst t) none_flag
let make_is_some t = make_not (make_is_none t)
let make_get_val t = make_snd t
let decomp_is_none t =
  match t.desc with
  | BinOp(Eq, {desc=Proj(0,t1)}, t2) when t2 = none_flag -> Some t1
  | _ -> None
let decomp_get_val t =
  match t.desc with
  | Proj(1, t) -> Some t
  | _ -> None

let is_randint_unit t =
  match t.desc with
  | App(t1, [{desc=Const Unit}]) -> t1.desc = randint_term.desc
  | _ -> false
let is_randbool_unit t =
  match t.desc with
  | BinOp((Eq|Leq|Geq|Lt|Gt), t, {desc=Const _})
  | BinOp((Eq|Leq|Geq|Lt|Gt), {desc=Const _}, t) -> is_randint_unit t
  | _ -> false






(*** AUXILIARY FUNCTIONS ***)

let is_base_var x = is_base_typ @@ Id.typ x
let is_fun_var x = is_fun_typ @@ Id.typ x

let decomp_var t =
  match t.desc with
  | Var x -> Some x
  | _ -> None
let is_var t = Option.is_some @@ decomp_var t

let is_fun t = [] <> fst @@ decomp_funs t

let is_const t =
  match t.desc with
  | Const _ -> true
  | _ -> false

let is_app t =
  match t.desc with
  | App _ -> true
  | _ -> false

let rec decomp_decls t =
  match t.desc with
  | Local(decl, t2) ->
      let decls,t2' = decomp_decls t2 in
      decl::decls, t2'
  | _ -> [], t

let rec decomp_lets t =
  match t.desc with
  | Local(Decl_let bindings, t2) ->
      let fbindings,t2' = decomp_lets t2 in
      bindings::fbindings, t2'
  | _ -> [], t

let rec decomp_and t =
  match t.desc with
  | BinOp(And, t1, t2) -> decomp_and t1 @@@ decomp_and t2
  | _ -> [t]

let decomp_assert t =
  match t.desc with
  | If(t1, {desc=Const Unit}, {desc=App({desc=Event("fail",_)}, [{desc=Const Unit}]); attr}) ->
      let loc = List.find_map_option (function ALoc loc -> Some loc | _ -> None) attr in
      Some (t1, loc)
  | _ -> None


let get_int = make_col [] (@@@)
let get_int_term t =
  match t.desc with
  | Const (Int n) -> [n]
  | _ -> get_int.col_term_rec t
let get_int_typ typ = []
let () = get_int.col_term <- get_int_term
let () = get_int.col_typ <- get_int_typ
let get_int t = List.unique @@ get_int.col_term t




let rec get_args ty =
  match elim_tattr ty with
  | TFun(x,typ) -> x :: get_args typ
  | _ -> []

let rec get_argvars ty =
  match elim_tattr ty with
  | TFun(x,typ) -> x :: get_argvars (Id.typ x) @ get_argvars typ
  | _ -> []

let rec get_argtyps ty =
  match elim_tattr ty with
  | TFun(x,typ) -> Id.typ x :: get_argtyps typ
  | _ -> []

let arg_num typ = List.length (get_args typ)


let is_poly_typ = make_col false (||)

let is_poly_typ_typ typ =
  match elim_tattr typ with
  | TVar({contents=None},_) -> true
  | _ -> is_poly_typ.col_typ_rec typ

let () = is_poly_typ.col_typ <- is_poly_typ_typ
let is_poly_typ = is_poly_typ.col_typ


let rename,rename_pat =
  let tr = make_trans2 () in
  let tr_var map x =
    match Id.assoc_option x map with
    | None -> x
    | Some y -> Id.set_typ y @@ Id.typ x
  in
  tr.tr2_var <- tr_var;
  tr.tr2_typ <- Fun.snd;
  tr.tr2_term, tr.tr2_pat


let subst = make_trans2 ()

(* [x |-> t], [t/x] *)
(* fv = FV(t) *)
(* capture-avoiding only when `fast = false` *)
let subst_term (x,t,fv,fast as arg) t' =
  let rename map t = List.fold_left (fun t (y,y') -> subst.tr2_term_rec (y, make_var y', None, fast) t) t map in
  match t'.desc, fv with
  | Var y, _ when Id.(x = y) -> t
  | Fun _, _ when fast -> subst.tr2_term_rec arg t'
  | Fun(y, t1), _ when Id.(x = y) -> t'
  | Fun(y, t1), Some fv when Id.mem y fv ->
      let y' = Id.new_var_id y in
      let desc = subst.tr2_desc_rec arg @@ Fun(y', rename [y,y'] t1) in
      {t' with desc}
  | Local _, _ when fast -> subst.tr2_term_rec arg t'
  | Local(Decl_let bindings, t2), _ when Id.mem_assoc x bindings -> t'
  | Local(Decl_let bindings, t2), Some fv when List.exists (Id.mem_assoc -$- bindings) fv ->
      let map =
        bindings
        |> List.filter_map (fun (y,_) -> if Id.mem y fv then Some y else None)
        |> List.map (Pair.add_right Id.new_var_id)
      in
      let bindings' = List.map (fun (f,t) -> List.assoc_default ~eq:Id.eq f f map, rename map t) bindings in
      let t2' = rename map t2 in
      let desc = subst.tr2_desc_rec arg @@ Local(Decl_let bindings', t2') in
      {t' with desc}
  | Match _, _ when fast -> subst.tr2_term_rec arg t'
  | Match(t1,pats), _ ->
      let pats_renamed =
        let aux (p,t) =
          let bv = get_bv_pat p in
          match fv with
          | None -> p, t
          | Some fv ->
              let bv' = List.Set.inter ~eq:Id.eq bv fv in
              let map = List.map (Pair.add_right Id.new_var_id) bv' in
              rename_pat map p, rename map t
        in
        List.map aux pats
      in
      let aux (p,t1) =
        let xs = get_bv_pat p in
        let t1' =
          if List.exists (Id.same x) xs then
            t1
          else
            subst.tr2_term arg t1
        in
        p, t1'
      in
      let desc = Match(subst.tr2_term arg t1, List.map aux pats_renamed) in
      {t' with desc}
  | Module decls, Some fv -> unsupported "subst"
  | Module decls, _ ->
      let rec aux decls =
        match decls with
        | [] -> []
        | Decl_let bindings::_ when Id.mem_assoc x bindings -> decls
        | decl::decls' -> subst.tr2_decl arg decl :: aux decls'
      in
      let desc = Module (aux decls) in
      {t' with desc}
  | _ -> subst.tr2_term_rec arg t'


let subst_int = make_trans2 ()

let subst_int_term (n,t) t' =
  match t'.desc with
  | Const (Int m) when n = m -> t
  | Const (Int m) -> make_add t @@ make_int (m-n)
  | _ -> subst_int.tr2_term_rec (n,t) t'

let () = subst_int.tr2_term <- subst_int_term
let subst_int n t t' = subst_int.tr2_term (n,t) t'


let subst_map = make_trans2 ()

let subst_map_term map t =
  match t.desc with
  | Var y -> if Id.mem_assoc y map then Id.assoc y map else t
  | Fun(y, t1) ->
      let map' = List.filter_out (fst |- Id.same y) map in
      let t1' = subst_map.tr2_term map' t1 in
      make_fun y t1'
  | Local(Decl_let bindings, t2) ->
      let map' = List.filter (fun (x,_) -> not (List.exists (fst |- Id.same x) bindings)) map in
      let bindings' = List.map (Pair.map_snd @@ subst_map.tr2_term map') bindings in
      let t2' = subst_map.tr2_term map' t2 in
      make_let bindings' t2'
  | Match(t1,pats) -> (* TODO: fix *)
      let aux (pat,t1) = pat, subst_map.tr2_term map t1 in
      {desc=Match(subst_map.tr2_term map t1, List.map aux pats); typ=t.typ; attr=[]}
  | _ -> subst_map.tr2_term_rec map t

let () = subst_map.tr2_term <- subst_map_term
let subst_decl_map map decl =
  if map = [] then
    decl
  else
    subst_map.tr2_decl map decl
let subst_map map t =
  if map = [] then
    t
  else
    subst_map.tr2_term map t


let () = subst.tr2_term <- subst_term
let subst_type ?(fast=false) x t typ = subst.tr2_typ (x,t,None,fast) typ
let subst_type_var x y typ = subst_type x (make_var y) typ
let subst_decl ?(fast=false) x t decl = subst.tr2_decl (x,t,None,fast) decl
let subst ?(rename_if_captured=false) ?(fast=false) x t1 t2 =
  let fv = if rename_if_captured then Some (get_fv t1) else None in
  subst.tr2_term (x,t1,fv,fast) t2
let subst_var ?(fast=false) x y t = subst ~fast x (make_var y) t
let subst_var_map map t =
  if map = [] then
    t
  else
    subst_map (List.map (Pair.map_snd make_var) map) t

(* TODO: subst_var_without_typ must be a derivative of subst_var_map_without_typ *)
let subst_var_without_typ =
  let tr = make_trans2 () in
  let tr_desc (x,y) desc =
    match desc with
    | Var z when Id.(x = z) -> Var (Id.set_typ y (Id.typ z))
    | Fun(z, t1) when Id.(x = z) -> desc
    | Local(Decl_let bindings, t2) when List.exists (fst |- Id.same x) bindings -> desc
    | Local(Decl_let bindings, t2) ->
        let aux (f,t1) = tr.tr2_var (x,y) f, tr.tr2_term (x,y) t1 in
        let bindings' = List.map aux bindings in
        let t2' = tr.tr2_term (x,y) t2 in
        Local(Decl_let bindings', t2')
    | Match(t1,pats) ->
        let aux (pat,t1) =
          let xs = get_bv_pat pat in
          if List.exists (Id.same x) xs
          then pat, t1
          else pat, tr.tr2_term (x,y) t1
        in
        Match(tr.tr2_term (x,y) t1, List.map aux pats)
    | _ -> tr.tr2_desc_rec (x,y) desc
  in
  tr.tr2_desc <- tr_desc;
  Fun.curry tr.tr2_term
let subst_var_map_without_typ map t =
  List.fold_right (Fun.uncurry subst_var_without_typ) map t


let make_nonrec_let_s bindings t2 =
  let map =
    bindings
    |> List.filter (fun (f,t) -> Id.mem f @@ get_fv t)
    |> List.map fst
    |> List.map (Pair.add_right Id.new_var_id)
  in
  let bindings' = List.map (Pair.map_fst (fun x -> List.assoc_default x x map)) bindings in
  make_let_s bindings' @@ subst_var_map map t2
let make_nonrec_lets_s bindings t2 =
  List.fold_right (make_nonrec_let_s -| List.singleton) bindings t2

let make_match ?typ t1 pats =
  match pats with
  | [] ->
      begin
        match typ with
        | None -> invalid_arg "Term_util.make_match"
        | Some ty -> make_bottom ty
      end
  | (_,t)::_ ->
      let pats' =
        let rec match_any p =
          match p.pat_desc with
          | PAny -> true
          | PVar _ -> true
          | PAlias(p1,_) -> match_any p1
          | PConst {desc=Const Unit} -> true
          | POr(p1,p2) -> match_any p1 || match_any p2
          | PWhen(p,c) -> match_any p && c.desc = Const True
          | _ -> false
        in
        let aux (p,t) acc =
          (p,t) :: (if match_any p then [] else acc)
        in
        List.fold_right aux pats []
      in
      match pats' with
      | [{pat_desc=PAny}, t2] -> make_seq t1 t2
      | [{pat_desc=PVar x}, t2] ->
          if Id.mem x @@ get_fv t1 then
            let x' = Id.new_var_id x in
            make_let_s [x',t1] @@ subst_var x x' t2
          else
            make_let_s [x,t1] t2
      | _ -> {desc=Match(t1,pats'); typ=t.typ; attr=[]}
let make_single_match ?(total=false) t1 p t2 =
  let rec is_total p =
    match p.pat_desc with
    | PAny -> true
    | PVar _ -> true
    | PTuple ps -> List.for_all is_total ps
    | PRecord fields -> List.for_all (snd |- is_total) fields
    | PAlias(p, _) -> is_total p
    | _ -> false
  in
  if total || is_total p
  then make_match t1 [p, t2]
  else make_match t1 [p, t2; make_pany p.pat_typ, make_fail t2.typ]
let make_trywith t x pats =
  if has_safe_attr t then
    t
  else
    let handler = make_fun x @@ make_match (make_var x) pats in
    {desc=TryWith(t, handler); typ=t.typ; attr=[]}
let make_trywith_simple t handler = {desc=TryWith(t, handler); typ=t.typ; attr=[]}




let get_tapred typ =
  match typ with
  | TAttr(attrs, _) ->
      Option.of_list @@ List.filter_map (function TAPred(x,ps) -> Some (x,ps) | _ -> None) attrs
  | _ -> None

let add_tapred x ps typ =
  let attrs',typ' =
    match get_tapred typ, typ with
    | None, _ -> [TAPred(x,ps)], typ
    | Some(x',ps'), TAttr(attrs, typ') ->
        let attrs' = List.filter (function TAPred _ -> false | _ -> true) attrs in
        let ps' = (List.map (subst_var x' x) ps') @ ps in
        TAPred(x,ps')::attrs', typ'
    | _ -> assert false
  in
  _TAttr attrs' typ'



let max_pat_num = make_col 0 max

let max_pat_num_term t =
  match t.desc with
  | Match(t,pats) ->
      let m = max (List.length pats) (max_pat_num.col_term t) in
      let aux acc (_,t) = max acc (max_pat_num.col_term t)  in
      List.fold_left aux m pats
  | _ -> max_pat_num.col_term_rec t

let () = max_pat_num.col_term <- max_pat_num_term
let max_pat_num = max_pat_num.col_term





let rec same_const c1 c2 =
  match c1,c2 with
  | Rand(typ1, b1), Rand(typ2, b2) -> b1 = b2 && same_shape typ1 typ2
  | _ -> c1 = c2
and same_term t1 t2 = same_desc t1.desc t2.desc
and same_desc t1 t2 =
  let (===) = same_term in
  match t1,t2 with
  | Const c1, Const c2 -> same_const c1 c2
  | Var x, Var y -> Id.(x = y)
  | Fun(x,t1), Fun(y,t2) -> t1 === subst_var y x t2
  | App(t1,ts1), App(t2,ts2) -> List.eq ~eq:same_term (t1::ts1) (t2::ts2)
  | If(t11,t12,t13), If(t21,t22,t23) -> t11 === t21 && t12 === t22 && t13 === t23
  | Local(Decl_let bindings1,t1), Local(Decl_let bindings2,t2) ->
     let eq (f,t1) (g,t2) = Id.(f = g) && t1 === t2 in
     List.eq ~eq bindings1 bindings2 && t1 === t2
  | BinOp(op1,t11,t12), BinOp(op2,t21,t22) -> op1 = op2 && t11 === t21 && t12 === t22
  | Not t1, Not t2 -> t1 === t2
  | Event(s1,b1), Event(s2,b2) -> s1 = s2 && b1 = b2
  | Record _, Record _ -> unsupported "same_term 2"
  | Field _, Field _ -> unsupported "same_term 3"
  | SetField _, SetField _ -> unsupported "same_term 4"
  | Nil, Nil -> true
  | Cons(t11,t12), Cons(t21,t22) -> t11 === t21 && t12 === t22
  | Constr(c1, ts1), Constr(c2, ts2) -> c1 = c2 && List.for_all2 (===) ts1 ts2
  | Match(t1,pats1), Match(t2,pats2) ->
      let eq (pat1,t1) (pat2,t2) = pat1 = pat2 && t1 === t2 in
      t1 === t2 && List.eq ~eq pats1 pats2
  | Raise t1, Raise t2 -> t1 === t2
  | TryWith(t11,t12), TryWith(t21,t22) -> t11 === t21 && t12 === t22
  | Tuple ts1, Tuple ts2 -> List.eq ~eq:same_term ts1 ts2
  | Proj(i,t1), Proj(j,t2) -> i = j && t1 === t2
  | Bottom, Bottom -> true
  | Label _, Label _ -> unsupported "same_term 11"
  | _ -> false

and same_info i1 i2 = unsupported "same_term"
and same_type_kind k1 k2 = unsupported "same_term"

and same_typed_pattern p1 p2 = same_pattern p1.desc p2.desc
and same_pattern p1 p2 = unsupported "same_term"

let same_term' t1 t2 = try same_term t1 t2 with _ -> false




let merge_tattrs attr1 attr2 =
  let attrs =
    let eq x y =
      match x, y with
      | TAPred _, TAPred _ -> true
      | TAPureFun,  TAPureFun -> true
      | TARefPred _, TARefPred _ -> true
      | TAId(s1,_), TAId(s2,_) -> s1 = s2
      | _ -> false
    in
    List.classify ~eq (List.Set.union attr1 attr2)
  in
  let merge a1 a2 =
    match a1 with
    | None -> Some a2
    | Some a1 ->
        match a1, a2 with
        | TAPred(x1,ps1), TAPred(x2,ps2) ->
            let merge_preds ps1 ps2 =
              let aux p ps =
                if List.exists (same_term p) ps
                then ps
                else p::ps
              in
              List.fold_right aux ps1 ps2
            in
            let ps2' = List.map (subst_var x2 x1) ps2 in
            Some (TAPred(x1, merge_preds ps1 ps2'))
        | TARefPred(x1,p1), TARefPred(x2,p2) ->
            let p2' = subst_var x2 x1 p2 in
            let p = if same_term p1 p2' then p1 else make_and p1 p2' in
            Some (TARefPred(x1, p))
        | TAPureFun, TAPureFun -> Some TAPureFun
        | TAId _, TAId _ ->
            warning "merge TAId";
            None
        | _ -> assert false
  in
  List.filter_map (List.fold_left merge None) attrs

let rec merge_typ typ1 typ2 =
  match typ1,typ2 with
  | TVar({contents=Some typ1},_), typ2
  | typ1, TVar({contents=Some typ2},_) -> merge_typ typ1 typ2
  | TVar({contents=None},_), _ -> typ2
  | _, TVar({contents=None},_) -> typ1
  | _ when typ1 = typ_unknown -> typ2
  | _ when typ2 = typ_unknown -> typ1
  | TVarLazy _, _
  | _, TVarLazy _ -> typ1
  | TBase b1, TBase b2 when b1 = b2 -> TBase b1
  | TAttr(attr1,typ1), TAttr(attr2,typ2) ->
      _TAttr (merge_tattrs attr1 attr2) (merge_typ typ1 typ2)
  | TAttr(attr, typ'), typ
  | typ, TAttr(attr, typ') -> _TAttr attr (merge_typ typ typ')
  | TFuns(xs1,typ1), TFuns(xs2,typ2) ->
      let xs = List.map2 (fun x1 x2 -> Id.new_var ~name:(Id.name x1) @@ merge_typ (Id.typ x1) (Id.typ x2)) xs1 xs2 in
      TFuns(xs, merge_typ typ1 typ2)
  | TFun(x1,typ1), TFun(x2,typ2) ->
      let x_typ = merge_typ (Id.typ x1) (Id.typ x2) in
      let x = Id.new_var ~name:(Id.name x1) x_typ in
      let typ = merge_typ (subst_type_var x1 x typ1) (subst_type_var x2 x typ2) in
      TFun(x, typ)
  | TApp(c1,typs1), TApp(c2,typs2) ->
      assert (c1 = c2);
      TApp(c1, List.map2 merge_typ typs1 typs2)
  | TTuple xs1, TTuple xs2 ->
      let aux x1 x2 xs =
        let x = Id.set_typ x1 @@ merge_typ (Id.typ x1) (Id.typ x2) in
        List.map (Id.map_typ @@ subst_type_var x2 x1) @@ x::xs
      in
      TTuple (List.fold_right2 aux xs1 xs2 [])
  | TData _, TData _ -> assert (typ1 = typ2); typ1
  | TVariant(poly1,labels1), TVariant(poly2,labels2) ->
      assert (poly1 = poly2);
      let labels = List.map2 (fun (s1,typs1) (s2,typs2) -> assert (s1=s2); s1, List.map2 merge_typ typs1 typs2) labels1 labels2 in
      TVariant(poly1, labels)
  | TRecord fields1, TRecord fields2 ->
      let fields = List.map2 (fun (s1,(f1,typ1)) (s2,(f2,typ2)) -> assert (s1=s2 && f1=f2); s1, (f1, merge_typ typ1 typ2)) fields1 fields2 in
      TRecord fields
  | _ -> Format.eprintf "typ1:%a, typ2:%a@." Print.typ typ1 Print.typ typ2; assert false

let make_if t1 t2 t3 =
  assert (Flag.Debug.check_typ => Type.can_unify t1.typ Ty.bool);
  if Flag.Debug.check_typ && not @@ Type.can_unify t2.typ t3.typ then
    (Format.eprintf "%a <=/=> %a@." Print.typ t2.typ Print.typ t3.typ;
     assert false);
  match t1.desc with
  | Const True -> t2
  | Const False -> t3
  | _ when has_safe_attr t2 && same_term' t2 t3 -> t2
  | _ when t2.desc = Const True && t3.desc = Const False -> t1
  | _ when same_term t2 t3 -> make_seq t1 t2
  | _ -> {desc=If(t1, t2, t3); typ=merge_typ t2.typ t3.typ; attr=make_attr[t1;t2;t3]}
let make_assert ?loc ?(force=false) t =
  if !Flag.Method.only_specified && not force then
    unit_term
  else
    make_if t unit_term (make_fail_unit loc)
let make_assume t1 t2 = make_if t1 t2 (make_bottom t2.typ)
let make_br t2 t3 = make_if randbool_unit_term t2 t3
let make_brs ts =
  if ts = [] then invalid_arg "Term_util.make_brs";
  List.reduce_right make_br ts

let rec get_top_funs acc = function
  | {desc=Local(Decl_let defs, t)} ->
      let acc' = List.fold_left (fun acc (f,_) -> f::acc) acc defs in
      get_top_funs acc' t
  | _ -> acc
let get_top_funs = get_top_funs []

let rec get_top_rec_funs acc = function
  | {desc=Local(Decl_let defs, t)} ->
      let acc' = List.fold_left (fun acc (f,_) -> f::acc) acc defs in
      get_top_rec_funs acc' t
  | _ -> acc
let get_top_rec_funs = get_top_rec_funs []


let has_no_effect =
  let col = make_col true (&&) in
  let col_desc desc =
    match desc with
    | Const _ -> true
    | Var _ -> true
    | Fun _ -> true
    | App _ -> false
    | Local(Decl_let bindings,t) -> col.col_term t && List.for_all (snd |- col.col_term) bindings
    | Field _ -> false
    | SetField _ -> false
    | Raise _ -> false
    | Bottom -> false
    | Ref _ -> false
    | Deref _ -> false
    | SetRef _ -> false
    | _ -> col.col_desc_rec desc
  in
  col.col_desc <- col_desc;
  col.col_term


let is_const_or_var t = is_const t || is_var t

let rec is_simple_aexp t =
  if elim_tattr t.typ <> Ty.int then
    false
  else
    match t.desc with
    | Const _ -> true
    | Var _ -> true
    | BinOp(_, t1, t2) -> is_simple_aexp t1 && is_simple_aexp t2
    | _ -> false

and is_simple_bexp t =
  if elim_tattr t.typ <> Ty.bool then
    false
  else
    match t.desc with
    | Const _ -> true
    | Var _ -> true
    | BinOp(_, t1, t2) ->
        is_simple_bexp t1 && is_simple_bexp t2 ||
        is_simple_aexp t1 && is_simple_aexp t2 ||
        is_const_or_var t1 && is_const_or_var t2
    | Not t -> is_simple_bexp t
    | _ -> false





let rec var_name_of_term t =
  match t.desc with
  | Bottom -> "bot"
  | Var x -> Id.name x
  | Local(_,t) -> var_name_of_term t
  | Tuple([]) -> "nil"
  | Tuple(ts) -> String.join "__" @@ List.map var_name_of_term ts
  | Proj(i,t) ->
      let n = tuple_num t.typ in
      let names = String.nsplit (var_name_of_term t) "__" in
      if n = Some (List.length names) && List.nth names i <> ""
      then List.nth names i
      else var_name_of_term t ^ "_" ^ string_of_int i
  | App({desc=Var f},_) -> "r" ^ "_" ^ Id.name f
  | _ -> Type.var_name_of @@ elim_tattr t.typ

let new_var_of_term t = Id.new_var ~name:(var_name_of_term t) t.typ


let rec var_name_of_pattern p =
  match p.pat_desc with
  | PAny -> "u"
  | PVar x -> Id.name x
  | PTuple [] -> "nil"
  | PTuple ps -> String.join "__" @@ List.map var_name_of_pattern ps
  | PNil -> "nil"
  | _ -> Type.var_name_of p.pat_typ

let new_var_of_pattern p = Id.new_var ~name:(var_name_of_pattern p) p.pat_typ


let make_let' t1 make_t2 =
  let x = new_var_of_term t1 in
  make_let [x,t1] @@ make_t2 x


let col_same_term = make_col2 [] (@@@)

let col_same_term_term t1 t2 =
  let b = try same_term t1 t2 with _ -> false in
  if b then [t2] else col_same_term.col2_term_rec t1 t2

let () = col_same_term.col2_term <- col_same_term_term
let col_same_term = col_same_term.col2_term



let col_info_id = make_col [] (@@@)

let col_info_id_desc desc =
  match desc with
  | Label(InfoId x, t) -> x::col_info_id.col_term t
  | _ -> col_info_id.col_desc_rec desc

let () = col_info_id.col_desc <- col_info_id_desc
let col_info_id = col_info_id.col_term



(* [t1 |-> x] *)
let subst_rev =
  let tr = make_trans2 () in
  let tr_term (t1,fv,x) t2 =
    if same_term' t1 t2 || t1 = t2 then
      make_var x
    else
      match t2.desc with
      | Fun(x, _) when Id.mem x fv -> t2
      | Match(t1,pats) when List.exists (fst |- get_bv_pat |- List.Set.inter ~eq:Id.eq fv |- List.is_empty |- not) pats ->
          let desc = Match(tr.tr2_term_rec (t1,fv,x) t2, pats) in
          {t2 with desc}
      | _ -> tr.tr2_term_rec (t1,fv,x) t2
  in
  tr.tr2_term <- tr_term;
  fun ?(check_capture=false) t1 x t2 ->
    let fv = if check_capture then get_fv t1 else [] in
    tr.tr2_term (t1,fv,x) t2


(* replace t1 with t2 in t3 *)
let replace_term t1 t2 t3 =
  let x = Id.new_var t1.typ in
  subst x t2 @@ subst_rev t1 x t3


(* for debug *)
let is_id_unique t =
  let bv = get_bv t in
  let rec check xs =
    match xs with
    | [] -> true
    | x::xs' ->
        if Id.mem x xs'
        then (Format.eprintf "%a" Id.print x; false)
        else check xs'
  in
  check bv
(*
  List.length bv = List.length (List.unique ~cmp:Id.same bv)
*)



let rec is_bottom_def f t =
  let xs,t = decomp_funs t in
  match xs, t.desc with
  | _::_, App({desc=Var g},ts) ->
      Id.(f = g) && List.for_all has_no_effect ts
  | _ -> false

let rec decomp_bexp t =
  match t.desc with
  | BinOp((And|Or), t1, t2) -> decomp_bexp t1 @ decomp_bexp t2
  | Not t1 -> decomp_bexp t1
  | _ -> [t]

let var_of_term t =
  match t.desc with
  | Var x -> x
  | _ -> invalid_arg "var_of_term"

let int_of_term t =
  match t.desc with
  | Const (Int n) -> n
  | _ -> invalid_arg "int_of_term"

let bool_of_term t =
  match t.desc with
  | Const True -> true
  | Const False -> false
  | _ -> invalid_arg "bool_of_term"

let pair_of_term t =
  match t.desc with
  | Tuple [t1; t2] -> t1, t2
  | _ -> invalid_arg "pair_of_term"

let tuple_of_term t =
  match t.desc with
  | Tuple ts -> ts
  | _ -> invalid_arg "tuple_of_term"

let rec list_of_term t =
  match t.desc with
  | Nil -> []
  | Cons(t1,t2) -> t1 :: list_of_term t2
  | _ -> invalid_arg "list_of_term"


(* not capture-avoiding *)
let subst_tdata,subst_tdata_typ =
  let tr = make_trans2 () in
  let tr_typ (s,ty1) ty2 =
    match ty2 with
    | TData s' when s = s' -> ty1
    | _ -> tr.tr2_typ_rec (s,ty1) ty2
  in
  tr.tr2_typ <- tr_typ;
  Fun.curry tr.tr2_term, Fun.curry tr.tr2_typ

(* not capture-avoiding *)
let subst_tdata_map,subst_tdata_typ_map =
  let tr = make_trans2 () in
  let tr_typ map ty =
    match ty with
    | TData s when List.mem_assoc s map -> List.assoc s map
    | _ -> tr.tr2_typ_rec map ty
  in
  tr.tr2_typ <- tr_typ;
  tr.tr2_term, tr.tr2_typ

(* capture-avoiding *)
let subst_tdata_ca =
  let tr = make_trans2 () in
  let tr_desc (s,ty) desc =
    match desc with
    | Local(Decl_type decls, _) when List.mem_assoc s decls -> desc
    | Module decls ->
        let _,decls_rev =
          let aux (b,acc_rev) decl =
            let b',decl' =
              if b then
                true, decl
              else
                match decl with
                | Decl_type decls when List.mem_assoc s decls -> true, decl
                | _ -> false, tr.tr2_decl (s,ty) decl
            in
            b', decl'::acc_rev
          in
          List.fold_left aux (false,[]) decls
        in
        Module (List.rev decls_rev)
    | _ -> tr.tr2_desc_rec (s,ty) desc
  in
  let tr_typ (s,ty1) ty2 =
    match ty2 with
    | TData s' when s = s' -> ty1
    | _ -> tr.tr2_typ_rec (s,ty1) ty2
  in
  tr.tr2_desc <- tr_desc;
  tr.tr2_typ <- tr_typ;
  Fun.curry tr.tr2_term

let alpha_rename_pred_share =
  let fld = make_fold_tr () in
  let find x env =
    if List.mem_assoc x env then
      env, List.assoc x env
    else
      let y = Id.new_int() in
      (x,y)::env, y
  in
  let fld_typ env ty =
    match ty with
    | TAttr(attr,ty1) ->
        let env,ty1' = fld.fld_typ env ty1 in
        let env, attr' =
          let aux a (env,acc) =
            let env',a' =
              match a with
              | TAId(s,x) when s = label_pred_share ->
                  let env',y = find x env in
                  env', TAId(s,y)
              | TAPredShare x ->
                  let env',y = find x env in
                  env', TAPredShare y
              | _ -> env, a
            in
            env', a'::acc
          in
          List.fold_right aux attr (env,[])
        in
        env, _TAttr attr' ty1'
    | _ -> fld.fld_typ_rec env ty
  in
  fld.fld_typ <- fld_typ;
  fld.fld_typ [] |- snd

let subst_tdata_with_copy =
  let tr = make_trans2 () in
  let tr_typ (s,ty1) ty2 =
    match ty2 with
    | TData s' when s = s' -> alpha_rename_pred_share ty1
    | _ -> tr.tr2_typ_rec (s,ty1) ty2
  in
  tr.tr2_typ <- tr_typ;
  fun s ty' t -> tr.tr2_term (s,ty') t

let rec get_last_definition prefix env def t =
  match t.desc with
  | Local(Decl_let bindings, t2) ->
      get_last_definition prefix env (Some (env,bindings)) t2
  | Local(Decl_type decls, t2) ->
      let env' = List.map (fun (s,_) -> s, TData (prefix ^ s)) decls @ env in
      get_last_definition prefix env' def t2
  | Module decls -> unsupported "get_last_definition"
  | Fun _ -> []
  | _ ->
      match def with
      | None -> []
      | Some (env', [m, {desc=Module decls}]) ->
          List.fold_right make_local decls end_of_definitions
          |> get_last_definition (Id.name m ^ "." ^ prefix) env None
      | Some (env', bindings) -> List.map (Pair.map_fst @@ Id.map_typ (subst_tdata_typ_map env')) bindings
let get_last_definition t = get_last_definition "" [] None t

let rec get_body t =
  match t.desc with
  | Local(_, t2) -> get_body t2
  | _ -> t

let count_occurrence x t =
  List.count Id.((=) x) @@ get_fv ~eq:(fun _ _ -> false) t

let get_id t =
  try
    List.find_map (function AId n -> Some n | _ -> None) t.attr
  with Not_found -> invalid_arg "get_id"
let get_id_option t =
   Option.try_with (fun () -> get_id t) ((=) @@ Invalid_argument "get_id")


let get_id_map = make_col2 () (Fun.const2 ())
let get_id_map_term map t =
  get_id_map.col2_term_rec map t;
  Hashtbl.add map (get_id t) t
let get_id_map_typ map typ = ()
let () = get_id_map.col2_term <- get_id_map_term
let () = get_id_map.col2_typ <- get_id_map_typ
let get_id_map t =
  let map = Hashtbl.create 0 in
  get_id_map.col2_term map t;
  map



let rec decomp_type_decls t =
  match t.desc with
  | Local(Decl_type tys, t1) ->
      let decls,t1' = decomp_type_decls t1 in
      tys::decls, t1'
  | _ -> [], t

let rec decomp_prog t =
  match t.desc with
  | Local(Decl_let bindings, t') ->
      let defs,main = decomp_prog t' in
      bindings::defs, main
  | _ -> [], t

let from_fpat_const c =
  match c with
  | Fpat.Const.Unit -> unit_term
  | Fpat.Const.True -> true_term
  | Fpat.Const.False -> false_term
  | Fpat.Const.Int n -> make_int n
  | _ -> unsupported "Term_util.from_fpat_const"

let from_fpat_idnt x =
  Id.from_string (Fpat.Idnt.string_of x) typ_unknown

let decomp_binop t =
  match t with
  | Fpat.Term.Const c ->
      begin
      match c with
      | Fpat.Const.Lt _ -> Some make_lt
      | Fpat.Const.Gt _ -> Some make_gt
      | Fpat.Const.Leq _ -> Some make_leq
      | Fpat.Const.Geq _ -> Some make_geq
      | Fpat.Const.Eq _ -> Some make_eq
      | Fpat.Const.Add _ -> Some make_add
      | Fpat.Const.Sub _ -> Some make_sub
      | Fpat.Const.Mul _ -> Some make_mul
      | Fpat.Const.Div _ -> Some make_div
      | Fpat.Const.Neq _ -> Some (fun x y -> make_not @@ make_eq x y)
      | _ -> None
      end
  | _ -> None

let rec decomp_list t =
  match t.desc with
  | Nil -> Some []
  | Cons(t1, t2) -> Option.map (List.cons t1) @@ decomp_list t2
  | _ -> None
let is_list_literal t = None <> decomp_list t

let rec from_fpat_term = function
  | Fpat.Term.Const c -> from_fpat_const c
  | Fpat.Term.Var x -> make_var (from_fpat_idnt x)
  | Fpat.Term.App(Fpat.Term.App(f, t1), t2) when Option.is_some @@ decomp_binop f ->
      let make = Option.get @@ decomp_binop f in
      let t1' = from_fpat_term t1 in
      let t2' = from_fpat_term t2 in
      make t1' t2'
  | Fpat.Term.App(Fpat.Term.Const Fpat.Const.Not, t) -> make_not (from_fpat_term t)
  | t -> Fpat.Term.pr Format.std_formatter t; assert false

let from_fpat_formula t = from_fpat_term @@ Fpat.Formula.term_of t


let find_exn_typ = make_col [] (@)
let find_exn_typ_term t =
  match t.desc with
  | Raise t' ->
      Debug.printf "FOUND1: %a@." Print.typ t'.typ;
      [t'.typ]
  | TryWith(t', {typ=TFun(x, _)}) ->
      Debug.printf "FOUND2: %a@." Print.typ @@ Id.typ x;
      [Id.typ x]
  | _ -> find_exn_typ.col_term_rec t
let find_exn_typ_typ typ = []
let () = find_exn_typ.col_term <- find_exn_typ_term
let () = find_exn_typ.col_typ <- find_exn_typ_typ
let find_exn_typ t =
  match find_exn_typ.col_term t with
  | [] -> None
  | typ::_ -> Some typ



let col_typ_var = make_col [] (@)
let col_typ_var_typ typ =
  match typ with
  | TVar({contents=None} as r,_) -> [r]
  | _ -> col_typ_var.col_typ_rec typ
let () = col_typ_var.col_typ <- col_typ_var_typ
let col_typ_var t =
  List.unique ~eq:(==) @@ col_typ_var.col_term t



let col_id =
  let col = make_col [] (@@@) in
  let col_attr attr =
    List.filter_map (function AId n -> Some n | _ -> None) attr
  in
  col.col_attr <- col_attr;
  col.col_typ <- Fun.const [];
  List.unique -| col.col_term

let col_tid =
  let col = make_col [] (@@@) in
  let col_typ ty =
    let acc = col.col_typ_rec ty in
    match ty with
    | TAttr(attr,ty) ->
        List.filter_map (function TAId(s,n) -> Some(s,n) | _ -> None) attr @@@ acc
    | _ -> acc
  in
  col.col_typ <- col_typ;
  col.col_term <- Fun.const [];
  List.unique -| col.col_typ


let rec is_fail t =
  match t.desc with
  | Local(Decl_let [_, t], _) -> is_fail t
  | App({desc=Event("fail",_)}, [{desc=Const Unit}]) -> true
  | _ -> false


let col_app_args =
  let col = make_col2 [] (@) in
  let col_desc f desc =
    match desc with
    | App({desc=Var g}, ts) when Id.(f = g) -> [ts]
    | _ -> col.col2_desc_rec f desc
  in
  col.col2_desc <- col_desc;
  col.col2_term


let col_non_fixed_args =
  let col = make_col2 [] (@) in
  let col_desc (f,xs) desc =
    match desc with
    | App({desc=Var g}, ts) when Id.(f = g) ->
        let check (i,x) =
          match List.nth ts i with
          | {desc=Var y} when Id.(x = y) -> []
          | t -> x :: col.col2_term (f,xs) t
          | exception Invalid_argument _ -> [x]
        in
        List.flatten_map check xs
    | _ -> col.col2_desc_rec (f,xs) desc
  in
  col.col2_desc <- col_desc;
  fun f xs t ->
    let xs' = List.mapi Pair.pair xs in
    col.col2_term (f,xs') t

let find_fixed_args f xs t =
  let non_fixed = col_non_fixed_args f xs t in
  List.filter_out (Id.mem -$- non_fixed) xs



let trans_if =
  let tr = make_trans2 () in
  let trans_if_term trans t2 =
    match trans t2 with
    | None -> tr.tr2_term_rec trans t2
    | Some t2' -> t2'
  in
  tr.tr2_term <- trans_if_term;
  tr.tr2_term

let get_max_var_id =
  let col = make_col (-1) max in
  let col_term t =
    match t.desc with
    | Var x -> max (Id.id x) (Id.id @@ Id.from_string (Id.name x) typ_unknown)
    | _ -> col.col_term_rec t
  in
  col.col_term <- col_term;
  col.col_term

let rec effect_of_typ ty =
  match ty with
  | TAttr(attr, ty') ->
      let attr' = List.filter_map (function TAEffect e -> Some e | _ -> None) attr in
      if attr' = [] then
        effect_of_typ ty'
      else
        List.hd attr'
  | _ ->
      Format.eprintf "%a@." Print.typ ty;
      invalid_arg "effect_of_typ"

let effect_of t =
  match t.attr with
  | AEffect e::_ -> e
  | _ ->
      Format.eprintf "%a@." Print.term t;
      invalid_arg "effect_of"

let get_tdata =
  let col = make_col [] (@@@) in
  let col_typ ty =
    match ty with
    | TData s -> [s]
    | _ -> col.col_typ_rec ty
  in
  col.col_typ <- col_typ;
  col.col_typ

let has_pnondet =
  let col = make_col false (||) in
  let col_pat p =
    match p.pat_desc with
    | PNondet -> true
    | _ -> col.col_pat_rec p
  in
  col.col_pat <- col_pat;
  col.col_pat

let has_event =
  let col = make_col false (||) in
  let col_desc desc =
    match desc with
    | Event _ -> true
    | _ -> col.col_desc_rec desc
  in
  col.col_desc <- col_desc;
  col.col_term

let rec copy_for_pred_share n m ty =
  let copy_var x =
    Id.typ x
    |> copy_for_pred_share n m
    |> Pair.map_same (Id.set_typ x)
  in
  match ty with
  | TBase _
  | TTuple [] ->
      let attr1,attr2 =
        match m with
        | None -> [TAId(label_pred_share,n)], [TAPredShare n]
        | Some m -> [TAId(label_pred_share,n); TAPredShare m], [TAId(label_pred_share,m); TAPredShare n]
      in
      _TAttr attr1 ty, _TAttr attr2 ty
  | TVarLazy _ -> assert false
  | TVar _ -> unsupported "copy_for_pred_share TVar"
  | TFun(x,ty') ->
      let x1,x2 = copy_var x in
      let ty1,ty2 = copy_for_pred_share n m ty' in
      TFun(x1,ty1), TFun(x2,ty2)
  | TFuns _ -> unsupported "copy_for_pred_share TFuns"
  | TTuple xs ->
      let xs1,xs2 = List.split_map copy_var xs in
      TTuple xs1, TTuple xs2
  | TData _ -> unsupported "copy_for_pred_share TData"
  | TVariant _ -> unsupported "copy_for_pred_share TVariant"
  | TRecord _ -> unsupported "copy_for_pred_share TRecord"
  | TApp _ -> unsupported "copy_for_pred_share TApp"
  | TAttr(attr,ty') ->
      let ty1,ty2 = copy_for_pred_share n m ty' in
      _TAttr attr ty1, _TAttr attr ty2
  | TModule _ -> unsupported "copy_for_pred_share TModule"
let copy_for_pred_share bidir ty =
  copy_for_pred_share !!Id.new_int (if bidir then Some !!Id.new_int else None) ty

let get_pred_share ty =
  let col ty =
    let (++) env1 env2 =
      List.fold_left (fun env (x,paths2) -> List.modify_opt x (fun paths1 -> Some (paths2 @ Option.default [] paths1)) env) env1 env2
    in
    let insert x path env = [x,[path]] ++ env in
    let rec aux path ty =
      match ty with
      | TBase _ -> [], []
      | TVarLazy _ -> assert false
      | TVar _ -> unsupported "get_pred_share TVar"
      | TFun(x,ty') ->
          let ips1,pps1 = aux (path@[0]) (Id.typ x) in
          let ips2,pps2 = aux (path@[1]) ty' in
          ips1++ips2, pps1++pps2
      | TFuns _ -> unsupported "get_pred_share TFuns"
      | TTuple xs -> unsupported "get_pred_share TTuple"
      | TData _ -> [], []
      | TVariant _ -> unsupported "get_pred_share TVariant"
      | TRecord _ -> unsupported "get_pred_share TRecord"
      | TApp _ -> unsupported "get_pred_share TApp"
      | TAttr(attr,ty') ->
          let ips,pps = aux path ty' in
          let aux' f acc =
            let aux'' a acc =
              match f a with
              | None -> acc
              | Some n -> insert n path acc
            in
            List.fold_right aux'' attr acc
          in
          aux' (function TAId(s,n) when s = label_pred_share -> Some n | _ -> None) ips,
          aux' (function TAPredShare n -> Some n | _ -> None) pps
      | TModule _ -> unsupported "get_pred_share TModule"
    in
    aux [] ty
  in
  let id_paths,pred_paths = col ty in
  let rec longest_common_prefix paths =
    if paths = [] || List.mem [] paths then
      [], paths
    else
      let x = List.hd @@ List.hd paths in
      if List.for_all (List.hd |- (=) x) paths then
        let paths' = List.map List.tl paths in
        let lcp,paths'' = longest_common_prefix paths' in
        x::lcp, paths''
      else
        [], paths
  in
  let rec aux n =
    let paths1 = List.assoc n id_paths in
    let paths2 = List.assoc_option n pred_paths in
    match paths2 with
    | None -> None
    | Some paths2 ->
        let prefix1,paths1' = longest_common_prefix paths1 in
        let prefix2,paths2' = longest_common_prefix paths2 in
        assert (List.Set.subset paths2' paths1');
        Some (prefix1, paths2', prefix2)
  in
  List.map fst id_paths
  |> List.unique
  |> List.filter_map aux

let set_id_counter_to_max =
  Id.set_counter -| succ -| get_max_var_id

let rec size_pattern p =
  let sum ps = List.fold_left (fun s p -> s + size_pattern p) 0 ps in
  match p.pat_desc with
  | PAny -> 1
  | PNondet -> 1
  | PVar x -> 1
  | PAlias(p,x) -> 1 + size_pattern p
  | PConst t -> size t
  | PConstr(s,ps) -> 1 + sum ps
  | PNil -> 1
  | PCons(p1,p2) -> 1 + sum [p1;p2]
  | PTuple ps -> 1 + sum ps
  | PRecord pats -> 1 + sum (List.map snd pats)
  | POr(p1,p2) -> 1 + sum [p1;p2]
  | PNone -> 1
  | PSome p -> 1 + size_pattern p
  | PWhen(p,cond) -> 1 + size_pattern p + size cond
and size_declaration decl =
  match decl with
  | Decl_let bindings -> List.fold_left (fun s (_,t) -> s + size t) 0 bindings
  | Decl_type _ -> 0
and size t =
  let sum ts = List.fold_left (fun s t -> s + size t) 0 ts in
  match t.desc with
  | End_of_definitions -> 1
  | Const c -> 1
  | Var y -> 1
  | Fun(y, t) -> 1 + size t
  | App(t1, ts) -> 1 + size t1
  | If(t1, t2, t3) -> 1 + sum [t1;t2;t3]
  | Local(decl, t2) -> 1 + size t2 + size_declaration decl
  | BinOp(op, t1, t2) -> 1 + sum [t1;t2]
  | Not t1 -> 1 + size t1
  | Event(s,b) -> 1
  | Record fields -> 1 + sum (List.map snd fields)
  | Field(t1,s) -> 1 + size t1
  | SetField(t1,_,t2) -> 1 + sum [t1;t2]
  | Nil -> 1
  | Cons(t1,t2) -> 1 + sum [t1;t2]
  | Constr(s,ts) -> 1 + sum ts
  | Match(t1,pats) -> 1 + size t1 + List.fold_left (fun s (p,t) -> s + size_pattern p + size t) 0 pats
  | Raise t -> 1 + size t
  | TryWith(t1,t2) -> 1 + sum [t1;t2]
  | Tuple ts -> 1 + sum ts
  | Proj(i,t) -> 1 + size t
  | Bottom -> 1
  | Label(info, t) -> 1 + size t
  | Ref t -> 1 + size t
  | Deref t -> 1 + size t
  | SetRef(t1,t2) -> 1 + sum [t1;t2]
  | TNone -> 1
  | TSome t -> 1 + size t
  | Module decls -> 1 + List.fold_left (fun s decl -> s + size_declaration decl) 0 decls

module Term = struct
  let unit = unit_term
  let tt = true_term
  let true_ = true_term
  let ff = false_term
  let false_ = false_term
  let fail = make_fail_unit None
  let randi = randint_unit_term
  let randb = randbool_unit_term
  let rand = make_rand_unit
  let bot = make_bottom
  let eod = end_of_definitions
  let var = make_var
  let vars = List.map make_var
  let int = make_int
  let bool = make_bool
  let string = make_string
  let (@) = make_app
  let (@@) = make_app
  let let_ = make_let
  let let_s = make_let_s
  let lets = make_lets
  let fun_ = make_fun
  let pfun = make_pure_fun
  let funs = make_funs
  let not = make_not
  let (&&) = make_and
  let ands = make_ands
  let (||) = make_or
  let ors = make_ors
  let (+) = make_add
  let (-) = make_sub
  let ( * ) = make_mul
  let (/) = make_div
  let (~-) = make_neg
  let if_ = make_if
  let br = make_br
  let brs = make_brs
  let (=) = make_eq
  let (<>) = make_neq
  let (<) = make_lt
  let (>) = make_gt
  let (<=) = make_leq
  let (>=) = make_geq
  let (<|) t1 op = make_binop op t1 and (|>) mb t2 = mb t2
  let fst = make_fst
  let snd = make_snd
  let pair = make_pair
  let tuple = make_tuple
  let proj = make_proj
  let nil = make_nil
  let cons = make_cons
  let list = make_list
  let seq = make_seq
  let seqs = List.fold_right make_seq
  let ignore = make_ignore
  let assert_ = make_assert
  let assume = make_assume
  let none = make_none
  let some = make_some
  let ref = make_ref
  let match_ = make_match
  let module_ = make_module
  let local = make_local
  let length = make_length
  let (|->) = subst ~rename_if_captured:false ~fast:false
end

module Pat = struct
  let __ = make_pany
  let const = make_pconst
  let unit = const unit_term
  let int = const -| make_int
  let bool = const -| make_bool
  let true_ = bool true
  let false_ = bool false
  let var = make_pvar
  let pair = make_ppair
  let tuple = make_ptuple
  let nil = make_pnil
  let nil2 = make_pnil2
  let cons = make_pcons
  let when_ = make_pwhen
end
