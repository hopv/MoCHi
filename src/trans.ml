open Util
open Syntax
open Term_util
open Type

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let flatten_tvar,flatten_tvar_typ =
  let tr = !!make_trans in
  tr.tr_term, tr.tr_typ

(* not capture-avoiding *)
let subst_var_id =
  let tr = make_trans2 () in
  let tr_desc (x,x') desc =
    match desc with
    | Var y when Id.(x = y) -> Var (Id.set_id y @@ Id.id x')
    | _ -> tr.tr2_desc_rec (x,x') desc
  in
  tr.tr2_desc <- tr_desc;
  fun x x' t -> tr.tr2_term (x,x') t

let map_id =
  let tr = make_trans2 () in
  tr.tr2_var <- (fun f -> f -| tr.tr2_var_rec f);
  tr.tr2_term

let remove_id_let =
  let tr = make_trans () in
  let tr_desc desc =
    match tr.tr_desc_rec desc with
    | Local(Decl_let [x, t], {desc=Var y}) when Id.(x = y) -> t.desc
    | desc' -> desc'
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let alpha_rename ?(whole=false) ?(set_counter=false) =
  let prefix = '#' in (* must not occur as a prefix of the name of each variable *)
  let tr = make_trans2 () in
  let tr_desc (cnt,names) desc =
    let new_id x =
      let rec aux var =
        let s = Id.to_string var in
        if s = "" || StringSet.mem s !names then
          aux @@ Id.set_id x @@ Counter.gen cnt
        else
          var
      in
      if whole then
        let x' = aux @@ Id.set_id x 0 in
        names := StringSet.add (Id.to_string x') !names;
        Id.add_name_before (String.of_char prefix) x'
      else
        Id.new_var_id x
    in
    let desc' = tr.tr2_desc_rec (cnt,names) desc in
    match desc' with
    | Local(Decl_let bindings, t1) ->
        let map = List.map (fun (f,_) -> f, new_id f) bindings in
        let bindings' = List.map2 (fun (_,t) (_,f') -> f', subst_var_map_without_typ map t) bindings map in
        Local(Decl_let bindings', subst_var_map_without_typ map t1)
    | Fun(x, t1)->
        let x' = new_id x in
        Fun(x', subst_var_without_typ x x' t1)
    | Match(t1,pats) ->
        let aux (p,t2) =
          let map = List.map (Pair.add_right new_id) @@ List.unique ~eq:Id.eq @@ get_bv_pat p in
          rename_pat map p,
          subst_var_map_without_typ map t2
        in
        Match(t1, List.map aux pats)
    | _ -> desc'
  in
  tr.tr2_desc <- tr_desc;
  tr.tr2_typ <- Fun.snd;
  let remove_sharp = Id.map_name (fun s -> if s <> "" && s.[0] = prefix then String.tl s else s) in
  fun t ->
    let cnt = !!Counter.create in
    let names = ref StringSet.empty in
    t
    |@> Debug.printf "INPUT: %a@." Print.term
    |> tr.tr2_term (cnt,names)
    |@> Debug.printf "OUTPUT: %a@." Print.term
    |> map_id remove_sharp
    |@set_counter&> set_id_counter_to_max

let inst_tvar, inst_tvar_typ =
  let col = make_col2 () Fun.ignore2 in
  let col_typ ty typ =
    match typ with
    | TVar({contents=None} as r, _) ->
        Debug.printf "INST_TVAR: %a := %a@." Print.typ typ Print.typ ty;
        r := Some ty
    | _ -> col.col2_typ_rec ty typ
  in
  col.col2_typ <- col_typ;
  col.col2_term, col.col2_typ

let rename_tvar,rename_tvar_var,rename_tvar_typ =
  let tr = make_trans2 () in
  let tr_typ map typ =
    match typ with
    | TVar({contents=None} as x, n) when List.mem_assq x map -> TVar(List.assq x map, n)
    | _ -> tr.tr2_typ_rec map typ
  in
  tr.tr2_typ <- tr_typ;
  tr.tr2_term, tr.tr2_var, tr.tr2_typ

let get_tvars =
  let col = make_col [] (List.fold_left (fun xs y -> if List.memq y xs then xs else y::xs)) in
  let col_typ typ =
    match typ with
    | TVar({contents=None} as x,_) -> [x]
    | TAttr(_,typ) -> col.col_typ typ
    | _ -> col.col_typ_rec typ
  in
  col.col_typ <- col_typ;
  col.col_typ

let unify_pattern_var =
  let col = make_col () Fun.ignore2 in
  let col_term t =
    match t.desc with
    | Match(t, pats) ->
        let aux1 (pat,t') =
          let aux2 x =
            let ty = Id.typ x in
            get_fv t'
            |> List.filter (Id.same x)
            |> List.iter (unify ty -| Id.typ)
          in
          List.iter aux2 @@ get_bv_pat pat
        in
        col.col_term t;
        List.iter aux1 pats
    | _ -> col.col_term_rec t
  in
  col.col_term <- col_term;
  col.col_term

let rec define_rand ?(name="") (env, defs as ed) typ =
  if List.mem_assoc typ env then
    (env, defs), make_app (make_var @@ List.assoc typ env) [unit_term]
  else
    match elim_tattr typ with
    | TBase _ -> (env, defs), make_rand_unit typ
    | TVar({contents=None} as r,_) -> r := Some Ty.int; define_rand ed Ty.int
    | TVar({contents=Some typ},_) -> define_rand ed typ
    | TFun _ when is_raise_tfun typ ->
        let ty_exn,x,typ = Option.get @@ decomp_raise_tfun typ in
        let ed,t_typ = define_rand ed typ in
        let ed,exn = define_rand ed ty_exn in
        ed, Term.(fun_ x (br (raise exn typ) t_typ))
    | TFun(x,typ) ->
        let ed',t = define_rand ed typ in
        ed', Term.fun_ x t
    | TApp("list", [TVar({contents=None} as r,_)]) ->
        r := Some Ty.unit;
        define_rand ed typ
    | TApp("list", [typ']) ->
        let u = Id.new_var Ty.unit in
        let f = Id.new_var ~name:("make_" ^ to_id_string typ) (TFun(u,typ)) in
        let env' = (typ,f)::env in
        let (env'',defs'),t_typ' = define_rand (env', defs) typ' in
        let t_typ = Term.(br (nil typ') (cons t_typ' (var f @ [unit]))) in
        (env'', (f, Term.fun_ u t_typ)::defs'), Term.(var f @ [unit])
    | TTuple xs ->
        let aux x (ed,ts) =
          let ed',t = define_rand ed @@ Id.typ x in
          ed', t::ts
        in
        let (env', defs'), ts = List.fold_right aux xs ((env,defs),[]) in
        (env', defs'), make_tuple ts
    | TApp("ref", [typ]) ->
        let ed',t = define_rand ed typ in
        ed', Term.ref t
    | TApp("array", [typ]) ->
        let ed',t = define_rand ed @@ make_tlist typ in
        let f = Id.new_var ~name:"Array.of_list" ~attr:[Id.External] Ty.(fun_ (list typ) (array typ)) in
        ed', Term.(var f @ [t])
    | TData _ -> (env, defs), make_rand_unit typ
    | TVariant(_,labels) ->
        let u = Id.new_var Ty.unit in
        let f = Id.new_var ~name:("make_" ^ to_id_string typ) (TFun(u,typ)) in
        let env' = (TData name,f)::(typ,f)::env in
        let n = List.length labels in
        let aux1 (_s,typs) (ed,itss,i) =
          let aux2 typ (ed,ts) =
            let ed',t = define_rand ed typ in
            ed', t::ts
          in
          let ed',ts' = List.fold_right aux2 typs (ed,[]) in
          ed', (i-1,ts')::itss, i-1
        in
        let (env'',defs'),itss,_ = List.fold_right aux1 labels ((env',defs),[],n) in
        let aux (s,_typs) (i,ts) =
          let p = if i < n-1 then make_pconst (make_int i) else make_pany Ty.int in
          p, {desc=Constr(s,ts); typ=typ; attr=[]}
        in
        let (env'',defs'),t = (env'', defs'), Term.(match_ randi (List.map2 aux labels itss)) in
        (env'', (f,make_fun u t)::defs'), Term.(var f @ [unit])
    | TRecord fields ->
        let u = Id.new_var Ty.unit in
        let f = Id.new_var ~name:("make_" ^ to_id_string typ) (TFun(u,typ)) in
        let env' = (TData name,f)::(typ,f)::env in
        let (env'',defs'),t =
          let aux (field,(_flag,typ)) (ed,sfts) =
            let ed', t = define_rand ed typ in
            ed', (field,t)::sfts
          in
          let ed',sfts = List.fold_right aux fields ((env',defs),[]) in
          ed', {desc=Record sfts; typ=typ; attr=[]}
        in
        (env'', (f,make_fun u t)::defs'), Term.(var f @ [unit])
    | TApp("option", [typ']) ->
        let (env',defs'),t_typ' = define_rand (env,defs) typ' in
        let t = make_br {desc=TNone;typ;attr=[]} {desc=TSome(t_typ');typ;attr=[]} in
        (env',defs'), t
    | _ ->
        unsupported @@ Format.asprintf "define_rand: %a" Print.typ typ
let define_rand ed typ = define_rand ~name:"" ed typ

(* INPUT: type declarations must be on top *)
let inst_randval =
  let fld = make_fold_tr () in
  let fld_term ed t =
    match t.desc with
    | App({desc=Const(Rand(TBase TInt,false));attr}, [t']) when t'.desc = Const Unit && List.mem AAbst_under attr -> (* for disproving termination  *)
        ed, t
    | App({desc=Const(Rand(typ,false))}, [t']) when t'.desc = Const Unit ->
        define_rand ed typ
    | Const(Rand _) ->
        assert false
    | _ -> fld.fld_term_rec ed t
  in
  fld.fld_term <- fld_term;
  fun t ->
    let (_,defs),t' = fld.fld_term ([],[]) t in
    let defs' =
      let edges =
        defs
        |> List.map (fun (f,t) -> f, List.filter_out (Id.eq f) @@ get_fv t)
        |> List.flatten_map (fun (f,fv) -> List.map (fun g -> g, f) fv)
      in
      let cmp = Compare.topological ~eq:Id.eq ~dom:(List.map fst defs) edges in
      List.sort (Compare.on ~cmp fst) defs
    in
    let tdecls,t'' = decomp_type_decls t' in
    make_lets defs' t''
    |> List.fold_right make_let_type tdecls

let part_eval t =
  let is_apply t =
    let xs,t' = decomp_funs t in
    match t'.desc, xs with
    | Var x, [y] -> Id.(x = y)
    | App(t, ts), _ ->
        let rec aux xs ts =
          match xs,ts with
          | [], [] -> true
          | x::xs', {desc=Var y}::ts' when Id.(x = y) -> aux xs' ts'
          | _ -> false
        in
        aux xs (t::ts)
    | _ -> false
  in
  let is_alias t =
    let xs,t' = decomp_funs t in
    match t'.desc with
    | Var x ->
        if xs = []
        then Some x
        else None
    | App({desc=Var f}, ts) ->
        let rec aux xs ts =
          match xs,ts with
            [], [] -> true
          | x::xs',{desc=Var y}::ts' when Id.(x = y) -> aux xs' ts'
          | _ -> false
        in
        if aux xs ts
        then Some f
        else None
    | _ -> None
  in
  let rec aux apply t =
    let desc =
      match t.desc with
      | End_of_definitions -> End_of_definitions
      | Const c -> Const c
      | Var x ->
          begin
            try
              Local(Decl_let [x, List.assoc x apply], make_var x)
            with Not_found -> Var x
          end
      | Fun(x, t) -> Fun(x, aux apply t)
      | App({desc=Var f}, ts) ->
          if List.mem_assoc f apply
          then
            match ts with
            | [] -> Local(Decl_let [f, List.assoc f apply], (make_var f))
            | [t] -> t.desc
            | t::ts' -> App(t, ts')
          else
            let ts' = List.map (aux apply) ts in
            App(make_var f, ts')
      | App({desc=Fun(x,t1);typ=typ'} as t, ts) ->
          if is_apply t then
            match ts with
            | [] -> Fun(x,t1)
            | [t] -> t.desc
            | t::ts' -> App(t, ts')
          else
            begin
              match ts with
              | [{desc=Const(True|False)}] -> (aux apply (subst x (List.hd ts) t1)).desc
              | _ ->
                  let t' = aux apply t1 in
                  let ts' = List.map (aux apply) ts in
                  App({desc=Fun(x,t');typ=typ'; attr=[]}, ts')
            end
      | App(t, ts) -> App(aux apply t, List.map (aux apply) ts)
      | If({desc=Const True}, t2, _) -> (aux apply t2).desc
      | If({desc=Const False}, _, t3) -> (aux apply t3).desc
      | If({desc=Not t1}, t2, t3) -> If(aux apply t1, aux apply t3, aux apply t2)
      | If(t1, t2, t3) ->
          if t2 = t3
          then t2.desc
          else If(aux apply t1, aux apply t2, aux apply t3)
      | Local(Decl_let [f, t1], t2) ->
          if is_apply t1
          then (aux ((f,t1)::apply) (aux apply t2)).desc
          else
            begin
              match is_alias t1  with
              | Some x when not @@ List.mem f @@ get_fv t1 ->
                  (subst_var f x @@ aux apply t2).desc
              | _ -> Local(Decl_let [f, aux apply t1], aux apply t2)
            end
      | Local _ -> assert false
      | BinOp(op, t1, t2) -> BinOp(op, aux apply t1, aux apply t2)
      | Not t -> Not (aux apply t)
      | Event(s,b) -> Event(s,b)
      | Record fields -> Record (List.map (Pair.map_snd @@ aux apply) fields)
      | Field(t,s) -> Field(aux apply t, s)
      | Nil -> Nil
      | Cons(t1,t2) -> Cons(aux apply t1, aux apply t2)
      | Constr(c,ts) -> Constr(c, List.map (aux apply) ts)
      | Match(t,pats) ->
          let aux' (pat,t) = pat, aux apply t in
          Match(aux apply t, List.map aux' pats)
      | Proj _ -> assert false
      | Tuple _ -> assert false
      | TryWith (_, _) -> assert false
      | Raise _ -> assert false
      | SetField _ -> assert false
      | Bottom -> assert false
      | Label _ -> assert false
      | Ref _ -> assert false
      | Deref _ -> assert false
      | SetRef _ -> assert false
      | TNone -> assert false
      | TSome _ -> assert false
      | Module _ -> assert false
      | MemSet _ -> assert false
      | AddSet _ -> assert false
      | Subset _ -> assert false
    in
    {desc=desc; typ=t.typ; attr=[]}
  in
  aux [] t

let trans_let =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(Decl_let [f, t1], t2) when not @@ is_fun t1 ->
        App(make_fun f @@ tr.tr_term t2, [tr.tr_term t1])
    | Local(Decl_let bindings, _t2) when List.exists (not -| is_fun -| snd) bindings ->
        assert false
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let propagate_typ_arg =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(Decl_let bindings, t2) ->
        let aux (f,t) =
          let xs,t' = decomp_funs t in
          let xs' =
            let ys = List.take (List.length xs) (get_args @@ Id.typ f) in
            let aux x y ys =
              let ys' = List.map (Id.map_typ @@ subst_type_var y x) ys in
              Id.set_typ x (Id.typ y) :: ys'
            in
            List.fold_right2 aux xs ys []
          in
          let t'' =
            t'
            |> tr.tr_term
            |> List.fold_right2 subst_var xs xs'
          in
          f, make_funs xs' t''
        in
        let bindings' = List.map aux bindings in
        let t2' = tr.tr_term t2 in
        Local(Decl_let bindings', t2')
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let replace_typ_var env x =
  Id.set_typ x @@ List.assoc_default (Id.typ x) x env

let replace_typ =
  let tr = make_trans2 () in
  let tr_desc env desc =
    match desc with
    | Local(Decl_let bindings, t2) ->
        let aux (f,t) =
          let xs,t' = decomp_funs t in
          let f' = replace_typ_var env f in
          if not @@ can_unify (Id.typ f) (Id.typ f') then
            begin
              let f'' = Id.set_typ f @@ elim_tattr_all @@ Id.typ f' in
              Format.eprintf "Prog: %a@.Spec: %a@." Print.id_typ f Print.id_typ f'';
              let msg = Format.sprintf "Type of %s in %s is wrong?" (Id.name f) !Flag.Input.spec in
              fatal @@ msg ^ " (please specify monomorphic types if polymorphic types exist)"
            end;
          let xs' =
            let ys = List.take (List.length xs) (get_args @@ Id.typ f') in
            List.map2 (fun x y -> Id.set_typ x @@ Id.typ y) xs ys
          in
          let t'' =
            t'
            |> tr.tr2_term env
            |> subst_var f f'
            |> List.fold_right2 subst_var xs xs'
          in
          f', make_funs xs' t''
        in
        let bindings' = List.map aux bindings in
        let t2' = tr.tr2_term env t2 in
        let t2'' = List.fold_left2 (fun t (f,_) (f',_) -> subst_var f f' t) t2' bindings bindings' in
        Local(Decl_let bindings', t2'')
    | _ -> tr.tr2_desc_rec env desc
  in
  tr.tr2_desc <- tr_desc;
  fun env t ->
    t
    |> tr.tr2_term env
    |> propagate_typ_arg

let rec eval t =
  let desc =
    match t.desc with
    | Const c -> Const c
    | Var x -> Var x
    | App({desc=Fun(x, t)}, t'::ts) ->
        (eval ({desc=App(subst_map [x, t'] t, ts);typ=t.typ; attr=[]})).desc
    | App(t, []) -> (eval t).desc
    | App(t, ts) ->
        App(eval t, List.map eval ts)
    | If({desc=Const True}, t2, _) ->
        (eval t2).desc
    | If({desc=Const False}, _, t3) ->
        (eval t3).desc
    | If(t1, t2, t3) ->
        If(eval t1, eval t2, eval t3)
    | Local _ -> assert false
    | BinOp(Add, {desc=Const (Int 0)}, t) ->
        (eval t).desc
    | BinOp(Mult, {desc=Const (Int 1)}, t) ->
        (eval t).desc
    | BinOp(Div, t, {desc=Const (Int 1)}) ->
        (eval t).desc
    | BinOp(Sub, t1, t2) ->
        (eval (make_add (eval t1) (eval (make_mul (make_int (-1)) t2)))).desc
    | BinOp(Mult, {desc=Const (Int n)}, {desc=BinOp(Mult, {desc=Const (Int m)}, t)}) ->
        (eval (make_mul (make_int (n*m)) t)).desc
    | BinOp(op, t1, t2) ->
        BinOp(op, eval t1, eval t2)
    | Not t ->
        Not(eval t)
    | Fun(x, {desc=App(t,ts)}) ->
        let t' = eval t in
        let ts' = List.map eval ts in
        let ts'',t_last = List.decomp_snoc ts' in
        if t_last.desc = Var x && not @@ List.mem x @@ get_fv @@ make_app t' ts'' then
          (eval @@ make_app t' ts'').desc
        else
          Fun(x, make_app t' ts')
    | Fun(x,t) ->
        Fun(x, eval t)
    | Event(s,b) -> Event(s,b)
    | _ -> assert false
  in
  {t with desc}

let normalize_binop_exp op t1 t2 =
  let neg xs = List.map (fun (x,n) -> x,-n) xs in
  let rec decomp t =
    match t.desc with
    | Const (Int n) -> [None, n]
    | Var x -> [Some {desc=Var x;typ=Id.typ x; attr=[]}, 1]
    | BinOp(Add, t1, t2) ->
        decomp t1 @@@ decomp t2
    | BinOp(Sub, t1, t2) ->
        decomp t1 @@@ neg (decomp t2)
    | BinOp(Mult, t1, t2) ->
        let xns1 = decomp t1 in
        let xns2 = decomp t2 in
        let reduce xns = List.fold_left (fun acc (_,n) -> acc+n) 0 xns in
        let aux (x,_) = x <> None in
        begin
          match List.exists aux xns1, List.exists aux xns2 with
          | true, true ->
              Format.eprintf "Nonlinear expression not supported: %a@." Print.term (make_binop op t1 t2);
              assert false
          | false, true ->
              let k = reduce xns1 in
              List.rev_map (fun (x,n) -> x,n*k) xns2
          | true, false ->
              let k = reduce xns2 in
              List.rev_map (fun (x,n) -> x,n*k) xns1
          | false, false ->
              [None, reduce xns1 + reduce xns2]
        end
    | _ -> assert false
  in
  let xns1 = decomp t1 in
  let xns2 = decomp t2 in
  let xns =
    let compare (x1,_) (x2,_) =
      let aux = function
        | None -> "\255"
        | Some {desc=Var x} -> Id.to_string x
        | _ -> assert false
      in
      compare (aux x2) (aux x1)
    in
    List.sort compare (xns1 @@@ (neg xns2))
  in
  let rec aux = function
    | [] -> []
    | (x,n)::xns ->
        let xns1,xns2 = List.partition (fun (y,_) -> x=y) xns in
        let n' = List.fold_left (fun acc (_,n) -> acc+n) 0 ((x,n)::xns1) in
        (x,n') :: aux xns2
  in
  let xns' = aux xns in
  let xns'' = List.filter (fun (_,n) -> n<>0) xns' in
  let x,n = List.hd xns'' in
  let xns = List.rev @@ List.tl xns'' in
  let op',t1',t2' =
    let aux = function
      | None,n -> {desc=Const (Int n); typ=Ty.int; attr=[]}
      | Some x,n -> if n=1 then x else make_mul (make_int n) x
    in
    let t1,xns',op' =
      if n<0
      then
        let op' =
          match op with
          | Eq -> Eq
          | Lt -> Gt
          | Gt -> Lt
          | Leq -> Geq
          | Geq -> Leq
          | _ -> assert false
        in
        aux (x,-n), xns, op'
      else
        aux (x,n), neg xns, op
    in
    let ts = List.map aux xns' in
    let t2 =
      match ts with
      | [] -> make_int 0
      | t::ts' -> List.fold_left make_add t ts'
    in
    op', t1, t2
  in
  let rec simplify t =
    let desc =
      match t.desc with
      | BinOp(Add, t1, {desc=BinOp(Mult, {desc=Const (Int n)}, t2)}) when n < 0 ->
          let t1' = simplify t1 in
          BinOp(Sub, t1', make_mul (make_int (-n)) t2)
      | BinOp(Add, t1, {desc=Const (Int n)}) when n < 0 ->
          let t1' = simplify t1 in
          BinOp(Sub, t1', make_int (-n))
      | BinOp(Add, t1, t2) ->
          let t1' = simplify t1 in
          BinOp(Add, t1', t2)
      | t -> t
    in
    {desc=desc; typ=t.typ; attr=[]}
  in
  BinOp(op', t1', simplify t2')

let rec normalize_bool_exp t =
  let desc =
    match t.desc with
    | Const True -> Const True
    | Const False -> Const False
    | Var x -> Var x
    | BinOp(Or|And as op, t1, t2) ->
        let t1' = normalize_bool_exp t1 in
        let t2' = normalize_bool_exp t2 in
        BinOp(op, t1', t2')
    | BinOp(Eq, {desc=Const(True|False)}, _)
    | BinOp(Eq, _, {desc=Const(True|False)})
    | BinOp(Eq, {desc=Nil|Cons _}, _)
    | BinOp(Eq, _, {desc=Nil|Cons _}) as t -> t
    | BinOp(Eq|Lt|Gt|Leq|Geq as op, t1, t2) -> normalize_binop_exp op t1 t2
    | Not t -> Not (normalize_bool_exp t)
    | _ -> assert false
  in
  {t with desc}

let rec merge_geq_leq t =
  let desc =
    match t.desc with
    | Const True -> Const True
    | Const False -> Const False
    | Var x -> Var x
    | BinOp(And, _, _) ->
        let ts = decomp_and t in
        let is_dual t1 t2 =
          match t1.desc,t2.desc with
          | BinOp(op1,t11,t12), BinOp(op2,t21,t22) when t11=t21 && t12=t22 -> op1=Leq && op2=Geq || op1=Geq && op2=Leq
          | _ -> false
        in
        let get_eq t =
          match t.desc with
          | BinOp((Leq|Geq),t1,t2) -> make_eq t1 t2
          | _ -> assert false
        in
        let rec aux = function
          | [] -> []
          | t::ts ->
              if List.exists (is_dual t) ts
              then
                let t' = get_eq t in
                let ts' = List.filter_out (is_dual t) ts in
                t' :: aux ts'
              else
                t :: aux ts
        in
        let ts' = aux ts in
        let t =
          match ts' with
          | [] -> assert false
          | [t] -> t
          | t::ts -> List.fold_left make_and t ts
        in
        t.desc
    | BinOp(Or, t1, t2) ->
        let t1' = merge_geq_leq t1 in
        let t2' = merge_geq_leq t2 in
        BinOp(Or, t1', t2')
    | BinOp(Eq|Lt|Gt|Leq|Geq as op, t1, t2) -> BinOp(op, t1, t2)
    | Not t -> Not (merge_geq_leq t)
    | _ -> Format.eprintf "%a@." Print.term t; assert false
  in
  {t with desc=desc}

let elim_fun =
  let tr = make_trans2 () in
  let tr_term fun_name t =
    match t.desc with
    | Fun(y, t1) ->
        let f = Id.new_var ~name:fun_name t.typ in
        make_let [f, make_fun y @@ tr.tr2_term fun_name t1] @@ make_var f
    | Local(Decl_let bindings, t2) ->
        let aux (f,t) =
          let xs,t' = decomp_funs t in
          f, make_funs xs @@ tr.tr2_term ("f_" ^ Id.name f) t' in
        let bindings' = List.map aux bindings in
        let t2' = tr.tr2_term fun_name t2 in
        make_let bindings' t2'
    | _ -> tr.tr2_term_rec fun_name t
  in
  tr.tr2_term <- tr_term;
  tr.tr2_term "f"

let make_ext_env =
  let col = make_col2 [] (@@@) in
  let col_desc funs desc =
    match desc with
    | Var x when Fpat.RefTypInfer.is_parameter (Id.name x) -> []
    | Var x when Id.is_coefficient x -> []
    | Var x when Id.mem x funs -> [x, Id.typ x]
    | Var _ -> []
    | _ -> col.col2_desc_rec funs desc
  in
  col.col2_desc <- col_desc;
  fun t -> col.col2_term (get_fv t) t

let init_base_rand =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | App({desc=Const(Rand(typ,false))},[{desc=Const Unit}]) when is_base_typ typ ->
        let name =
          match typ with
          | TBase TInt -> "_ri"
          | TBase TBool -> "_rb"
          | _ -> "_r"
        in
        make_var @@ Id.new_var ~name typ
    | Const(Rand(TBase TInt,_)) -> assert false
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let rec inlined_f inlined fs t =
  let desc =
    match t.desc with
    | Const c -> Const c
    | Var y ->
        if List.exists (Triple.fst |- Id.same y) fs then
          let _, xs, t' = List.find (Triple.fst |- Id.same y) fs in
          let f, _ =
            List.fold_left
              (fun (f, ty) y ->
               (fun t ->
                f {desc=Fun(y, t); typ=ty; attr=[]}),
                match ty with
                | Type.TFun(_, ty') -> ty'
                | _ -> Format.eprintf "%a@." Print.typ ty; assert false)
              (Fun.id, t.typ)
              xs
          in
          let t' = inlined_f inlined fs t' in
          (f t').desc
        else
          Var y
    | Fun(y, t1) -> Fun(y, inlined_f inlined fs t1)
    | App(t1, ts) ->
        (match t1.desc with
         | Var f when List.exists (Triple.fst |- Id.same f) fs ->
             let _, xs, t = try List.find (Triple.fst |- Id.same f) fs with Not_found -> assert false in
             let ts = List.map (inlined_f inlined fs) ts in
             let ys = List.map (fun t -> match t.desc with Const (Unit | True | False | Int _) | Var _ -> `L(t) | _ -> `R(Id.new_var ~name:"arg" t.typ)) ts in
             let ys1, ys2 = if List.length ys <= List.length xs then ys, [] else Fpat.Util.List.split_nth (List.length xs) ys in
             let xs1, xs2 = Fpat.Util.List.split_nth (List.length ys1) xs in
             let map = List.map2 (fun x y -> match y with `L(t) -> x, t | `R(y) -> x, make_var y) xs1 ys1 in
             let t' = subst_map map t in
             let f, _ =
               List.fold_left
                 (fun (f, ty) x -> (fun t -> f {desc=Fun(x, t); typ=ty; attr=[]}), match ty with Type.TFun(_, ty') -> ty' | _ -> assert false)
                 ((fun t -> t), Type.app_typ t1.typ (List.map Syntax.typ ts))
                 xs2
             in
             let bindings = Fpat.Util.List.filter_map2 (fun y t -> match y with `L(_) -> None | `R(y) -> Some(y, t)) ys ts in
             (make_lets bindings (make_app (f t') (List.map (fun y -> match y with `L(t) -> t | `R(y) -> make_var y) ys2))).desc
         | _ ->
             let t1' = inlined_f inlined fs t1 in
             let ts' = List.map (inlined_f inlined fs) ts in
             App(t1', ts'))
    | If(t1, t2, t3) -> If(inlined_f inlined fs t1, inlined_f inlined fs t2, inlined_f inlined fs t3)
    | Local(Decl_type decls, t2) -> Local(Decl_type decls, inlined_f inlined fs t2)
    | Local(Decl_let bindings, t2) ->
        let aux (f,t) =
          `L(f, inlined_f inlined fs t)
        in
        let bindings', fs' = Fpat.Util.List.partition_map aux bindings in
        let t2' = inlined_f inlined (fs @ fs') t2 in
        if bindings' = [] then
          t2'.desc
        else
          Local(Decl_let bindings', t2')
    | BinOp(op, t1, t2) -> BinOp(op, inlined_f inlined fs t1, inlined_f inlined fs t2)
    | Not t1 -> Not (inlined_f inlined fs t1)
    | Event(s,b) -> Event(s,b)
    | Record fields ->  Record (List.map (Pair.map_snd @@ inlined_f inlined fs) fields)
    | Field(t1,s) -> Field(inlined_f inlined fs t1,s)
    | SetField(t1,s,t2) -> SetField(inlined_f inlined fs t1,s,inlined_f inlined fs t2)
    | Nil -> Nil
    | Cons(t1,t2) -> Cons(inlined_f inlined fs t1, inlined_f inlined fs t2)
    | Constr(s,ts) -> Constr(s, List.map (inlined_f inlined fs) ts)
    | Match(t1,pats) ->
        let aux (pat,t1) = pat, inlined_f inlined fs t1 in
        Match(inlined_f inlined fs t1, List.map aux pats)
    | Raise t -> Raise (inlined_f inlined fs t)
    | TryWith(t1,t2) -> TryWith(inlined_f inlined fs t1, inlined_f inlined fs t2)
    | Tuple ts -> Tuple (List.map (inlined_f inlined fs) ts)
    | Proj(i,t) -> Proj(i, inlined_f inlined fs t)
    | Bottom -> Bottom
    | MemSet(t1,t2) -> MemSet(inlined_f inlined fs t1, inlined_f inlined fs t2)
    | AddSet(t1,t2) -> AddSet(inlined_f inlined fs t1, inlined_f inlined fs t2)
    | Subset(t1,t2) -> Subset(inlined_f inlined fs t1, inlined_f inlined fs t2)
    | _ -> Format.eprintf "inlined_f: %a@." Print.constr t; assert false
  in
  {t with desc}

let inlined_f inlined t = inlined_f inlined [] t |@> Type_check.check




let lift_fst_snd = make_trans2 ()

let lift_fst_snd_term fs t =
  match t.desc with
  | Fun(y, t1) -> make_fun y @@ lift_fst_snd.tr2_term fs t1(* ommit the case where y is a pair *)
  | Local(Decl_let bindings, t2) ->
      let bindings' =
        List.map
          (fun (f,t) ->
           let xs,t = decomp_funs t in
           f, make_funs xs
           (let fs' =
             List.flatten
               (List.filter_map
                  (fun x ->
                   match x.Id.typ with
                   | TTuple [_; _] ->
                       Some([Id.new_var ~name:x.Id.name (fst_typ x.Id.typ), true, x; Id.new_var ~name:x.Id.name (snd_typ x.Id.typ), false, x])
                   | _ -> None)
                  xs)
           in
           if fs' = [] then
             lift_fst_snd.tr2_term fs t
           else
             make_lets
               (List.map
                  (fun (x, bfst, xorig) ->
                   (* ommit the case where x is a pair *)
                   x, if bfst then make_fst (make_var xorig) else make_snd (make_var xorig))
                  fs')
               (lift_fst_snd.tr2_term (fs @ fs') t)))
          (* ommit the case where f is a pair *)
          bindings
      in
      make_let bindings' @@ lift_fst_snd.tr2_term fs t2
  | Proj(0, {desc=Var x}) when tuple_num (Id.typ x) = Some 2 ->
      (try
          let (x, _, _) = List.find (fun (_, bfst, x') -> bfst && Id.(x' = x)) fs in
          make_var x
        with Not_found ->
          make_fst @@ lift_fst_snd.tr2_term fs t)
  | Proj(1, {desc=Var x}) when tuple_num (Id.typ x) = Some 2 ->
      (try
          let (x, _, _) = List.find (fun (_, bfst, x') -> not bfst && Id.(x' = x)) fs in
          make_var x
        with Not_found ->
          make_snd @@ lift_fst_snd.tr2_term fs t)
  | _ -> lift_fst_snd.tr2_term_rec fs t

let () = lift_fst_snd.tr2_term <- lift_fst_snd_term
let lift_fst_snd t = lift_fst_snd.tr2_term [] t





let simplify_match =
  let tr = make_trans () in
  let tr_term t =
    let is_var = function {pat_desc=PVar _} -> true | _ -> false in
    match t.desc with
    | Match(t1, ({pat_desc=PTuple ps}, t2)::_) when List.for_all is_var ps ->
        let xs = List.map (function {pat_desc=PVar x} -> x | _ -> assert false) ps in
        let x = new_var_of_term t1 in
        make_lets ((x,t1) :: List.mapi (fun i y -> y, Term.(proj i (var x))) xs) @@ tr.tr_term t2
    | Match(t1, pats) ->
        let aux (pat,t1) = pat, tr.tr_term t1 in
        let pats' = List.map aux pats in
        let rec elim_unused = function
          | [] -> []
          | (({pat_desc=PAny|PVar _}, _) as pct)::_ -> [pct]
          | pct::pats -> pct :: elim_unused pats
        in
        let pats'' = elim_unused pats' in
        begin
          match pats'' with
          | [] -> assert false
          | [{pat_desc=PAny}, t] -> make_seq t1 t
          | [{pat_desc=PConst {desc=Const Unit}}, t] -> make_seq t1 t
          | [{pat_desc=PVar x}, t] -> make_let [x, t1] t
          | _ -> make_match (tr.tr_term t1) pats''
        end
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term



let should_insert typs = List.for_all (function TFun _ -> true | _ -> false) typs

(* Insert extra parameters into functions with only function arguments.
   Input must be CPS *)

let insert_param_funarg =
  let tr = make_trans () in
  let tr_typ typ =
    match typ with
    | TFun _ as typ ->
        let xs,typ' = decomp_tfun typ in
        let xs' = List.map tr.tr_var xs in
        let xs'' =
          if should_insert @@ List.map Id.typ xs
          then (Id.new_var Ty.unit) :: xs'
          else xs'
        in
        List.fold_right _TFun xs'' @@ tr.tr_typ typ'
    | _ -> tr.tr_typ_rec typ
  in
  let tr_term t =
    let typ = tr.tr_typ t.typ in
    let desc =
      match t.desc with
      | Fun _ ->
          let xs,t' = decomp_funs t in
          let xs' = List.map tr.tr_var xs in
          let xs'' =
            if should_insert @@ List.map Id.typ xs
            then Id.new_var Ty.unit :: xs'
            else xs'
          in
          (make_funs xs'' @@ tr.tr_term t').desc
      | App(t1, ts) ->
          let ts' = List.map tr.tr_term ts in
          let ts'' =
            if should_insert @@ get_argtyps t1.typ
            then unit_term :: ts'
            else ts'
          in
          App(tr.tr_term t1, ts'')
      | _ -> tr.tr_desc_rec t.desc
    in
    {desc; typ; attr=t.attr}
  in
  tr.tr_typ <- tr_typ;
  tr.tr_term <- tr_term;
  fun t ->
    t
    |> tr.tr_term
    |@> Type_check.check ~ty:Term_util.typ_result


let remove_defs =
  let tr = make_trans2 () in
  let remove_defs_desc xs desc =
    match desc with
    | Local(Decl_let bindings, t) ->
        let bindings' = List.filter_out (fun (f,_) -> Id.mem f xs) bindings in
        (make_let bindings' @@ tr.tr2_term xs t).desc
    | _ -> tr.tr2_desc_rec xs desc
  in
  tr.tr2_desc <- remove_defs_desc;
  tr.tr2_term

let rename_ext_funs =
  let fld = make_fold_tr () in
  let fld_desc (funs,tenv,map) desc =
    match desc with
    | Var x when Id.mem x funs ->
        let map',x' =
          try
            let eq x y = can_unify ~tenv (Id.typ x) (Id.typ y) && Id.name x = Id.name y in
            map, List.find (eq x) map
          with Not_found ->
            let x' = Id.new_var_id x in
            x'::map, x'
        in
        (funs,tenv,map'), Var x'
    | Local(Decl_type decls, _) ->
        let tenv' = decls @ tenv in
        fld.fld_desc_rec (funs,tenv',map) desc
    | _ -> fld.fld_desc_rec (funs,tenv,map) desc
  in
  fld.fld_desc <- fld_desc;
  fun funs t ->
    let (_,_,map),t' = fld.fld_term (funs,[],[]) t in
    map, t'

let remove_ext_attr =
  let tr = make_trans () in
  tr.tr_var <- Id.map_attr (List.remove_all -$- Id.External);
  tr.tr_term

let make_ext_fun_def f =
  let xs,typ' = decomp_tfun @@ Id.typ f in
  let xs' = List.map Id.new_var_id xs in
  let make_fun_arg_call x (env,defs,t) =
    let xs,_typ = decomp_tfun @@ Id.typ x in
    let aux typ ((env,defs),args) =
      let (env',defs'),arg = define_rand (env, defs) typ in
      (env', defs'), arg::args
    in
    let (env',defs'),args = List.fold_right aux (List.map Id.typ xs) ((env,defs),[]) in
    let t'' =
      if xs = []
      then t
      else Term.(seq (br unit (ignore (var x @ args))) t)
    in
    env', defs', t''
  in
  let (env,defs),t = define_rand ([],[]) typ' in
  let _,defs',t' = List.fold_right make_fun_arg_call xs' (env,defs,t) in
  f, Term.(funs xs' (let_ defs' t'))

let col_type_decl =
  let col = make_col [] (@) in
  let col_desc desc =
    match desc with
    | Local(Decl_type decls, t1) -> decls :: col.col_term t1
    | _ -> col.col_desc_rec desc
  in
  col.col_desc <- col_desc;
  col.col_term

let remove_type_decl =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(Decl_type _, t1) -> tr.tr_desc t1.desc
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let lift_type_decl t =
  let decls = col_type_decl t in
  let aux (s,ty) acc =
    match List.assoc_opt s acc with
    | None -> (s,ty)::acc
    | Some ty' ->
        if not @@ Type.same_shape ty ty' then
          Format.eprintf "Assume %a is the same as %a@." Print.typ ty Print.typ ty';
        acc
  in
  let decls' = List.fold_right aux (List.flatten decls) [] in
  make_let_type decls' @@ remove_type_decl t


(* order of "env" matters *)
let make_ext_funs ?(fvs=[]) env t =
  let typ_exn = find_exn_typ t in
  let t' = remove_defs (List.map fst env) t in
  Debug.printf "MEF t': %a@." Print.term t';
  Debug.printf "MEF env: %a@." Print.(list (id * Ref_type.print)) env;
  let funs =
    let eq = Id.eq_ty ~eq:can_unify in
    get_fv ~eq t'
    |> List.filter Id.is_external
    |@> Debug.printf "MEF fv: %a@." Print.(list id)
    |> List.filter Id.is_external
    |> List.filter_out Id.is_coefficient
    |> List.filter_out (List.mem_assoc -$- env)
    |> List.filter_out (Id.mem -$- fvs)
    |@> Debug.printf "MEF: %a@." Print.(list id_typ)
    |> List.filter_out (Id.mem_assoc -$- env)
  in
  if List.exists (is_poly_typ -| Id.typ) funs then
    unsupported "Trans.make_ext_funs (polymorphic functions)";
  let map,t'' = rename_ext_funs funs t' in
  Debug.printf "MEF t'': %a@." Print.term' t'';
  let defs1 = List.map make_ext_fun_def map in
  let genv,cenv,defs2 =
    let aux (f,typ) (genv,cenv,defs) =
      let genv',cenv',t = Ref_type_gen.generate typ_exn genv cenv typ in
      let f' = Id.set_typ f @@ Ref_type.to_abst_typ ~with_pred:true typ in
      genv', cenv', (f',t)::defs
    in
    List.fold_right aux env ([],[],[])
  in
  let defs = List.map snd (genv @ cenv) @ defs2 in
  t''
  |> make_lets defs1
  |> make_lets defs
  |> remove_id_let
  |> remove_ext_attr
  |> lift_type_decl

let assoc_typ =
  let col = make_col2 [] (@@@) in
  let col_desc f desc =
    match desc with
    | Local(Decl_let bindings, t1) ->
        let aux (g,t) =
          let typs1 = if Id.(f = g) then [Id.typ g] else [] in
          typs1 @@@ col.col2_term f t
        in
        col.col2_term f t1 @@@ List.rev_flatten_map aux bindings
    | _ -> col.col2_desc_rec f desc
  in
  col.col2_desc <- col_desc;
  fun f t ->
    match col.col2_term f t with
    | [] -> raise Not_found
    | [typ] -> typ
    | _ -> Debug.printf "VAR:%a@.PROG:%a@." Id.print f Print.term t; assert false

let inline_no_effect =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(Decl_let [x,t], {desc=Var y}) when Id.(x = y) && not @@ Id.mem x @@ get_fv t ->
        (tr.tr_term t).desc
    | Local(Decl_let [x,t], t2) when Id.mem x (get_fv t2) && has_no_effect t && not @@ Id.mem x @@ get_fv t ->
        let t' = tr.tr_term t in
        let t2' = tr.tr_term t2 in
        (subst x t' t2').desc
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let beta_no_effect =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | App(t1, [t2]) ->
        let t1' = tr.tr_term t1 in
        let t2' = tr.tr_term t2 in
        begin
          match t1'.desc with
          | Fun(x,t1'') when has_no_effect t2' -> (subst x t2' t1'').desc
          | _ -> App(t1', [t2'])
        end
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let rec diff_terms t1 t2 =
  match t1.desc, t2.desc with
  | Const(Rand(typ1,b1)), Const(Rand(typ2,b2)) ->
      if Type.same_shape typ1 typ2 && b1 = b2
      then []
      else [t1,t2]
  | Const c1, Const c2 -> if c1 = c2 then [] else [t1,t2]
  | Var x1, Var x2 -> if Id.(x1 = x2) then [] else [t1,t2]
  | Fun _, Fun _ -> [t1,t2]
  | App(t11,[t12]), App(t21,[t22]) -> diff_terms t11 t21 @ diff_terms t12 t22
  | App(t1,ts1), App(t2,ts2) ->
      let ts1',t12 = List.decomp_snoc ts1 in
      let ts2',t22 = List.decomp_snoc ts2 in
      let t1' = {desc=App(make_app t1 ts1', [t12]); typ=t1.typ; attr=[]} in
      let t2' = {desc=App(make_app t2 ts2', [t22]); typ=t2.typ; attr=[]} in
      diff_terms t1' t2'
  | If(t11,t12,t13), If(t21,t22,t23) ->
      diff_terms t11 t21 @ diff_terms t12 t22 @ diff_terms t13 t23
  | Local(Decl_let _bindings1,t1), Local(Decl_let _bindings2,t2) -> [t1,t2]
  | BinOp(op1,t11,t12), BinOp(op2,t21,t22) ->
      if op1 = op2
      then diff_terms t11 t21 @ diff_terms t12 t22
      else [t1,t2]
  | Not t1, Not t2 -> diff_terms t1 t2
  | Event(s1,b1), Event(s2,b2) -> if s1 = s2 && b1 = b2 then [] else [t1,t2]
  | Record _, Record _ -> [t1,t2] (* Not implemented *)
  | Field _, Field _ -> [t1,t2] (* Not implemented *)
  | SetField _, SetField _ -> [t1,t2] (* Not implemented *)
  | Nil, Nil -> []
  | Cons(t11,t12), Cons(t21,t22) ->
      diff_terms t11 t21 @ diff_terms t12 t22
  | Constr _, Constr _ -> [t1,t2] (* Not implemented *)
  | Match _, Match _ -> [t1,t2] (* Not implemented *)
  | Raise _, Raise _ -> [t1,t2] (* Not implemented *)
  | TryWith _, TryWith _ -> [t1,t2] (* Not implemented *)
  | Tuple ts1, Tuple ts2 ->
      List.flatten @@ List.map2 diff_terms ts1 ts2
  | Proj(i,t1), Proj(j,t2) when i = j -> diff_terms t1 t2
  | Bottom, Bottom -> []
  | Label _, Label _ -> [t1,t2]
  | _ -> [t1, t2]

let subst_let_xy =
  let tr = make_trans () in
  let tr_desc desc =
    let desc' = tr.tr_desc_rec desc in
    match desc with
    | Local(Decl_let bindings, _) when is_non_rec bindings ->
        let bindings',t' =
          match desc' with
          | Local(Decl_let bindings', t') when is_non_rec bindings' -> bindings', t'
          | _ -> assert false
        in
        let sbst bind t =
          match bind with
          | (x, ({desc=Var _} as t')) -> subst x t' t
          | _ -> raise Not_found
        in
        let bindings1,bindings2 =
          let check bind =
            try
              ignore @@ sbst bind unit_term;
              true
            with Not_found -> false
          in
          List.partition check bindings'
        in
        (make_let bindings2 @@ List.fold_right sbst bindings1 t').desc
    | _ -> desc'
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let flatten_let =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | Local(Decl_let [x,t1], t2) when is_non_rec [x,t1] ->
        let t1' = tr.tr_term t1 in
        let t2' = tr.tr_term t2 in
        begin match t1'.desc with
        | Local _ ->
            let fbindings,t12 = decomp_lets t1' in
            let fbindings' = fbindings @ [[x,t12]] in
            List.fold_right make_let fbindings' t2'
        | _ ->
            make_let [x,t1'] t2'
        end
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let normalize_let =
  let tr = make_trans2 () in
  let tr_aux is_atom t =
    match t.desc with
    | Var _ -> t, Fun.id
    | _ when is_atom t -> t, Fun.id
    | _ ->
        let post t' =
          match t'.desc with
          | BinOp _ | App _ | Tuple _ | Proj _ ->
              let y = new_var_of_term t' in
              make_lets [y,t'] @@ make_var y
          | _ -> t'
        in
        let x = new_var_of_term t in
        let t' = tr.tr2_term is_atom t in
        let post' t'' = make_let [x,t'] @@ post t'' in
        make_var x, post'
  in
  let tr_term is_atom t =
    match t.desc with
    | _ when is_atom t -> t
    | BinOp(op,t1,t2) ->
        let t1',post1 = tr_aux is_atom t1 in
        let t2',post2 = tr_aux is_atom t2 in
        post1 @@ post2 @@ make_binop op t1' t2'
    | Not t1 ->
        let t1',post = tr_aux is_atom t1 in
        post @@ make_not t1'
    | App(t, ts) ->
        let ts',posts = List.split_map (tr_aux is_atom) ts in
        let t',post = tr_aux is_atom t in
        let post' = List.fold_left (|-) post posts in
        post' @@ make_app t' ts'
    | Tuple ts ->
        let ts',posts = List.split_map (tr_aux is_atom) ts in
        List.fold_right (@@) posts @@ make_tuple ts'
    | Proj(i,t) ->
        let t',post = tr_aux is_atom t in
        post @@ make_proj i t'
    | If(t1, t2, t3) ->
        let t1',post = tr_aux is_atom t1 in
        let t2'  = tr.tr2_term is_atom t2 in
        let t3'  = tr.tr2_term is_atom t3 in
        post @@ add_attrs t.attr @@ make_if t1' t2' t3'
    | Raise t1 ->
        let t1',post = tr_aux is_atom t1 in
        post @@ make_raise t1' t.typ
    | _ -> tr.tr2_term_rec is_atom t
  in
  tr.tr2_term <- tr_term;
  tr.tr2_typ <- Fun.snd;
  fun ?(is_atom=fun _ -> false) -> tr.tr2_term is_atom

let inline_var =
  let tr = make_trans () in
  let tr_term t =
    let t' = tr.tr_term_rec t in
    match t'.desc with
    | Local(Decl_let [x,({desc=Var _} as t1)], t2) -> subst x t1 t2
    | _ -> t'
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let rec is_const t =
  match t.desc with
  | Var _ -> true
  | Const _ -> true
  | Tuple ts -> List.for_all is_const ts
  | _ -> false

let inline_var_const =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | Local(Decl_let [x,t1], t2) when is_const t1 && not @@ List.mem ADoNotInline t.attr ->
        subst ~rename_if_captured:true x t1 @@ tr.tr_term t2
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let remove_label =
  let tr = make_trans2 () in
  let tr_term label t =
    match label, t.desc with
    | None, Label(_, t1) -> tr.tr2_term label t1
    | Some l, Label(InfoString l', {desc=Label(_, t1)}) when l = l' -> tr.tr2_term label t1
    | Some l, Label(InfoString l', t1) when l = l' -> tr.tr2_term label t1
    | _ -> tr.tr2_term_rec label t
  in
  tr.tr2_term <- tr_term;
  fun ?(label="") t -> tr.tr2_term (if label="" then None else Some label) t

let decomp_pair_eq =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | BinOp(Eq, t1, t2) ->
        begin match t1.typ with
        | TTuple xs ->
            let aux t =
              match t with
              | {desc=Var y} -> y, Fun.id
              | _ ->
                  let y = new_var_of_term t in
                  y, make_let [y,t]
            in
            let y1,post1 = aux @@ tr.tr_term t1 in
            let y2,post2 = aux @@ tr.tr_term t2 in
            let ts = List.mapi Term.(fun i _ -> proj i (var y1) = proj i (var y2)) xs in
            post2 @@ post1 @@ List.fold_left make_and true_term ts
        | _ -> tr.tr_term_rec t
        end
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let elim_unused_let =
  let tr = make_trans2 () in
  let tr_term (leave,cbv,div) t =
    let has_no_effect' t = has_no_effect t || has_safe_attr t in
    let t' = tr.tr2_term_rec (leave,cbv,div) t in
    let flag = List.mem ADoNotInline t.attr in
    if flag then
      t'
    else
      let desc =
        match t'.desc with
        | Local(Decl_let bindings, t1) ->
            let fv = get_fv t1 in
            let dummy = Id.new_var Ty.int in
            let deps =
              let deps1 = List.map (fun x -> dummy, x) fv in
              let deps2 = List.flatten_map (fun (f,t) -> List.map (fun x -> f, x) @@ get_fv t) bindings in
              transitive_closure ~eq:Id.eq (deps1@deps2)
            in
            let cannot_be_removed (f,t) =
              Id.mem f leave ||
              List.exists Id.(fun (x,y) -> x = dummy && y = f) deps ||
              cbv && (if div then not (has_safe_attr t) else not (has_no_effect' t))
            in
            let bindings' = List.filter cannot_be_removed bindings in
            (make_let bindings' t1).desc
        | _ -> t'.desc
      in
      {t' with desc}
  in
  tr.tr2_term <- tr_term;
  fun ?(leave_last=false) ?(cbv=true) ?(elim_may_div=false) t ->
    let leave =
      if leave_last then
        List.map fst @@ get_last_definition t
      else
        []
    in
    tr.tr2_term (leave,cbv,elim_may_div) t

let subst_with_rename =
  let tr = make_trans2 () in
  let tr_desc (x,t) desc =
    match desc with
    | Var y when Id.(x = y) -> (alpha_rename t).desc
    | Fun(y, _) when Id.(x = y) -> desc
    | Local(Decl_let bindings, t2) when is_non_rec bindings ->
        let aux (f,t1) = tr.tr2_var (x,t) f, tr.tr2_term (x,t) t1 in
        let bindings' = List.map aux bindings in
        let t2' =
          if List.exists (Id.same x -| fst) bindings
          then t2
          else tr.tr2_term (x,t) t2
        in
        Local(Decl_let bindings', t2')
    | Local(Decl_let bindings, _) when List.exists (Id.same x -| fst) bindings -> desc
    | Local(Decl_let bindings, t2) ->
        let aux (f,t1) =
          tr.tr2_var (x,t) f,
          tr.tr2_term (x,t) t1
        in
        let bindings' = List.map aux bindings in
        let t2' = tr.tr2_term (x,t) t2 in
        Local(Decl_let bindings', t2')
    | Match(t1,pats) ->
        let aux (pat,t1) =
          let xs = get_bv_pat pat in
          if List.exists (Id.same x) xs
          then pat, t1
          else pat, tr.tr2_term (x,t) t1
        in
        Match(tr.tr2_term (x,t) t1, List.map aux pats)
    | _ -> tr.tr2_desc_rec (x,t) desc
  in
  tr.tr2_desc <- tr_desc;
  fun ?(check=false) x t1 t2 ->
    if check && count_occurrence x t2 = 1
    then subst x t1 t2
    else tr.tr2_term (x,t1) t2

let elim_unused_branch =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | If({desc=Const True}, t1, _) -> tr.tr_term t1
    | If({desc=Const False}, _, t2) -> tr.tr_term t2
    | If({desc=BinOp(Eq,{desc=Var x},{desc=Var y})}, t1, _) when Id.(x = y) -> tr.tr_term t1
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let inline_simple_exp =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | Local(Decl_let [x,t1],t2) when is_simple_aexp t1 || is_simple_bexp t1 ->
        tr.tr_term @@ subst x t1 t2
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let replace_base_with_int,replace_base_with_int_typ =
  let hash_of_const c =
    match c with
    | Char c -> int_of_char c
    | _ -> Hashtbl.hash c
  in
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Const(Char _ | String _ | Float _ | Int32 _ | Int64 _ | Nativeint _ as c) ->
        Flag.Abstract.use "Base with int";
        Const (Int (hash_of_const c))
    | Const(Rand(TBase (TPrim _), b)) ->
        Flag.Abstract.use "Base with int";
        Const (Rand(Ty.int,b))
    | _ -> tr.tr_desc_rec desc
  in
  let tr_typ typ =
    match typ with
    | TBase (TPrim _) -> Ty.int
    | _ -> tr.tr_typ_rec typ
  in
  let tr_pat p =
    match p.pat_desc with
    | PConst {desc=Const(Char _|String _|Float _|Int32 _|Int64 _|Nativeint _)} -> {pat_desc=PNondet; pat_typ=TBase TInt}
    | _ -> tr.tr_pat_rec p
  in
  tr.tr_desc <- tr_desc;
  tr.tr_typ <- tr_typ;
  tr.tr_pat <- tr_pat;
  tr.tr_term, tr.tr_typ

let remove_top_por =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | Match(t, pats) ->
        let aux (p,t2) =
          let rec flatten p =
            match p.pat_desc with
            | POr(p1,p2) -> flatten p1 @ flatten p2
            | _ -> [p]
          in
          let t2' = alpha_rename @@ tr.tr_term t2 in
          List.map (fun p -> p, t2') @@ flatten p
        in
        let t' = tr.tr_term t in
        make_match t' @@ List.flatten_map aux pats
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let short_circuit_eval =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | _ when has_no_effect t -> tr.tr_term_rec t
    | BinOp(And, t1, t2) -> make_if (tr.tr_term t1) (tr.tr_term t2) false_term
    | BinOp(Or, t1, t2) -> make_if (tr.tr_term t1) true_term (tr.tr_term t2)
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

(* input is assumed to be a CBN-program *)
let expand_let_val =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | Local(Decl_let bindings, t2) ->
        let bindings' = List.map (Pair.map_snd tr.tr_term) bindings in
        let t2' = tr.tr_term t2 in
        let bindings2,bindings1 = List.partition (is_fun -| snd) bindings' in
        let t2'' = List.fold_left (fun t (f,t') -> subst_with_rename f t' t) t2' bindings1 in
        let attr = if bindings2 = [] then t.attr @ t2''.attr else t.attr in
        {(make_let bindings2 t2'') with attr}
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let rec eval_aexp t =
  match t.desc with
  | Const (Int n) -> n
  | Var _ -> invalid_arg "eval_aexp"
  | BinOp(op, t1, t2) ->
      let f =
        match op with
        | Add -> (+)
        | Sub -> (-)
        | Mult -> ( * )
        | Div -> (/)
        | _ -> invalid_arg "eval_aexp"
      in
      f (eval_aexp t1) (eval_aexp t2)
  | _ -> invalid_arg "eval_aexp"

let rec eval_bexp t =
  match t.desc with
  | Const True -> true
  | Const False -> false
  | Var _ -> invalid_arg "eval_bexp"
  | BinOp((Eq|Lt|Gt|Leq|Geq) as op, t1, t2) ->
      let f =
        match op with
        | Eq -> (=)
        | Lt -> (<)
        | Gt -> (>)
        | Leq -> (<=)
        | Geq -> (>=)
        | _ -> invalid_arg "eval_bexp"
      in
      f (eval_aexp t1) (eval_aexp t2)
  | BinOp((And|Or) as op, t1, t2) ->
      let f =
        match op with
        | And -> (&&)
        | Or -> (||)
        | _ -> invalid_arg "eval_bexp"
      in
      f (eval_bexp t1) (eval_bexp t2)
  | Not t -> not @@ eval_bexp t
  | _ -> false

(* input is assumed to be a CBN-program *)
let beta_reduce =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | Local(Decl_let [x,{desc=Var y}], t1) ->
        tr.tr_term @@ subst_with_rename ~check:true x (make_var y) t1
    | App(t1, []) ->
        tr.tr_term t1
    | App(t1, t2::ts) ->
        begin
          match tr.tr_term t1 with
          | {desc=Fun(x,t1')} -> tr.tr_term @@ make_app (subst_with_rename ~check:true x t2 t1') ts
          | t1' -> make_app t1' @@ List.map tr.tr_term (t2::ts)
        end
    | Proj(i, {desc=Tuple ts}) -> tr.tr_term @@ List.nth ts i
    | If(t1,t2,t3) when is_simple_bexp t1 && get_fv t1 = [] ->
        tr.tr_term @@ if eval_bexp t1 then t2 else t3
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let replace_bottom_def =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(Decl_let [f,t1], t2) when is_bottom_def f t1 ->
        let xs,t1 = decomp_funs t1 in
        Local(Decl_let [f, make_funs xs @@ make_bottom t1.typ], tr.tr_term t2)
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let flatten_tuple =
  let tr = make_trans () in
  let tr_typ typ =
    match typ with
    | TTuple xs ->
        let xs' = List.map tr.tr_var xs in
        let ys = List.flatten_map (fun x -> match Id.typ x with TTuple xs -> xs | _ -> [x]) xs' in
        TTuple ys
    | _ -> tr.tr_typ_rec typ
  in
  let make_proj' i t =
    match t.typ with
    | TTuple _ -> make_proj i t
    | _ -> assert (i=0); t
  in
  let make_tuple' ts =
    match ts with
    | [] -> assert false
    | [t] -> t
    | _ -> make_tuple ts
  in
  let tr_term t =
    match t.desc with
    | Match _ -> unsupported "not implemented: flatten_tuple (match)"
    | Proj(i,t1) ->
        let t1' = tr.tr_term t1 in
        let x = Id.add_name_after (string_of_int i) (new_var_of_term t1') in
        let ns = List.map (fun typ -> match tr.tr_typ typ with TTuple xs' -> List.length xs' | _ -> 1) @@ decomp_ttuple t1.typ in
        let rec new_pos i j acc ns =
          match ns with
          | [] -> assert false
          | n::ns' ->
              if i = j
              then List.map ((+) acc) @@ List.fromto 0 n
              else new_pos i (j+1) (n+acc) ns'
        in
        make_let [x,t1'] @@ make_tuple' @@ List.map (make_proj' -$- make_var x) @@ new_pos i 0 0 ns
    | Tuple ts ->
        let ts' = List.map tr.tr_term ts in
        let xs' = List.map new_var_of_term ts' in
        let aux y =
          let ys = match Id.typ y with TTuple ys -> ys | _ -> [y] in
          let aux2 i _ =
            let t = make_proj' i @@ make_var y in
            let y' = new_var_of_term t in
            y', (y', t) in
          let ys',defs = List.split @@ List.mapi aux2 ys in
          make_lets defs,
          List.map make_var ys'
        in
        let conts,tss = List.split @@ List.map aux xs' in
        make_lets (List.combine xs' ts') @@ List.fold_left (|>) (make_tuple' @@ List.flatten tss) conts
    | _ -> tr.tr_term_rec t
  in
  tr.tr_typ <- tr_typ;
  tr.tr_term <- tr_term;
  tr.tr_term

let rec is_in_redex x t =
  match t.desc with
  | Var y -> Some Id.(x = y)
  | Const _ -> Some false
  | Tuple ts ->
      let rs = List.map (is_in_redex x) ts in
      List.fold_right (fun r acc -> match acc with None -> None | Some b -> Option.map ((||) b) r) rs (Some false)
  | Proj(_,t1) -> is_in_redex x t1
  | Local(Decl_let bindings, t1) when List.for_all (function (_,{desc=Fun _}) -> true | _ -> false) bindings ->
      is_in_redex x t1
  | _ -> None

let inline_next_redex =
  let tr = make_trans () in
  let can_inline x t =
    count_occurrence x t = 1 &&
    Option.default false @@ is_in_redex x t
  in
  let tr_term t =
    match t.desc with
    | Local(Decl_let [x,t1], t2) when is_non_rec [x,t1] ->
        let t1' = tr.tr_term t1 in
        let t2' = tr.tr_term t2 in
        if can_inline x t2'
        then subst x t1' t2'
        else tr.tr_term_rec t
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let beta_var_tuple =
  let tr = make_trans2 () in
  let tr_term env t =
    match t.desc with
    | Local(Decl_let [x,({desc=Tuple ts} as t1)], t2) when is_non_rec [x,t1] ->
        let xs = List.map (function {desc=Var x} -> Some x | _ -> None) ts in
        if List.for_all Option.is_some xs then
          let xs' = List.map Option.get xs in
          make_let [x,t1] @@ tr.tr2_term ((x,xs')::env) t2
        else
          tr.tr2_term_rec env t
    | Proj(i,{desc=Var x}) when Id.mem_assoc x env -> make_var @@ List.nth (Id.assoc x env) i
    | _ -> tr.tr2_term_rec env t
  in
  tr.tr2_term <- tr_term;
  tr.tr2_term []

let beta_no_effect_tuple =
  let tr = make_trans2 () in
  let tr_term env t =
    match t.desc with
    | Local(Decl_let [x,({desc=Tuple ts} as t1)], t2) when is_non_rec [x,t1] ->
        if List.for_all has_no_effect ts
        then make_let [x,t1] @@ tr.tr2_term ((x,ts)::env) t2
        else tr.tr2_term_rec env t
    | Proj(i,{desc=Var x}) when Id.mem_assoc x env -> List.nth (Id.assoc x env) i
    | _ -> tr.tr2_term_rec env t
  in
  tr.tr2_term <- tr_term;
  tr.tr2_term []

let reduce_bottom =
  let tr = make_trans () in
  let tr_term t =
    let t' = tr.tr_term_rec t in
    match t'.desc with
    | Local(Decl_let [_,{desc=Bottom}], _) -> make_bottom t.typ
    | _ -> t'
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let merge_bound_var_typ =
  let tr = make_trans2 () in
  let tr_typ_desc map desc =
    match desc with
    | Local(Decl_let bindings,t) ->
        let aux (f,t) =
          let f' =
            try
              let typ = Id.assoc f map in
              Id.map_typ (merge_typ typ) f
            with Not_found -> f
          in
          let t' = tr.tr2_term map t in
          f', t'
        in
        let bindings' = List.map aux bindings in
        let t' = tr.tr2_term map t in
        Local(Decl_let bindings', t')
    | _ -> tr.tr2_desc_rec map desc
  in
  tr.tr2_desc <- tr_typ_desc;
  fun map t ->
    t
    |> tr.tr2_term map
    |> propagate_typ_arg

let rename_poly_funs =
  let fld = make_fold_tr () in
  let can_unify tenv f (_,g) = can_unify ~tenv (Id.typ f) (Id.typ g) in
  let find_and_copy fs map tenv x =
    match List.find_opt (List.exists (can_unify tenv x)) map with
    | None ->
        let x_map : (id * id) list =
          let copy f (env,acc) =
            let env, ty = copy_tvar_typ ~env @@ Id.typ f in
            if Id.(x = f) then unify (Id.typ x) ty;
            let f' = Id.set_typ f ty in
            let g = Id.new_var_id f' in
            env, (f',g)::acc
          in
          snd @@ List.fold_right copy fs ([],[])
        in
        let x' = Id.assoc x x_map in
        x_map::map, x'
    | Some x_map ->
        map, Id.assoc x x_map
  in
  let fld_list focus fs map tenv xs =
    let aux x (map,acc) =
      let ctx,t = focus x in
      let (_,map',_),t' = fld.fld_term (fs,map,tenv) t in
      map', ctx t'::acc
    in
    List.fold_right aux xs (map,[])
  in
  let fld_desc (fs,(map:(id * id) list list),tenv) desc =
    match desc with
    | Var x when Id.mem x fs ->
        assert (not @@ is_poly_typ @@ Id.typ x);
        let map',x' = find_and_copy fs map tenv x in
        (fs,map',tenv), Var x'
    | Fun(x, t) ->
        let fs' = List.filter_out Id.(eq x) fs in
        let (_,map',_),t' = fld.fld_term (fs',map,tenv) t in
        (fs,map',tenv), Fun(x, t')
    | Local(Decl_let bindings, t) ->
        let fs' = List.filter_out (Id.mem_assoc -$- bindings) fs in
        let (_,map,_),t' = fld.fld_term (fs',map,tenv) t in
        let map, bindings' = fld_list Focus.snd fs' map tenv bindings in
        (fs,map,tenv), Local(Decl_let bindings', t')
    | App({desc=Var x}, ts) when Id.mem x fs ->
        let map,ts' = fld_list Focus.id fs map tenv ts in
        let map',x' = find_and_copy fs map tenv x in
        (fs,map',tenv), App(make_var x', ts')
    | Local(Decl_type tenv', t) ->
        let tenv'' = tenv'@tenv in
        let (_,map',_),t' = fld.fld_term (fs,map,tenv'') t in
        (fs,map',tenv), Local(Decl_type tenv', t')
    | Match(_,pats) when List.exists (fun (p,_) -> List.exists (Id.mem -$- fs) (get_bv_pat p)) pats -> unsupported "rename_poly_funs Match"
    | _ -> fld.fld_desc_rec (fs,map,tenv) desc
  in
  fld.fld_desc <- fld_desc;
  fun fs t ->
    let (_,map,_),t' = fld.fld_term (fs,[],[]) t in
    map, t'

let copy_poly_ext_funs ?eq t =
  let eq =
    match eq with
    | None ->
        let tenv = col_decl_type t in
        fun x y -> Id.(x = y) && can_unify ~tenv (Id.typ x) (Id.typ y)
    | Some eq -> eq
  in
  let fv_map =
    let fv = get_fv ~eq t in
    fv
    |> List.filter (fun x -> 2 <= List.count (Id.eq x) fv)
    |> List.map (Pair.add_right Id.new_var_id)
  in
  let aux t =
    match t.desc with
    | Var x ->
        List.assoc_opt ~eq x fv_map
        |> Option.map Term.var
    | _ -> None
  in
  trans_if aux t

let copy_poly_funs =
  let fld = make_fold_tr () in
  let fld_desc (eq,map) desc =
    match desc with
    | Local(Decl_let bindings, t2) when List.exists (is_poly_typ -| Id.typ -| fst) bindings ->
        Debug.printf "POLY %a:@." Print.(list id_typ) (List.map fst bindings);
        let (_,map),t2' = fld.fld_term (eq,map) t2 in
        let fs = List.map fst bindings in
        let map_renames,t2'' = rename_poly_funs fs t2' in
        let map_renames,t2''' =
          match map_renames with
          | [] -> [List.map Pair.copy fs], t2'
          | [map_rename] ->
              [List.map (fun (f,g) -> f, Id.set_id g (Id.id f)) map_rename], t2'
          | _ -> map_renames, t2''
        in
        Debug.printf "@[<hv 2>COPY%a:@ %a@.@." Print.(list id_typ) fs Print.(list (list id_typ)) (List.map (List.map snd) map_renames);
        let map,bindingss =
          let copy bindings =
            let aux (x,t) (env,acc) =
              let env,x_ty = copy_tvar_typ ~env @@ Id.typ x in
              let x' = Id.set_typ x x_ty in
              let env,t' = copy_tvar ~env t in
              env, (x',t')::acc
            in
            snd @@ List.fold_right aux bindings ([],[])
          in
          let make map map_rename =
            let bindings' = copy bindings in
            List.iter2 (fun (f,_) (f',_) -> unify (Id.typ f) (Id.typ f')) bindings' map_rename;
            let aux (x,t) (map,acc) =
              let x' = Id.assoc x map_rename in
              let (_,map),t' =
                t
                |> subst_var_map map_rename
                |> fld.fld_term (eq,map)
                |@> inst_tvar Ty.unit -| snd
              in
              map, (x',t')::acc
            in
            List.fold_right aux bindings' (map,[])
          in
          let aux (map,bindingss) map_rename =
            let map,bindings = make map map_rename in
            map_rename@map, bindings::bindingss
          in
          List.fold_left aux (map,[]) map_renames
        in
        let t = List.fold_right Term.let_ bindingss t2''' in
        if !!Debug.check then Type_check.check ~ty:t.typ t;
        (eq,map), t.desc
    | _ -> fld.fld_desc_rec (eq,map) desc
  in
  let fld_typ eqmap ty = inst_tvar_typ Ty.unit ty; eqmap, ty in
  fld.fld_desc <- fld_desc;
  fld.fld_typ <- fld_typ;
  fun t ->
    unify_pattern_var t;
    let tenv = col_decl_type t in
    let eq x y = Id.(x = y) && can_unify ~tenv (Id.typ x) (Id.typ y) in
    let (_,map),t' = fld.fld_term (eq,[]) t in
    let make_get_rtyp get_rtyp f =
      let fs = List.assoc_all ~eq:Id.eq f map in
      if fs = [] then raise Not_found;
      Ref_type.Inter(Id.typ f, List.map get_rtyp fs)
    in
    copy_poly_ext_funs ~eq t', make_get_rtyp

let rec map_main f t =
  match t.desc with
  | Local(decls, t') ->
      let desc = Local(decls, map_main f t') in
      {t with desc}
  | _ -> f t

let rec replace_main ?(force=false) ~main t =
  match t.desc with
  | Local(Decl_let bindings, t2) ->
      make_let bindings @@ replace_main ~force ~main t2
  | Local(Decl_type decls, t2) ->
      make_let_type decls @@ replace_main ~force ~main t2
  | Const Unit -> main
  | End_of_definitions -> main
  | Var x when Id.typ x = Ty.unit -> main
  | Tuple [] -> main
  | _ when force -> main
  | _ -> assert false

let main_name = "main"

let replace_main_wrap ?(force=false) main t =
  let u = Id.new_var ~name:main_name main.typ in
  replace_main ~force ~main:Term.(let_ [u, main] unit) t

let get_set_main t =
  match List.decomp_snoc_opt @@ get_last_definition t with
  | Some (_, (x, _)) when Id.name x = main_name -> Some x
  | _ -> None

let ref_to_assert ?(make_fail=make_fail ?loc:None ~force:true) ?typ_exn ref_env t =
  let typ_exn =
    match typ_exn with
    | None -> find_exn_typ t
    | Some typ -> Some typ
  in
  let ref_env = Ref_type.Env.to_list ref_env in
  let main =
    let aux (f, typ) =
      if not @@ can_unify (Id.typ f) (Ref_type.to_simple typ) then
        begin
          Format.eprintf "VAR: %a@." Id.print f;
          Format.eprintf "  Prog: %a@." Print.typ @@ Id.typ f;
          Format.eprintf "  Spec: %a@." Ref_type.print typ;
          fatal @@ Format.sprintf "Type of %s in the specification is wrong?" @@ Id.name f
        end;
      let genv',cenv',t_typ = Ref_type_gen.generate_check typ_exn ~make_fail [] [] f typ in
      let defs = List.map snd (genv' @ cenv') in
      make_lets defs @@ make_assert t_typ
    in
    let ts = List.map aux ref_env in
    Term.(seqs ts unit)
  in
  let map = List.map (Pair.map_snd Ref_type.to_abst_typ) ref_env in
  merge_bound_var_typ map @@ replace_main_wrap main t

let make_main catch_all f =
  let xs = get_args (Id.typ f) in
  let bindings =
    let aux i x =
      let x' = Id.new_var ~name:("arg" ^ string_of_int @@ i+1) @@ Id.typ x in
      let t = inst_randval @@ make_rand_unit @@ Id.typ x in
      x', t
    in
    List.mapi aux xs
  in
  let ys = List.map fst bindings in
  Term.(lets bindings (catch_all (var f @ vars ys)))

let set_main t =
  let catch_all = make_catch_all t in
  match List.decomp_snoc_opt @@ get_last_definition t with
  | None ->
      let u = Id.new_var ~name:"main" t.typ in
      Term.(let_ [u, catch_all t] unit)
  | Some(_, (f,_)) ->
      let main = make_main catch_all f in
      replace_main_wrap main t

let set_main_for ?(force=false) targets t =
  let catch_all = make_catch_all t in
  match get_last_definition t with
  | [] ->
      Term.ignore (catch_all t)
  | _ ->
      let main = Term.tuple (List.map (make_main catch_all) targets) in
      replace_main_wrap ~force main t
      |> elim_unused_let

let recover_const_attr_shallowly t =
  let attr =
    match t.desc with
    | BinOp(_, t1, t2) -> make_attr [t1; t2]
    | Not t -> make_attr [t]
    | If(t1, t2, t3) -> make_attr [t1; t2; t3]
    | Proj(_, t) -> make_attr [t]
    | _ -> []
  in
  {t with attr = List.Set.(attr + t.attr)}


let recover_const_attr =
  let tr = make_trans () in
  tr.tr_term <- recover_const_attr_shallowly -| tr.tr_term_rec;
  tr.tr_term


let beta_reduce_trivial =
  let tr = make_trans2 () in
  let tr_term env t =
    match t.desc with
    | App({desc=Var f}, ts) ->
        begin
          try
            let n,t = Id.assoc f env in
            let check t = has_no_effect t || List.Set.([ATerminate;ANotFail] <= t.attr) in
            let ts' = List.map (tr.tr2_term env) ts in
            if n = List.length ts && List.for_all check ts'
            then alpha_rename t
            else raise Not_found
          with Not_found -> tr.tr2_term_rec env t
        end
    | Local(Decl_let bindings, t1) ->
        let env' =
          let aux (f,t) =
            let xs,t = decomp_funs t in
            if get_fv t = [] then Some (f,(List.length xs,t)) else None
          in
          List.filter_map aux bindings @ env
        in
        let bindings' = List.map (Pair.map_snd @@ tr.tr2_term env') bindings in
        make_let bindings' @@ tr.tr2_term env' t1
    | _ -> tr.tr2_term_rec env t
  in
  tr.tr2_term <- (fun env t -> recover_const_attr_shallowly @@ tr_term env t);
  fun t ->
    t
    |> tr.tr2_term []
    |> elim_unused_let
    |> inline_var_const


let exists_exception =
  let col = make_col false (||) in
  let col_desc desc =
    match desc with
    | Event("fail", _) -> true
    | Raise _ -> true
    | _ -> col.col_desc_rec desc
  in
  col.col_desc <- col_desc;
  col.col_term


let ignore_non_termination =
  let tr = make_trans2 () in
  let tr_desc fail_free desc =
    match desc with
    | App({desc=Var f}, ts) when Id.mem f fail_free && can_unify Ty.unit (make_app (make_var f) ts).typ->
        Const Unit
    | Local(Decl_let bindings, t1) ->
        let bindings' = List.map (Pair.map_snd @@ tr.tr2_term fail_free) bindings in
        let fv = get_fv t1 in
        let check t =
          let xs,t = decomp_funs t in
          List.for_all (Type.is_base_typ -| Id.typ) xs &&
          List.Set.(get_fv t <= (xs @@@ fail_free)) &&
          not @@ exists_exception t
        in
        let fail_free' = List.filter_map (fun (f,t) -> if check t then Some f else None) bindings' in
        let bindings'' = List.filter_out (fun (f,_) -> Id.mem f fail_free' && not @@ Id.mem f fv) bindings' in
        (make_let bindings'' @@ tr.tr2_term (fail_free'@@@fail_free) t1).desc
    | _ -> tr.tr2_desc_rec fail_free desc
  in
  tr.tr2_desc <- tr_desc;
  tr.tr2_term []


let null_tuple_to_unit =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Tuple [] -> Const Unit
    | _ -> tr.tr_desc_rec desc
  in
  let tr_typ typ =
    match typ with
    | TTuple [] -> Ty.unit
    | _ -> tr.tr_typ_rec typ
  in
  tr.tr_desc <- tr_desc;
  tr.tr_typ <- tr_typ;
  tr.tr_term


let beta_full_app =
  let tr = make_trans2 () in
  let tr_desc (f,xs,t) desc =
    match desc with
    | App({desc=Var g}, ts) when Id.(f = g) && List.length xs = List.length ts ->
        (List.fold_right2 (subst_with_rename ~check:true) xs ts t).desc
    | _ -> tr.tr2_desc_rec (f,xs,t) desc
  in
  tr.tr2_desc <- tr_desc;
  tr.tr2_term


let beta_affine_fun =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(Decl_let [f, ({desc=Fun _} as t1)], t2) when is_non_rec [f,t1]  ->
        let xs,t1 = decomp_funs t1 in
        let t1' = tr.tr_term t1 in
        begin
          match t1'.desc with
          | App _ ->
              let used = List.Set.inter ~eq:Id.eq xs @@ get_fv ~eq:(fun _ _ -> false) t1' in
              let not_rand_int t = (* for non-termination *)
                match t.desc with
                | App({desc=Const(Rand(TBase TInt,_))}, _) -> false
                | _ -> true
              in
              if used = List.unique ~eq:Id.eq used &&
                 not_rand_int t1 &&
                 count_occurrence f t2 <= 1
              then
                let t2' =
                  t2
                  |> tr.tr_term
                  |> beta_full_app (f, xs, t1')
                  |> tr.tr_term
                in
                if Id.mem f @@ get_fv t2'
                then Local(Decl_let [f, make_funs xs t1'], t2')
                else t2'.desc
              else tr.tr_desc_rec desc
          | _ -> tr.tr_desc_rec desc
        end
    | _ -> tr.tr_desc_rec desc
  in
  let tr_term t =
    let desc =
      if List.mem ADoNotInline t.attr then
        tr.tr_desc_rec t.desc
      else
        tr.tr_desc t.desc
    in
    {t with desc}
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term <- tr_term;
  tr.tr_term


let beta_size1 =
  let tr = make_trans () in
  let tr_desc desc =
    let size_1 t =
      match t.desc with
      | Const _
      | Var _ -> true
      | _ -> false
    in
    match desc with
    | App(t1, []) -> tr.tr_desc t1.desc
    | App({desc=Fun(x,t)}, t2::ts) when size_1 t2 -> tr.tr_desc @@ App(subst x t2 t, ts)
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term


let conv = Fpat.Formula.of_term -| FpatInterface.of_term
let is_sat = FpatInterface.is_sat -| conv
let is_valid = FpatInterface.is_valid -| conv
let implies ts t = FpatInterface.implies (List.map conv ts) [conv t]


let reconstruct =
  let tr = make_trans () in
  let tr_term t =
    let t' =
      match t.desc with
      | Const _ -> {t with attr = const_attr}
      | Var x -> make_var x
      | Fun(x, t) -> make_fun x @@ tr.tr_term t
      | App(t1, ts) -> make_app (tr.tr_term t1) @@ List.map tr.tr_term ts
      | If(t1, t2, t3) -> make_if (tr.tr_term t1) (tr.tr_term t2) (tr.tr_term t3)
      | Local(Decl_let bindings, t) -> make_let (List.map (Pair.map_snd tr.tr_term) bindings) @@ tr.tr_term t
      | BinOp(op, t1, t2) -> make_binop op (tr.tr_term t1) (tr.tr_term t2)
      | Not t -> make_not @@ tr.tr_term t
      | Tuple ts -> make_tuple @@ List.map tr.tr_term ts
      | Proj(i, t) -> make_proj i @@ tr.tr_term t
      | Field(t1, s) -> make_field (tr.tr_term t1) s
      | TryWith(t1, {desc=Fun(x,{desc=Match({desc=Var y},pats)})}) when Id.(x = y) -> make_trywith t1 x pats
      | _ -> tr.tr_term_rec t
    in
    let attr' = List.unique (t.attr @ t'.attr) in
    {t' with attr=attr'}
  in
  tr.tr_term <- tr_term;
  tr.tr_term


let simplify_if_cond = make_trans2 ()
let simplify_if_cond_desc cond desc =
  match desc with
  | If(t1,t2,t3) ->
      let t1' = reconstruct t1 in
      let ts = decomp_and t1' in
      let t1'' =
        let simplify t =
          if has_no_effect t then
            if implies cond t then
              true_term
            else if implies cond @@ make_not t then
              false_term
            else
              t
          else
            t
        in
        make_ands @@ List.map simplify ts
      in
      let cond1 = List.filter has_no_effect ts @ cond in
      let cond2 = if has_no_effect t1' then make_not t1' :: cond else cond in
      let t2' = simplify_if_cond.tr2_term cond1 t2 in
      let t3' = simplify_if_cond.tr2_term (List.map make_not cond2) t3 in
      If(t1'', t2', t3')
  | _ -> simplify_if_cond.tr2_desc_rec cond desc
let () = simplify_if_cond.tr2_desc <- simplify_if_cond_desc
let simplify_if_cond = simplify_if_cond.tr2_term []




let decomp_var_match_tuple =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Match({desc=Var x}, [{pat_desc=PTuple pats}, t]) ->
        begin
          try
            let aux i pat =
              let y = match pat.pat_desc with PVar y -> y | _ -> raise Not_found in
              y, make_proj i @@ make_var x
            in
            (make_lets (List.mapi aux pats) t).desc
          with Not_found ->
            tr.tr_desc_rec desc
        end
    | _ ->
        tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term


let map_attr =
  let tr = make_trans2 () in
  let tr_term f t =
    let t' = tr.tr2_term_rec f t in
    {t' with attr = f t.attr}
  in
  tr.tr2_term <- tr_term;
  tr.tr2_term

let filter_attr f t = map_attr (List.filter f) t


let map_tattr =
  let tr = make_trans2 () in
  let tr_typ f ty =
    match ty with
    | TAttr(attr, ty') ->
        let attr' = f attr in
        let ty'' = tr.tr2_typ f ty' in
        if attr' = [] then
          ty''
        else
          TAttr(attr', ty'')
    | _ -> tr.tr2_typ_rec f ty
  in
  tr.tr2_typ <- tr_typ;
  tr.tr2_term

let filter_tattr f t = map_tattr (List.filter f) t


let tfuns_to_tfun =
  let tr = make_trans () in
  let tr_typ typ =
    match typ with
    | TFuns(xs, typ) ->
        let xs' = List.map tr.tr_var xs in
        let typ' = tr.tr_typ typ in
        List.fold_right _TFun xs' typ'
    | _ -> tr.tr_typ_rec typ
  in
  tr.tr_typ <- tr_typ;
  tr.tr_term


let tfun_to_tfuns =
  let tr = make_trans () in
  let tr_typ typ =
    match typ with
    | TFun(x, typ) ->
        let x' = tr.tr_var x in
        let typ' = tr.tr_typ typ in
        TFuns([x'], typ')
    | _ -> tr.tr_typ_rec typ
  in
  tr.tr_typ <- tr_typ;
  tr.tr_term


let split_assert_and =
  let tr = make_trans () in
  let tr_term t =
    match decomp_assert t with
    | Some (t1,loc) ->
        t1
        |> decomp_and
        |> List.map (make_assert ?loc)
        |> List.reduce_right make_seq
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let inline_specified =
  let tr = make_trans2 () in
  let tr_term (f,xs,t1) t =
    match t.desc with
    | Var g when Id.(f = g) ->
        if xs <> [] then invalid_arg "inline_specified?";
        t1
    | App({desc=Var g}, ts) when Id.(f = g) ->
        if List.length xs <> List.length ts then invalid_arg "inline_specified!";
        subst_map (List.combine xs ts) t1
    | _ -> tr.tr2_term_rec (f,xs,t1) t
  in
  tr.tr2_term <- tr_term;
  tr.tr2_term

let add_id_if =
  let tr = make_trans2 () in
  let tr_term (f,cnt) t =
    let t' = tr.tr2_term_rec (f,cnt) t in
    if f t then
      let id = AId (Counter.gen cnt) in
      add_attr id t'
    else
      t'
  in
  tr.tr2_term <- tr_term;
  fun f t ->
    let cnt = Counter.create () in
    let t' = tr.tr2_term (f,cnt) t in
    Counter.peep cnt, t'

let add_id t = add_id_if (Fun.const true) t

let remove_id t = filter_attr (function AId _ -> false | _ -> true) t
let remove_tid label t = filter_tattr (function TAId(s,_) when s = label -> false | _ -> true) t

let replace_fail =
  let f by desc =
    match desc with
    | App({desc=Event("fail", _)}, [{desc=Const Unit}]) -> Some by
    | _ -> None
  in
  fun ~by t -> trans_if_desc (f by) t

let replace_fail_with_bot =
  let f ids t =
    match t.desc with
    | App({desc=Event("fail", _)}, [{desc=Const Unit}]) ->
        if List.exists (function AId id -> List.mem id ids | _ -> false) t.attr then
          None
        else
          Some (make_bottom t.typ)
    | _ -> None
  in
  fun ?(except=[]) t -> trans_if (f except) t

(** eta_normal does not see the existence of side-effects *)
let eta_normal =
  let tr = make_trans () in
  let map_arg t =
    match t.desc with
    | Var _ -> t
    | App(t1,ts) ->
        let t1' = tr.tr_term t1 in
        let desc = App(t1', List.map tr.tr_term ts) in
        {t with desc}
    | _ -> assert false
  in
  let tr_term t =
    match t.desc with
    | App _ when is_fun_typ t.typ ->
        let t' = map_arg t in
        let xs =
          t.typ
          |> decomp_tfun
          |> fst
          |> List.map Id.new_var_id
        in
        make_funs xs (make_app t' @@ List.map make_var xs)
    | App _ -> map_arg t
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let direct_from_CPS =
  let tr = make_trans () in
  let tr_typ typ =
    if typ = typ_result then
      Ty.unit
    else
      tr.tr_typ_rec typ
  in
  let tr_desc desc =
    match desc with
    | Const CPS_result -> Const Unit
    | App({desc=Event(s, true)}, [t1; t2]) ->
        let t1' = tr.tr_term t1 in
        let t2' = tr.tr_term t2 in
        (make_seq (make_app (make_event s) [t1']) (make_app t2' [unit_term])).desc
    | App({desc=Const(Rand(typ, true))}, [t1; t2]) ->
        let t1' = tr.tr_term t1 in
        let t2' = tr.tr_term t2 in
        (make_app t2' [make_app (make_rand typ) [t1']]).desc
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_typ <- tr_typ;
  tr.tr_desc <- tr_desc;
  tr.tr_term

let reduce_fail_unit =
  let tr = make_trans () in
  let tr_term t =
    let t' = tr.tr_term_rec t in
    match t'.desc with
    | Local(Decl_let [_,t''], _) when t''.desc = (make_fail_unit None).desc -> t''
    | _ -> t'
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let remove_no_effect_trywith =
  let tr = make_trans () in
  let tr_term t =
    let t' = tr.tr_term_rec t in
    match t'.desc with
    | TryWith(t, _) when has_no_effect t -> t
    | _ -> t'
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let bool_eta_reduce =
  let tr = make_trans () in
  let tr_term t =
    let t' = tr.tr_term_rec t in
    match t'.desc with
    | If(t1, {desc=Const True}, {desc=Const False}) -> t1
    | _ -> t'
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let eta_tuple =
  let tr = make_trans () in
  let tr_desc desc =
    match tr.tr_desc_rec desc with
    | Proj(i, {desc=Tuple ts}) when List.for_alli (fun j t -> i = j || has_no_effect t) ts ->
        (List.nth ts i).desc
    | desc' -> desc'
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let eta_reduce =
  let tr = make_trans () in
  let tr_desc desc =
    let desc' = tr.tr_desc_rec desc in
    match desc' with
    | Fun(x, {desc=App(t1, ts)}) ->
        let ts',t2 = List.decomp_snoc ts in
        begin
          match t2.desc with
          | Var y when Id.(x = y) ->
              let t1' = make_app t1 ts' in
              if has_no_effect t1' && not @@ occur_in x t1' then
                t1'.desc
              else
                desc'
          | _ -> desc'
        end
    | _ -> desc'
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let name_read_int =
  let tr = make_trans () in
  let tr_term t =
    let desc' =
      match t.desc with
      | Local(Decl_let ([_,{desc=App({desc=Const(Rand _)}, [{desc=Const Unit}])}] as bindings), t) ->
          Local(Decl_let bindings, tr.tr_term t)
      | App({desc=Const(Rand(TBase TInt,false));attr}, [{desc=Const Unit}]) when List.mem AAbst_under attr ->
          let x = Id.new_var ~name:"r" Ty.int in
          (make_let [x,t] @@ make_var x).desc
      | _ -> tr.tr_desc_rec t.desc
    in
    {t with desc=desc'}
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let reduce_size_by_beta =
  let tr = make_trans () in
  let tr_term t =
    let desc =
      match t.desc with
      | Local(Decl_let ([_,{desc=App({desc=Const(Rand _)}, [{desc=Const Unit}])}] as bindings), t) ->
          Local(Decl_let bindings, tr.tr_term t)
      | App({desc=Const(Rand(TBase TInt,false));attr}, [{desc=Const Unit}]) when List.mem AAbst_under attr ->
          let x = Id.new_var ~name:"r" Ty.int in
          (make_let [x,t] @@ make_var x).desc
      | _ -> tr.tr_desc_rec t.desc
    in
    {t with desc}
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let elim_redundant_arg =
  let tr = make_trans2 () in
  let tr_desc vars desc =
    match desc with
    | Local(Decl_let [f,t1], t) when not @@ is_non_rec [f,t1] ->
        let xs,t1 = decomp_funs t1 in
        let fixed_args = find_fixed_args f xs t1 in
        if fixed_args = [] then
          Local(Decl_let [f, make_funs xs @@ tr.tr2_term_rec (xs@vars) t1], tr.tr2_term_rec vars t)
        else
          let ixs = List.filter_mapi (fun i x -> if Id.mem x fixed_args then Some (i,x) else None) xs in
          begin
            match col_app_args f t with
            | [] -> Local(Decl_let [f, make_funs xs @@ tr.tr2_term_rec (xs@vars) t1], tr.tr2_term_rec vars t)
            | args::argss ->
                let args' = List.map decomp_var args in
                let argss' = List.map (List.map decomp_var) argss in
                let redundant =
                  let check (i,_) =
                    match List.nth args' i with
                    | None -> false
                    | Some x ->
                        Id.mem x vars &&
                        List.for_all (fun args'' -> Option.exists (Id.eq x) @@ List.nth args'' i) argss'
                    | exception _ -> false
                  in
                  List.filter check ixs
                in
                let pos = List.map fst redundant in
                let map = List.map (fun (i,x) -> x, List.nth args i) redundant in
                let f' = Id.map_typ (List.fold_right Type.remove_arg_at pos) f in
                let xs' = List.fold_right List.remove_at pos xs in
                let remove_arg =
                  let tr = make_trans () in
                  let tr_desc desc =
                    match desc with
                    | App({desc=Var g}, ts) when Id.(f = g) ->
                        App(make_var f', List.fold_right List.remove_at pos ts)
                    | Fun(g,_) when Id.(f = g) -> desc
                    | Local(Decl_let bindings, _) when List.exists (fst |- Id.(=) f) bindings -> desc
                    | _ -> tr.tr_desc_rec desc
                  in
                  tr.tr_desc <- tr_desc;
                  tr.tr_term
                in
                let t1' =
                  t1
                  |> tr.tr2_term (xs@vars)
                  |> subst_map map
                  |> remove_arg
                in
                let t' =
                  t
                  |> tr.tr2_term vars
                  |> remove_arg
                in
                Local(Decl_let [f',make_funs xs' t1'], t')
          end
    | Local(Decl_let bindings, t) ->
        let bindings' = List.map (fun (f,t1) -> f, tr.tr2_term_rec vars t1) bindings in
        Local(Decl_let bindings', tr.tr2_term_rec vars t)
    | _ -> tr.tr2_desc_rec vars desc
  in
  tr.tr2_desc <- tr_desc;
  tr.tr2_term []

let split_let =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | Local(Decl_let bindings, t2) ->
        let bindings' = List.map (Pair.map_snd tr.tr_term) bindings in
        let fvs = List.flatten_map (snd |- get_fv) bindings' in
        let recs,non_recs = List.partition (fun (f,_) -> Id.mem f fvs) bindings' in
        make_let recs @@ make_lets non_recs @@ tr.tr_term t2
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_typ <- Fun.id;
  tr.tr_term

let remove_effect_attribute =
  let tr = make_trans () in
  let tr_attr = List.filter (function AEffect _ -> false | _ -> true) in
  let tr_typ ty =
    match ty with
    | TAttr(attrs, ty1) ->
        let attrs' = List.filter (function TAEffect _ -> false | _ -> true) attrs in
        let ty1' = tr.tr_typ ty1 in
        if attrs' = [] then
          ty1'
        else
          TAttr(attrs', ty1')
    | _ -> tr.tr_typ_rec ty
  in
  tr.tr_attr <- tr_attr;
  tr.tr_typ <- tr_typ;
  tr.tr_term

let assign_id_to_tvar =
  let fld = make_fold_tr () in
  let fld_typ cnt ty =
    match ty with
    | TVar({contents=None}, _) -> cnt+1, TVar({contents=None}, cnt)
    | ty -> fld.fld_typ_rec cnt ty
  in
  fld.fld_typ <- fld_typ;
  snd -| fld.fld_term 0



let inline_record_type =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(Decl_type decls, t) ->
        let tys = List.flatten_map (snd |- get_tdata) decls in
        let check (_,ty) =
          match ty with
          | TRecord _ -> if List.exists (List.mem -$- tys) @@ get_tdata ty then unsupported "recursive record types"
          | _ -> ()
        in
        List.iter check decls;
        let decls1,decls2 = List.partition (function (_,TRecord _) -> true | _ -> false) decls in
        let t' =
          t
          |> tr.tr_term
          |> List.fold_right (Fun.uncurry subst_tdata) decls1 (* TODO: support recursive declaration *)
        in
        if decls2 = [] then
          t'.desc
        else
          Local(Decl_type decls2, t')
    | Module _ -> unsupported "inline_record_type"
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let simplify_pattern =
  let tr = make_trans () in
  let is_all_any ps = List.for_all (fun p -> p.pat_desc = PAny) ps in
  let tr_pat p =
    match tr.tr_pat_rec p with
    | {pat_desc=POr(p1, p2)} when is_all_any [p1;p2] -> make_pany p.pat_typ
    | {pat_desc=PTuple ps} when is_all_any ps -> make_pany p.pat_typ
    | p' -> p'
  in
  tr.tr_pat <- tr_pat;
  tr.tr_term

let remove_pnondet =
  let tr = make_trans () in
  let tr_desc desc =
    match desc, tr.tr_desc_rec desc with
    | Match(_,pats), Match(t',pats') ->
        let pats'' =
          let aux (p,_) (p',t') =
            let p'' =
              if has_pnondet p then
                Pat.when_ p' Term.randb
              else
                p'
            in
            p'', t'
          in
          List.map2 aux pats pats'
        in
        Match(t', pats'')
    | _, desc' -> desc'
  in
  let tr_pat p =
    let p' = tr.tr_pat_rec p in
    match p'.pat_desc with
    | PNondet -> {p' with pat_desc=PAny}
    | POr({pat_desc=PAny},{pat_desc=PAny}) -> {p' with pat_desc=PAny}
    | _ -> p'
  in
  tr.tr_desc <- tr_desc;
  tr.tr_pat <- tr_pat;
  tr.tr_term

let split_type_decls =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(Decl_type decls as decl, t) ->
        let tys = List.map fst decls in
        let decls1,decls2 = List.partition (fun (x,ty) -> List.Set.((get_tdata ty && tys) <= [x])) decls in
        if decls1 = [] then
          Local(decl, tr.tr_term t)
        else
          make_local (Decl_type decls2) t
          |> tr.tr_term
          |> List.fold_right (fun decl -> make_local @@ Decl_type [decl]) decls1
          |> Syntax.desc
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let abst_recdata =
  let tr = make_trans2 () in
  let tr_term (s,check,env) t =
    let desc =
      match t.desc with
      | Local(Decl_type decls, t) ->
          let env' = decls::env in
          let t' = tr.tr2_term (s,check, env') t in
          let decls' = List.map (fun (s',ty) -> s', tr.tr2_typ (s,check,env') ty) decls in
          Local(Decl_type decls', t')
      | Match(_, pats) ->
          let t1',pats' =
            match tr.tr2_desc_rec (s,check,env) t.desc with
            | Match(t',pats') -> t', pats'
            | _ -> assert false
          in
          let pats'' =
            let aux (p1,_) (p2,t) =
              let make x =
                let ty = tr.tr2_typ (s,check,env) @@ Id.typ x in
                Id.set_typ x ty, make_rand_unit ty
              in
              let bindings =
                get_bv_pat p1
                |> List.Set.diff ~eq:Id.eq -$- (get_bv_pat p2)
                |> List.map make
              in
              p2, make_lets_s bindings t
            in
            List.map2 aux pats pats'
          in
          Match(t1', pats'')
      | Constr(_,ts) when check t.typ env ->
          Flag.Abstract.use s;
          let ts' = List.map (tr.tr2_term (s,check,env)) ts in
          Term.(seqs ts' randi).desc
      | _ -> tr.tr2_desc_rec (s,check,env) t.desc
    in
    let typ = tr.tr2_typ (s,check,env) t.typ in
    {desc; typ; attr=t.attr}
  in
  let tr_typ (s,check,env) ty =
    match ty with
    | TData _
    | TVariant _ when check ty env -> Ty.int
    | _ -> tr.tr2_typ_rec (s,check,env) ty
  in
  let tr_pat (s,check,env) p =
    match p.pat_desc with
    | PConstr _ when check p.pat_typ env ->
        Flag.Abstract.use s;
        {pat_desc=PNondet; pat_typ=Ty.int}
    | _ -> tr.tr2_pat_rec (s,check,env) p
  in
  tr.tr2_term <- tr_term;
  tr.tr2_typ <- tr_typ;
  tr.tr2_pat <- tr_pat;
  fun s check t ->
    t
    |> tr.tr2_term (s,check,[])
    |> remove_pnondet
    |> simplify_pattern
    |> split_type_decls

let replace_list_with_int =
  let tr = make_trans () in
  let tr_term t =
    let desc =
      match t.desc with
      | App({desc=Var len}, [t]) when is_length_var len ->
          let t' = tr.tr_term t in
          Term.(seq t' randi).desc
      | Match(_, pats) ->
          let t1',pats' =
            match tr.tr_desc_rec t.desc with
            | Match(t',pats') -> t', pats'
            | _ -> assert false
          in
          let pats'' =
            let aux (p1,_) (p2,t) =
              let make x =
                let ty = tr.tr_typ @@ Id.typ x in
                Id.set_typ x ty, make_rand_unit ty
              in
              let bindings =
                get_bv_pat p1
                |> List.unique ~eq:Id.eq
                |> List.Set.diff ~eq:Id.eq -$- (get_bv_pat p2)
                |> List.map make
              in
              p2, make_lets_s bindings t
            in
            List.map2 aux pats pats'
          in
          Match(t1', pats'')
      | Nil -> Term.randi.desc
      | Cons(t1,t2) ->
          Flag.Abstract.use "list-to-int";
          let t1' = tr.tr_term t1 in
          let t2' = tr.tr_term t2 in
          Term.(seqs [t1';t2'] randi).desc
      | _ -> tr.tr_desc_rec t.desc
    in
    let typ = tr.tr_typ t.typ in
    {desc; typ; attr=t.attr}
  in
  let tr_typ ty =
    match ty with
    | TApp("list", _) -> Ty.int
    | _ -> tr.tr_typ_rec ty
  in
  let tr_pat p =
    match p.pat_desc with
    | PNil ->
        Flag.Abstract.use "list-to-int";
        {pat_desc=PNondet; pat_typ=Ty.int}
    | PCons _ ->
        Flag.Abstract.use "list-to-int";
        {pat_desc=PNondet; pat_typ=Ty.int}
    | _ -> tr.tr_pat_rec p
  in
  tr.tr_term <- tr_term;
  tr.tr_typ <- tr_typ;
  tr.tr_pat <- tr_pat;
  fun t ->
    t
    |> tr.tr_term
    |> remove_pnondet
    |> simplify_pattern

let abst_ext_recdata =
  let typ_not_in_env ty env =
    match elim_tattr ty with
    | TData s -> not (List.exists (List.mem_assoc s) env)
    | TVariant _ -> false
    | _ -> true
  in
  abst_recdata "External rec. data with int" typ_not_in_env

let replace_data_with_int =
  abst_recdata "Data with int" (fun _ _ -> true)

let replace_data_with_int_but typ =
  abst_recdata "Data with int but exceptions" (fun ty _ -> Some ty <> typ)

let replace_exn_with_int t =
  match find_exn_typ t with
  | None -> t
  | Some ty_exn ->
      let check ty _ = ty = ty_exn in
      abst_recdata "Exceptions with int" check t

let replace_complex_data_with_int =
  let rec get_leaves ty =
    match elim_tattr ty with
    | TTuple xs -> List.flatten_map (Id.typ |- get_leaves) xs
    | TVariant(_, styss) -> List.flatten_map (snd |- List.flatten_map get_leaves) styss
    | _ -> [ty]
  in
  let is_complex ty env =
    try
      match elim_tattr ty with
      | TData s ->
          List.find (List.mem_assoc s) env
          |> List.flatten_map (snd |- get_leaves)
          |> List.filter ((<>) (TData s))
          |> List.exists (data_occurs s)
      | _ -> false
    with Not_found -> true
  in
  abst_recdata "Complex data with int" is_complex

(* ASSUME: there is no recursive types *)
let inline_type_decl =
  let tr = make_trans () in
  let tr_term t =
    let t' = tr.tr_term_rec t in
    match t'.desc with
    | Local(Decl_type decls, t1) -> List.fold_right (Fun.uncurry subst_tdata) decls t1
    | _ -> t'
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let mark_fv_as_external =
  let tr = make_trans2 () in
  let tr_desc bv desc =
    match desc with
    | Var x ->
        if Id.mem x bv || Id.is_primitive x then
          Var x
        else
          Var (Id.add_attr Id.External x)
    | Local(Decl_let defs, _) ->
        let bv' = List.map fst defs @ bv in
        tr.tr2_desc_rec bv' desc
    | Fun(x, _) ->
        tr.tr2_desc_rec (x::bv) desc
    | Match(t1, pats) ->
        let t1' = tr.tr2_term_rec bv t1 in
        let aux (p,t) =
          let bv' = get_bv_pat p @ bv in
          p, tr.tr2_term bv' t
        in
        Match(t1', List.map aux pats)
    | _ -> tr.tr2_desc_rec bv desc
  in
  tr.tr2_desc <- tr_desc;
  tr.tr2_typ <- Fun.snd;
  tr.tr2_term []

(** ASSUME: record types are inlined *)
let complete_precord =
  let tr = make_trans2 () in
  let tr_desc decls desc =
    match desc with
    | Local(Decl_type decls', _) ->
        tr.tr2_desc_rec (decls'@decls) desc
    | _ -> tr.tr2_desc_rec decls desc
  in
  let tr_pat _ p =
    match p.pat_desc with
    | PRecord pats ->
        let pats' =
          let aux (s,(_,ty)) =
            match List.assoc_opt s pats with
            | None -> s, {pat_desc=PAny; pat_typ=ty}
            | Some p -> s, p
          in
          List.map aux @@ decomp_trecord @@ p.pat_typ
        in
        {p with pat_desc=PRecord pats'}
    | _ -> p
  in
  tr.tr2_desc <- tr_desc;
  tr.tr2_pat <- tr_pat;
  tr.tr2_term []

let instansiate_poly_types =
  let tr = make_trans () in
  let tr_term t =
    match t.desc with
    | Deref t' ->
        Type.unify (Ty.ref t.typ) t'.typ;
        tr.tr_term_rec t
    | SetRef(t1,t2) ->
        Type.unify (Ty.ref t2.typ) t1.typ;
        tr.tr_term_rec t
    | App({desc=Var f;typ} as t1, ts) when List.exists (fun t -> is_poly_typ t.typ) (t1::ts) ->
        let rec unify ty ts =
          match elim_tattr ty, ts with
          | TFun(x,ty'), t2::ts' ->
              Type.unify (Id.typ x) t2.typ;
              unify ty' ts'
          | _, [] -> Type.unify ty t.typ
          | _ -> assert false
        in
        let _,ty = copy_tvar_typ typ in
        let f' = Id.set_typ f ty in
        unify ty ts;
        let ts' = List.map tr.tr_term ts in
        Term.(var f' @ ts')
    | Local(Decl_let [x, {desc=Var y}], _) ->
        unify (Id.typ x) (Id.typ y);
        tr.tr_term_rec t
    | Local(Decl_let defs, t1) -> (* the order of the transformations matters *)
        let defs' = List.map (Pair.map tr.tr_var tr.tr_term) defs in
        let t1' = tr.tr_term t1 in
        {t with desc=Local(Decl_let defs', t1')}
    | Match(t1, pats) ->
        let t1' = tr.tr_term t1 in
        let pats' =
          let aux (p,t) =
            let p' = tr.tr_pat p in
            let t' = tr.tr_term t in
            let bv = get_bv_pat p in
            let fv = get_fv ~eq:(fun _ _ -> false) t' in
            let aux x =
              let ty = Id.typ x in
              fv
              |> List.filter Id.(eq x)
              |> List.iter (unify ty -| Id.typ)
            in
            List.iter aux bv;
            p', t'
          in
          List.map aux pats
        in
        {t with desc = Match(t1', pats')}
    | _ -> tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  tr.tr_term

let instansiate_poly_types_with_env =
  let col = make_col2 () Fun.ignore2 in
  let col_var env x = if Id.mem_assoc x env then unify (Id.typ x) (Id.assoc x env) in
  col.col2_var <- col_var;
  fun env t -> col.col2_term env t; t

let inline_simple_types =
  let fld = make_fold_tr () in
  let fld_desc (env,map) desc =
    match desc with
    | Local(Decl_type decls, t) ->
        let rec is_simple ?(top=true) ty =
          match ty with
          | TData s -> top || not @@ List.mem_assoc s decls
          | TBase _ -> true
          | TFun(x,ty') -> is_simple ~top:false (Id.typ x) && is_simple ~top:false ty'
          | TTuple xs -> List.for_all (Id.typ |- is_simple ~top:false) xs
          | TApp(_, tys) -> List.for_all (is_simple ~top:false) tys
          | TAttr(_, ty) -> is_simple ~top:false ty
          | TVariant(_,labels) -> List.for_all (snd |- List.for_all (is_simple ~top:false)) labels
          | _ -> false
        in
        let decls1,decls2 = List.partition (snd |- is_simple) decls in
        let map' = decls1 @ map in
        if decls1 = [] then
          let env' = decls @ env in
          fld.fld_desc_rec (env',map') desc
        else
          let env' = decls1 @ env in
          let envmap,{desc} =
            make_local (Decl_type decls2) t
            |> subst_tdata_map decls1
            |> fld.fld_term (env',map')
          in
          envmap, desc
    | _ -> fld.fld_desc_rec (env,map) desc
  in
  fld.fld_desc <- fld_desc;
  fld.fld_term ([],[]) |- Pair.map_fst snd

let set_length_typ =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | App({desc=Var x}, [t]) when is_length_var x -> (make_length @@ tr.tr_term t).desc
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let split_mutual_rec =
  let tr = make_trans2 () in
  let tr_desc only_top desc =
    match desc with
    | Local(Decl_let (_::_::_ as bindings), t) ->
        let map =
          let rec aux bindings =
            match bindings with
            | [] -> []
            | (f,_)::bindings' ->
                let tys = List.map (fst |- Id.typ) bindings' in
                let f' =
                  f
                  |> Id.new_var_id
                  |> Id.map_typ (Ty.funs tys)
                in
                (f, f') :: aux bindings'
          in
          aux bindings
        in
        let bindings' =
          if only_top then
            bindings
          else
            List.map (Pair.map_snd @@ tr.tr2_term only_top) bindings
        in
        let bindings'' =
          let rec aux acc bindings =
            match bindings with
            | [] -> acc
            | (f,t1)::bindings' ->
                let args = List.map fst bindings' in
                let args' = List.map Id.new_var_id args in
                let arg_map = List.combine args args' in
                let f' = Id.assoc f map in
                let t_f = Term.(var f' @ vars args) in
                let t1' =
                  t1
                  |> subst_map acc
                  |> Term.(f |-> t_f)
                  |> subst_var_map arg_map
                in
                let acc' = (f,t_f) :: List.map (Pair.map_snd @@ subst f t_f) acc in
                (f', make_funs args' t1') :: aux acc' bindings'
          in
          aux [] bindings'
        in
        (make_lets bindings'' @@ tr.tr2_term only_top t).desc
    | _ -> tr.tr2_desc_rec only_top desc
  in
  tr.tr2_desc <- tr_desc;
  fun ?(only_top=false) t -> tr.tr2_term only_top t


let is_big_literal t =
  match t.desc with
  | Const (String s) -> !Flag.Abstract.literal <= String.length s
  | Cons _ ->
      begin
        match decomp_list t with
        | None -> false
        | Some ts -> List.length ts >= !Flag.Abstract.literal && List.for_all has_safe_attr ts
      end
  | _ -> false

let abst_literal =
  let tr = make_trans () in
  let tr_term t =
    if is_big_literal t then
      begin
        Flag.Abstract.use "literal";
        make_rand_unit t.typ
      end
    else
      tr.tr_term_rec t
  in
  tr.tr_term <- tr_term;
  fun t -> if !Flag.Abstract.literal < 0 then t else tr.tr_term @@ reconstruct t

let encode_bool_as_int =
  let tr = make_trans () in
  let tr_typ typ =
    if typ = Ty.bool then
      Ty.int
    else
      tr.tr_typ_rec typ
  in
  let int_of_bool t = Term.(if_ t (int 1) (int 0)) in
  let boo_of_int t =
    match t.desc with
    | If(t1, {desc=Const (Int 1)}, {desc=Const (Int 0)}) -> t1
    | _ -> Term.(t <> int 0)
  in
  let tr_desc desc =
    match desc with
    | Const True -> Const (Int 1)
    | Const False -> Const (Int 0)
    | Not t ->
        let t' = boo_of_int @@ tr.tr_term t in
        Term.(int_of_bool (not t')).desc
    | BinOp((And|Or as op), t1, t2) ->
        let op' = match op with And -> Term.(&&) | Or -> Term.(||) | _ -> assert false in
        let t1' = boo_of_int @@ tr.tr_term t1 in
        let t2' = boo_of_int @@ tr.tr_term t2 in
        (int_of_bool @@ op' t1' t2').desc
    | BinOp((Eq|Lt|Gt|Leq|Geq), _, _) ->
        let desc' = tr.tr_desc_rec desc in
        let t' = {desc=desc'; attr=[]; typ=Ty.bool} in
        (int_of_bool t').desc
    | If(t1, t2, t3) ->
        let t1' = tr.tr_term t1 in
        let t2' = tr.tr_term t2 in
        let t3' = tr.tr_term t3 in
        Term.(if_ (boo_of_int t1') t2' t3').desc
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_typ <- tr_typ;
  tr.tr_desc <- tr_desc;
  tr.tr_term

(* only for closed terms *)
let remove_unambiguous_id =
  let col = make_col2 [] (@) in
  let col_term env t =
    match t.desc with
    | Var x ->
        let x' = List.find (fun x' -> Id.name x' = Id.name x) env in
        if Id.id x' = Id.id x' then [x] else []
    | Fun(x, _) ->
        let env' = x::env in
        col.col2_term_rec env' t
    | Local(Decl_let bindings as decl, t) ->
        let env' = List.map fst bindings @ env in
        col.col2_decl env' decl @ col.col2_term env' t
    | Match _ -> unsupported "Trans.remove_unambiguous_id: Match"
    | _ -> col.col2_term_rec env t
  in
  col.col2_term <- col_term;
  fun t ->
    let t' = alpha_rename ~whole:true t in
    let xs = col.col2_term [] t' in
    let bv = get_bv t' in
    let xs' = List.Set.diff ~eq:Id.eq bv xs in
    map_id (fun x -> if Id.mem x xs' then Id.set_id x 0 else x) t'

let replace_typ_result_with_unit =
  let tr = make_trans () in
  let tr_typ typ =
    if typ = typ_result then
      Ty.unit
    else
      tr.tr_typ_rec typ
  in
  tr.tr_typ <- tr_typ;
  tr.tr_term

let rename_for_ocaml =
  let reserved =
    ["and";"as";"assert";"asr";"begin";"class";"constraint";"do";"done";"downto";"else";"end";
     "exception";"external";"false";"for";"fun";"function";"functor";"if";"in";"include";"inherit";
     "initializer";"land";"lazy";"let";"lor";"lsl";"lsr";"lxor";"match";"method";"mod";"module";
     "mutable";"new";"nonrec";"object";"of";"open";"or";"private";"rec";"sig";"struct";"then";"to";
     "true";"try";"type";"val";"virtual";"when";"while";"with"]
  in
  let tr = make_trans () in
  let tr_var x =
    let s = String.sign_to_letters @@ Id.name x in
    let s' =
      if Char.is_uppercase s.[0] then
        "_" ^ s
      else if List.mem (Id.to_string x) reserved then
        s ^ "_"
      else
        s
    in
    Id.set_name x s'
  in
  tr.tr_var <- tr_var;
  tr.tr_term

let remove_tattr =
  {!!make_trans with tr_typ = Type.elim_tattr_all}.tr_term

let reduce_rand =
  let tr = make_trans2 () in
  let rec is_rand_unit t =
    match t.desc with
    | Const Unit -> true
    | App({desc=Const (Rand(_,false))}, [{desc=Const Unit}]) -> true
    | Tuple ts -> List.for_all is_rand_unit ts
    | BinOp((Eq|Lt|Gt|Leq|Geq), t1, t2) -> is_rand_unit t1 || is_rand_unit t2
    | BinOp((Add|Sub|Mult), t1, t2) -> is_rand_unit t1 || is_rand_unit t2
    | BinOp(Div, t1, {desc=Const c}) when c <> Int 0 -> is_rand_unit t1
    | If(t1,t2,t3) -> has_safe_attr t1 && is_rand_unit t2 && is_rand_unit t3
    | _ -> false
  in
  let tr_term rand_funs t =
    match t.desc with
    | Local(Decl_let bindings, t) ->
        let bindings' = List.map (Pair.map_snd @@ tr.tr2_term rand_funs) bindings in
        let rand_funs' = List.filter_map Option.(some_if (snd |- decomp_funs |- snd |- is_rand_unit) |- map fst) bindings' in
        let t' = tr.tr2_term (rand_funs'@rand_funs) t in
        make_let bindings' t'
    | _ ->
        let t' = tr.tr2_term_rec rand_funs t in
        match t'.desc with
        | _ when is_rand_unit t' -> Term.rand t.typ
        | App({desc=Var f}, ts) when Id.mem f rand_funs && List.for_all has_safe_attr ts -> Term.rand t.typ
        | If(t1, t2, {desc=Bottom}) when is_rand_unit t1 -> t2
        | If(t1, t2, t3) when is_rand_unit t1 && same_term t2 t3 -> t2
        | Local(Decl_let _, _) -> assert false
        | _ -> t'
  in
  tr.tr2_term <- tr_term;
  tr.tr2_term [] |- elim_unused_let

let reduce_ignore =
  let tr = make_trans2 () in
  let tr_term ignore_funs t =
    match t.desc with
    | Local(Decl_let bindings, t) ->
        let bindings' = List.map (Pair.map_snd @@ tr.tr2_term ignore_funs) bindings in
        let ignore_funs' = List.filter_map Option.(some_if (snd |- decomp_funs |- snd |- Syntax.desc |- (=) (Const Unit)) |- map fst) bindings' in
        let t' = tr.tr2_term (ignore_funs'@ignore_funs) t in
        make_let bindings' t'
    | _ ->
        let t' = tr.tr2_term_rec ignore_funs t in
        match t'.desc with
        | App({desc=Var f}, ts) when Id.mem f ignore_funs ->
            List.fold_right make_seq ts unit_term
        | Local(Decl_let _, _) -> assert false
        | _ -> t'
  in
  tr.tr2_term <- tr_term;
  tr.tr2_term [] |- elim_unused_let

let reduce_branch =
  let tr = make_trans () in
  let rec decomp_branch t =
    match t.desc with
    | If(t1,t2,t3) when is_randbool_unit t1 -> decomp_branch t2 @ decomp_branch t3
    | _ -> [t]
  in
  let tr_term t =
    t
    |> tr.tr_term_rec
    |> decomp_branch
    |> List.classify ~eq:same_term
    |> List.map List.hd
    |> List.reduce_right make_br
  in
  tr.tr_term <- tr_term;
  tr.tr_term


(* Add unique id to each "fail" *)
let mark_fail =
  let fld = make_fold_tr () in
  let fld_term map t =
    match t.desc with
    | App({desc=Event("fail",false)}, [{desc=Const Unit}]) ->
        let loc = List.find_map_opt (function ALoc loc -> Some loc | _ -> None) t.attr in
        let c = List.length map in
        (c,loc)::map, add_attr (AId c) t
    | Event("fail",_) -> unsupported "mark_fail"
    | _ -> fld.fld_term_rec map t
  in
  fld.fld_term <- fld_term;
  fld.fld_term []

let split_assert t =
  if col_id t <> [] then unsupported "Trans.split_assert";
  let t' = split_assert_and t in
  let map,t'' = mark_fail t' in
  List.rev_map (fun (id,loc) -> replace_fail_with_bot ~except:[id] t'', loc) map

let insert_extra_param t =
  t
  |> lift_fst_snd
  |> FpatInterface.insert_extra_param (* THERE IS A BUG in exception handling *)
  |@> Debug.printf "insert_extra_param (%d added)::@. @[%a@.@." (List.length !Fpat.RefTypInfer.params) Print.term

(* input must be the whole program *)
let unify_pure_fun_app =
  let tr = make_trans () in
  let rec trans_apps ts =
    match ts with
    | [] -> []
    | t::ts' ->
        let ts1,ts2 = List.partition (same_term t) ts' in
        (List.length ts1 + 1, t)::trans_apps ts2
  in
  let collect_app =
    let col = make_col [] (@@@) in
    let filter bv apps =
      List.filter (get_fv |- List.Set.inter ~eq:Id.eq bv |- List.is_empty) apps
    in
    let col_term t =
      match t.desc with
      | App(_,ts) when has_pure_attr t -> t :: List.flatten_map col.col_term ts
      | Fun(x,t1) -> filter [x] @@ col.col_term t1
      | Match(t1,pats) ->
          let aux (p,t) = filter (get_bv_pat p) (col.col_pat p @@@ col.col_term t) in
          col.col_term t1 @@@ List.flatten_map aux pats
      | Local(Decl_let defs, t2) ->
          filter (List.map fst defs) @@ col.col_term t2
      | _ -> col.col_term_rec t
    in
    col.col_term <- col_term;
    col.col_term |- trans_apps
  in
  let unify t =
    let t' = tr.tr_term t in
    let apps = collect_app t' in
    let aux (n,app) t =
      if n >= 2 then
        let x = new_var_of_term app in
        make_let [x,app] @@ subst_rev app x t
      else
        t
    in
    List.fold_right aux apps t'
  in
  let tr_desc desc =
    match desc with
    | If(t1, t2, t3) -> If(tr.tr_term t1, unify t2, unify t3)
    | Match(t, pats) -> Match(tr.tr_term t, List.map (Pair.map_snd unify) pats)
    | Fun(x, t) -> Fun(x, unify t)
    | Local(Decl_let defs, t) -> Local(Decl_let (List.map (Pair.map_snd unify) defs), unify t)
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let lift_assume =
  let tr = make_trans () in
  let collect_assume =
    let union = List.Set.union ~eq:same_term in
    let col = make_col [] union in
    let col_term t =
      match t.desc with
      | If(t1, t2, {desc=Bottom}) ->
          union [t1] (union (col.col_term t1) (col.col_term t2))
      | If(t1, _, _)
        | Match(t1, _) -> col.col_term t1
      | Fun _ -> []
      | Local(Decl_let defs, t') ->
          t' :: List.map snd defs
          |> List.map col.col_term
          |> List.reduce union
          |> List.filter_out (get_fv |- List.exists (Id.mem_assoc -$- defs))
      | _ -> col.col_term_rec t
    in
    col.col_term <- col_term;
    col.col_term
  in
  let remove_assume =
    let tr = make_trans () in
    let tr_desc desc =
      match desc with
      | If(_, t2, {desc=Bottom}) -> tr.tr_desc t2.desc
      | _ -> tr.tr_desc_rec desc
    in
    tr.tr_desc <- tr_desc;
    tr.tr_term
  in
  let tr_desc desc =
    let lift ?fs t =
      let asms =
        t
        |> collect_assume
        |> List.map remove_assume
      in
      let asms' =
        match fs with
        | None -> asms
        | Some fs -> List.filter (get_fv |- List.exists (List.mem -$- fs)) asms
      in
      t
      |> tr.tr_term
      |> List.fold_right Term.assume asms'
    in
    match desc with
    | If(_, t2, {desc=Bottom}) -> tr.tr_desc t2.desc
    | If(t1, t2, t3) -> If(tr.tr_term t1, lift t2, lift t3)
    | Match(t, pats) -> Match(tr.tr_term t, List.map (Pair.map_snd lift) pats)
    | Fun(x, t) -> Fun(x, lift t)
    | Local(Decl_let defs, t) ->
        let fs = List.map fst defs in
        Local(Decl_let (List.map (Pair.map_snd tr.tr_term) defs), lift ~fs t)
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let elim_singleton_tuple =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Tuple [t] -> tr.tr_desc t.desc
    | Proj(_, t) when tuple_num t.typ = Some 1 -> tr.tr_desc t.desc
    | _ -> tr.tr_desc_rec desc
  in
  let tr_typ typ =
    match typ with
    | TTuple [x] -> tr.tr_typ @@ Id.typ x
    | _ -> tr.tr_typ_rec typ
  in
  let tr_pat p =
    match p.pat_desc with
    | PTuple [p] -> tr.tr_pat p
    | _ -> tr.tr_pat_rec p
  in
  tr.tr_desc <- tr_desc;
  tr.tr_typ <- tr_typ;
  tr.tr_pat <- tr_pat;
  tr.tr_term

let lift_pwhen =
  let collect_side_cond =
    let col = make_col Term.true_ Term.(&&) in
    let col_pat p =
      match p.pat_desc with
      | PWhen(p,c) -> Term.(col.col_pat p && c)
      | POr(p1,p2) ->
          assert ((col.col_pat p1).desc = Const True);
          assert ((col.col_pat p2).desc = Const True);
          Term.true_
      | _ -> col.col_pat_rec p
    in
    col.col_pat <- col_pat;
    col.col_pat
  in
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Match(t1, pats) ->
        let t1' = tr.tr_term t1 in
        let pats' =
          let aux (p,t) =
            let cond = collect_side_cond p in
            let cond' = tr.tr_term cond in
            let p' = tr.tr_pat p in
            Pat.(when_ p' cond'), tr.tr_term t
          in
          List.map aux pats
        in
        Match(t1', pats')
    | _ -> tr.tr_desc_rec desc
  in
  let tr_pat p =
    match p.pat_desc with
    | PWhen(p, _) -> tr.tr_pat p
    | _ -> tr.tr_pat_rec p
  in
  tr.tr_desc <- tr_desc;
  tr.tr_pat <- tr_pat;
  tr.tr_term


(* Output: the direct ancestors of patters for constructors must be PAny or PVar wrapped with PWhen *)
let decompose_match =
  let tr = make_trans () in
  let decomp_var p =
    match p.pat_desc with
    | PVar x -> Some(x, Term.true_)
    | PWhen({pat_desc=PVar x}, cond) -> Some(x, cond)
    | _ -> None
  in
  let rec tr_pat_list ps =
    let aux p =
      match p.pat_desc with
      | PVar _ -> p, Fun.id
      | _ ->
          let x = new_var_of_pattern p in
          let p',bind = tr_pat p in
          let cond = Term.(match_ (var x) [p', true_; Pat.(__ p'.pat_typ), false_]) in
          let bind' t = Term.(match_ (var x) [p', bind t]) in
          Pat.(when_ (var x) cond), bind'
    in
    let ps',binds = List.split_map aux ps in
    ps', List.fold_left (-|) Fun.id binds
  and tr_pat p =
    match p.pat_desc with
    | PAny -> p, Fun.id
    | PNondet -> assert false
    | PVar _ -> p, Fun.id
    | PAlias(p1,x) ->
        let p1',bind = tr_pat p1 in
        let pat_desc = PAlias(p1', x) in
        {p with pat_desc}, bind
    | PConst c ->
        let x = new_var_of_term c in
        let c' = tr.tr_term c in
        Pat.(when_ (var x) Term.(var x = c')), Fun.id
    | PConstr(c,ps) ->
        let ps',bind = tr_pat_list ps in
        let pat_desc = PConstr(c,ps') in
        {p with pat_desc}, bind
    | PNil -> p, Fun.id
    | PCons(p1,p2) ->
        let p1',p2',bind =
          match tr_pat_list [p1;p2] with
          | [p1';p2'], bind -> p1',p2',bind
          | _ -> assert false
        in
        let pat_desc = PCons(p1', p2') in
        {p with pat_desc}, bind
    | PTuple ps ->
        let ps',bind1 = tr_pat_list ps in
        let xs,conds = List.split_map (Option.get -| decomp_var) ps' in
        let x = new_var_of_pattern p in
        let bind2 = List.mapi (fun i y -> Term.(let_s [y, proj i (var x)])) xs in
        let bind = List.fold_right (-|) bind2 Fun.id in
        let bind' = bind -| bind1 in
        Pat.(when_ (var x) Term.(bind (ands conds))), bind'
    | PRecord sps ->
        let ss,ps = List.split sps in
        let ps',bind = tr_pat_list ps in
        let sps' = List.combine ss ps' in
        let pat_desc = PRecord sps' in
        {p with pat_desc}, bind
    | PNone -> p, Fun.id
    | PSome p1 ->
        let p1',bind = tr_pat p1 in
        let pat_desc = PSome p1' in
        {p with pat_desc}, bind
    | POr(p1,p2) ->
        let p1',bind1 = tr_pat p1 in
        let p2',bind2 = tr_pat p2 in
        begin
          match decomp_var p1', decomp_var p2' with
          | Some(x1, cond1), Some(x2, cond2) ->
              let bind = Term.(let_s [x2, var x1]) -| bind1 -| bind2 in
              Pat.(when_ (var x1) Term.(bind (cond1 || cond2))), bind
          | _ ->
              let pat_desc = POr(p1', p2') in
              {p with pat_desc}, bind1 -| bind2
        end
    | PWhen(p1,cond) ->
        let p1',bind = tr_pat p1 in
        let cond' = tr.tr_term cond in
        Pat.(when_ p1' (bind cond')), bind
  in
  let tr_desc desc =
    match desc with
    | Match(t1, pats) ->
        let x = new_var_of_term t1 in
        let pats' =
          let aux (p,t) =
            let p',bind = tr_pat p in
            let t' = tr.tr_term t in
            p', bind t'
          in
          List.map aux pats
        in
        let t1' = tr.tr_term t1 in
        let t' = Term.(match_ t1' pats') in
        if Id.mem x @@ get_fv t' then
          Term.(let_ [x,t1'] (match_ (var x) pats')).desc
        else
          t'.desc
    | _ -> tr.tr_desc_rec desc
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term

let variant_args_to_tuple =
  let tr = make_fold_tr () in
  let tr_desc _ desc =
    match desc with
    | Constr(s,ts) ->
        let _,ts' = List.split_map (tr.fld_term []) ts in
        [], Constr(s, [Term.tuple ts'])
    | Match(t1, pats) ->
        let _,t1' = tr.fld_term [] t1 in
        let pats' =
          let aux (p,t) =
            let bind,p' = tr.fld_pat [] p in
            let _,t' = tr.fld_term [] t in
            p', make_lets_s bind t'
          in
          List.map aux pats
        in
        [], Match(t1', pats')
    | _ -> tr.fld_desc_rec [] desc
  in
  let tr_pat bind p =
    match p.pat_desc with
    | PConstr(s,ps) ->
        let _,pat_typ = tr.fld_typ [] p.pat_typ in
        let binds,_ = List.split_map (tr.fld_pat []) ps in
        let x =
          match pat_typ with
          | TVariant(_,styss) -> Id.new_var @@ List.get @@ List.assoc s styss
          | _ -> assert false
        in
        let bind =
          let aux i p =
            match p.pat_desc with
            | PVar y -> y, Term.(proj i (var x))
            | _ -> invalid_arg "Trans.variant_args_to_tuple"
          in
          List.mapi aux ps
        in
        let pat_desc = PConstr(s, [Pat.(var x)]) in
        bind @ List.flatten binds, {pat_desc; pat_typ}
    | PWhen(p,cond) ->
        let bind,p' = tr.fld_pat [] p in
        let cond' = make_let_s bind cond in
        bind, Pat.(when_ p' cond')
    | _ -> tr.fld_pat_rec bind p
  in
  let tr_typ _ ty =
    match ty with
    | TVariant(b,styss) ->
        let tr = snd -| tr.fld_typ [] in
        let styss' = List.map (Pair.map_snd (List.singleton -| Ty.tuple -| List.map tr)) styss in
        [], TVariant(b, styss')
    | _ -> tr.fld_typ_rec [] ty
  in
  tr.fld_desc <- tr_desc;
  tr.fld_pat <- tr_pat;
  tr.fld_typ <- tr_typ;
  fun ?(do_decomp=true) t ->
    let t' =
      if do_decomp then
        decompose_match t
      else
        t
    in
    snd @@ tr.fld_term [] t'

let remove_obstacle_type_attribute_for_pred_share =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Local(decl, t) ->
        let decl' =
          match decl with
          | Decl_let defs ->
              let aux (f,t) =
                let f' = if is_fun_var f then f else tr.tr_var f in
                f', tr.tr_term t
              in
              Decl_let (List.map aux defs)
          | _ -> decl
        in
        Local(decl', tr.tr_term t)
    | _ -> tr.tr_desc_rec desc
  in
  let tr_typ ty =
    match ty with
    | TAttr(attr, ty') ->
        let attr' = List.filter (function TAId(s,_) when s = label_pred_share -> false | TAPredShare _ -> false | _ -> true) attr in
        _TAttr attr' @@ tr.tr_typ ty'
    | _ -> tr.tr_typ_rec ty
  in
  tr.tr_desc <- tr_desc;
  tr.tr_typ <- tr_typ;
  tr.tr_term

let alpha_rename_if =
  let tr = make_trans2 () in
  let tr_desc check desc =
    let new_id x =
      if check x then
        Id.new_var_id x
      else
        x
    in
    let desc' = tr.tr2_desc_rec check desc in
    match desc' with
    | Local(Decl_let bindings, t1) ->
        let map = List.map (fun (f,_) -> f, new_id f) bindings in
        let bindings' = List.map2 (fun (_,t) (_,f') -> f', subst_var_map_without_typ map t) bindings map in
        Local(Decl_let bindings', subst_var_map_without_typ map t1)
    | Fun(x, t1)->
        let x' = new_id x in
        Fun(x', subst_var_without_typ x x' t1)
    | Match(t1,pats) ->
        let aux (p,t2) =
          let map = List.map (Pair.add_right new_id) @@ List.unique ~eq:Id.eq @@ get_bv_pat p in
          rename_pat map p,
          subst_var_map_without_typ map t2
        in
        Match(t1, List.map aux pats)
    | _ -> desc'
  in
  tr.tr2_desc <- tr_desc;
  tr.tr2_term

(** The input must be in CPS *)
(* TODO: refactor *)
let add_occurence_param =
  let fld = make_fold_tr () in
  let gen x env =
    try
      List.assoc_map ~eq:Id.eq x succ env
      |> Pair.swap
    with Not_found -> (x,1)::env, 0
  in
  let fld_term env t0 =
    match t0.desc with
    | Fun _ ->
        let xs,t' = decomp_funs t0 in
        let env,xs' = fold_tr_list fld.fld_var env xs in
        let env,t'' = fld.fld_term env t' in
        let y = Id.new_var Ty.int in
        env, Term.funs (y::xs') t''
    | App({desc=Const (Rand(ty,_))}, [{desc=Const Unit}; {desc=Var k}]) ->
        let env,ty' = fld.fld_typ env ty in
        let env,x = gen k env in
        let env,k' = fld.fld_var env k in
        env, Term.(make_rand_cps ty' @ [unit; var k' @ [int x]])
    | App({desc=Const (Rand(ty,_))}, [{desc=Const Unit}; {desc=Fun(x,t)}]) ->
        let env, ty' = fld.fld_typ env ty in
        let env, t' = fld.fld_term env t in
        let env, x' = fld.fld_var env x in
        env, Term.(make_rand_cps ty' @ [unit; fun_ x' t'])
    | App({desc=Const (Rand _)}, _) -> assert false
    | App({desc=Event(s,_)}, [{desc=Const Unit}; {desc=Fun(x,t)}]) ->
        let env, t' = fld.fld_term env t in
        let env, x' = fld.fld_var env x in
        env, Term.(make_event_cps s @ [unit; fun_ x' t'])
    | App({desc=Event _}, _) -> assert false
    | App({desc=Var f}, ts) ->
        let env,f' = fld.fld_var env f in
        let env,x = gen f env in
        let env,ts' = fold_tr_list fld.fld_term env ts in
        env, Term.(var f' @ int x::ts')
    | App({desc=Fun _} as t1, ts) ->
        let env,t1' = fld.fld_term env t1 in
        let env,ts' = fold_tr_list fld.fld_term env ts in
        env, Term.(t1' @ int 0::ts')
    | _ -> fld.fld_term_rec env t0
  in
  let fld_typ env ty =
    match ty with
    | TFun _ ->
        let xs,ty' = decomp_tfun ty in
        let env,xs' = fold_tr_list fld.fld_var env xs in
        let x = Id.new_var Ty.int in
        let env,ty'' = fld.fld_typ env ty' in
        env, List.fold_right _TFun (x::xs') ty''
    | ty -> fld.fld_typ_rec env ty
  in
  fld.fld_term <- fld_term;
  fld.fld_typ <- fld_typ;
  snd -| fld.fld_term [] -| eta_normal

let map_typ =
  let tr = make_trans2 () in
  tr.tr2_term <- Fun.snd;
  tr.tr2_typ <- (@@);
  tr.tr2_term

let split_by_ref_type env t =
  if env = [] then invalid_arg "Trans.split_by_ref_type";
  let make acc_rev t =
    acc_rev
    |> List.fold_left (Fun.flip Term.local) t
    |> copy_tvar
    |> snd
  in
  let rec aux env acc_rev t =
    let have defs (f,_) = Id.mem_assoc f defs in
    match t.desc with
    | Local(Decl_let defs as decl, t1) when List.exists (have defs) env ->
        let f_env,env' = List.partition (have defs) env in
        begin match f_env with
        | [] -> assert false
        | [f,ty] ->
            let acc_rev' = decl::acc_rev in
            (Some (f,ty), make acc_rev' Term.eod) :: aux env' acc_rev t1
        | _ -> unsupported "split_by_ref_type"
        end
    | Local(decl, t1) -> aux env (decl::acc_rev) t1
    | _ ->
        let t' = make acc_rev t in
        let t'' =
          if !Flag.Method.verify_ref_interface then
            if env <> [] then
              (fatal @@ Format.asprintf "%a not found (unused functions are removed)" (print_list Print.id ",") (List.map fst env))
            else
              replace_fail_with_bot t'
          else
            t'
        in
        [None, t'']
  in
  aux env [] t

let rename_target_ext_funs map =
  let assoc x loc =
    let s_loc = Format.asprintf "%a" Print.location loc in
    List.find_map_opt (fun (y,s,y') -> if Id.(x=y) && String.exists s_loc s then Some y' else None) map
  in
  let f t =
    match t.desc with
    | Var x ->
        Id.get_loc x
        |> Option.bind -$- (assoc x)
        |> Option.map Term.var
    | _ -> None
  in
  trans_if f

let set_assert_ref_typ ?catch_all x ty t =
  let catch_all = Option.default_delayed (fun () -> make_catch_all t) catch_all in
  let tys,ty' = Ref_type.decomp_funs ty in
  let r = Id.new_var ~name:"r" @@ Ref_type.to_simple ty' in
  let t_check =
    match ty' with
    | Ref_type.Base(_,y,p) -> subst_var y r p
    | _ -> Term.true_
  in
  let xs =
    let make = Id.new_var ~name:"arg" -| Ref_type.to_simple ~with_pred:true in
    List.map (snd |- make) tys
  in
  let t_check' = List.fold_right2 (subst_var -| fst) tys xs t_check in
  let term =
    let main = Term.(let_ [r, catch_all (var x @ vars xs)] (assert_ t_check')) in
    let rec aux t =
      match t.desc with
      | Local(Decl_let bindings, t2) ->
          let t2' = if Id.mem_assoc x bindings then main else aux t2 in
          make_let bindings t2'
      | Local(Decl_type decls, t2) ->
          make_let_type decls @@ aux t2
      | _ -> assert false
    in
    aux t
  in
  let env =
    let aux x (y,ty) acc = (x,ty) :: List.map (Pair.map_snd @@ Ref_type.subst_var y x) acc in
    List.fold_right2 aux xs tys []
  in
  env, term

let copy_por =
  let tr = make_trans () in
  let tr_desc desc =
    match desc with
    | Match(t, pats) ->
        let pats' =
          let rec aux (p,t) =
            match p.pat_desc with
            | POr(p1,p2) -> aux (p1,t) @ aux (p2,t)
            | PWhen(p1,cond) -> List.map (Pair.map_fst (Pat.when_ -$- cond)) @@ aux (p1,t)
            | _ -> [p,t]
          in
          pats
          |> List.map (Pair.map_snd tr.tr_term)
          |> List.flatten_map aux
        in
        Match(tr.tr_term t, pats')
    | _ -> tr.tr_desc_rec desc
  in
  let tr_pat p =
    match p.pat_desc with
    | POr _ -> assert false
    | _ -> tr.tr_pat_rec p
  in
  tr.tr_desc <- tr_desc;
  tr.tr_pat <- tr_pat;
  tr.tr_term


let merge_deref =
  let fld = make_fold_tr () in
  let deref env xs t =
    let defs,xs_env =
      let make (r,ty) =
        let name = "v_" ^ Id.name r in
        let x = Id.new_var ~name ty in
        (x, Term.(!(var r))), (r, Term.var x)
      in
      xs
      |> List.filter_map (fun x -> match Id.typ x with TApp("ref", [ty]) -> Some(x,ty) | _ -> None)
      |> List.split_map make
    in
    let env = xs_env @ env in
    let env,t' = fld.fld_term env t in
    env, Term.(lets defs t')
  in
  let fld_term env t =
    match t.desc with
    | Var r ->
        let env =
          match t.typ with
          | TApp("ref", _) -> List.filter_out (fst |- Id.eq r) env
          | _ -> env
        in
        env, t
    | Deref {desc = Var r} ->
        env, Option.default t @@ Id.assoc_opt r env
    | SetRef({desc=Var r} as t1, t2) ->
        let env,t2' = fld.fld_term env t2 in
        let env = List.filter_out (fst |- Id.eq r) env in
        env, {t with desc=SetRef(t1, t2')}
    | Fun _ ->
        let xs,t1 = decomp_funs t in
        let env,t1' = deref env xs t1 in
        let env = List.filter_out (fst |- Id.mem -$- xs) env in
        env, Term.(funs xs t1')
    | Local(Decl_let _ as decl, t1) ->
        let env,decl' = fld.fld_decl env decl in
        let xs =
          match decl' with
          | Decl_let defs -> List.map fst defs
          | _ -> assert false
        in
        let env,t1' = deref env xs t1 in
        let env = List.filter_out (fst |- Id.mem -$- xs) env in
        env, {t with desc=Local(decl', t1')}
    | Match(t1,pats) ->
        let check =
          let pats_dummy = List.map (Pair.map_snd @@ Fun.const Term.unit) pats in
          get_fv Term.(match_ unit pats_dummy)
          |> List.exists (Id.typ |- function TApp("ref",_) -> true | _ -> false)
        in
        if check then unsupported "Trans.shrink_deref";
        let env,t1' = fld.fld_term env t1 in
        let envs,pats' =
          let aux (p,t) =
            let xs = get_bv_pat p in
            let env,t' = deref env xs t in
            let env = List.filter_out (fst |- Id.mem -$- xs) env in
            env, (p,t')
          in
          List.split_map aux pats
        in
        let env = List.fold_left (List.Set.diff ~eq:(Compare.eq_on ~eq:Id.eq fst)) env envs in
        env, {t with desc=Match(t1',pats')}
    | _ -> fld.fld_term_rec env t
  in
  fld.fld_term <- fld_term;
  fld_term [] |- snd

let update_attr = AInfo (InfoString "ref_update")

let infer_ref_update =
  let trc = make_tr_col2 false (||) in
  let trc_term () t =
    let update,desc = trc.tr_col2_desc_rec () t.desc in
    let update,desc =
      match desc with
      | Fun _ -> false, desc
      | App _ -> true, desc
      | SetRef _ -> true, desc
      | _ -> update, desc
    in
    let attr = if update then update_attr::t.attr else t.attr in
    update, {t with desc; attr}
  in
  trc.tr_col2_term <- trc_term;
  trc_term () |- snd


let merge_deref =
  let has_update t = List.mem update_attr t.attr in
  let rec decomp t =
    match t.desc with
    | Local(Decl_let [x,({desc=Deref {desc=Var r}} as t1)], t2) ->
        let refs',t2' = decomp t2 in
        (x,r,t1)::refs', t2'
    | _ -> [], t
  in
  let let_refs refs = Term.lets (List.map Triple.take13 refs) in
  let (++) refs1 refs2 =
    let aux refs (x,r,t) =
      match List.find_opt (fun (_,r',_) -> Id.(r = r')) refs with
      | None -> (x,r,t)::refs
      | Some(y,_,_) -> (x, r, Term.var y)::refs
    in
    List.fold_left aux refs1 refs2
    |> List.rev
  in
  let tr_list_focus focus tr_list xs =
    let ctxs,ts = List.split_map focus xs in
    let defs,ts',rs = tr_list ts in
    defs, List.map2 (@@) ctxs ts', rs
  in
  let rec tr_aux update t =
    let t' = tr t in
    if update then
      [], t', true
    else
      let refs,t'' = decomp t' in
      refs, t'', has_update t
  and tr_list_left ?(update=false) ts =
    let aux (refs_rev,ts_rev,update) t =
      let refs,t',update' = tr_aux update t in
      List.rev refs ++ refs_rev, t'::ts_rev, update'
    in
    let refs_rev,ts_rev,rs = List.fold_left aux ([],[],update) ts in
    List.rev refs_rev,
    List.rev ts_rev,
    rs
  and tr_list_right ?(update=false) ts =
    let aux t (refs_acc,ts_acc,update) =
      let refs,t',update' = tr_aux update t in
      refs ++ refs_acc, t'::ts_acc, update'
    in
    List.fold_right aux ts ([],[],update)
  and tr_list left_to_right = if left_to_right then tr_list_left else tr_list_right
  and tr t =
    let refs,desc =
      match t.desc with
      | End_of_definitions
      | Const _
      | Event _
      | Nil
      | Bottom
      | TNone
      | Var _ -> [], t.desc
      | Fun(x, t1) -> (* can improve *)
          [], Fun(x, tr t1)
      | App(t1,ts) ->
          let refs,(t1',ts') =
            let refs,ts,_ = tr_list Flag.EvalStrategy.app_left_to_right (t1::ts) in
            refs, List.decomp_cons ts
          in
          refs, App(t1', ts')
      | If(t1,t2,t3) ->
          let refs1,t1',update = tr_aux false t1 in
          let refs2,t2',_ = tr_aux update t2 in
          let refs3,t3',_ = tr_aux update t3 in
          let refs = refs1 ++ refs2 ++ refs3 in
          refs, If(t1', t2', t3')
      | Local(Decl_let defs, t2) ->
          let refs1,defs',rs = tr_list_focus Focus.snd (tr_list true) defs in
          let refs2,t2',_ = tr_aux rs t2 in
          let refs = refs1 ++ refs2 in
          refs, Local(Decl_let defs', t2')
      | Local(decl, t2) -> (* can improve *)
          [], Local(decl, tr t2)
      | BinOp(op,t1,t2) ->
          let refs,t1',t2' =
            match tr_list Flag.EvalStrategy.binop_left_to_right [t1;t2] with
            | refs, [t1'; t2'], _ -> refs, t1', t2'
            | _ -> assert false
          in
          refs, BinOp(op, t1', t2')
      | Not t1 ->
          let refs,t1',_ = tr_aux false t1 in
          refs, Not t1'
      | Record fields ->
          let refs,fields',_ = tr_list_focus Focus.snd (tr_list true) fields in
          refs, Record fields'
      | Field(t1,s) ->
          let refs,t1',_ = tr_aux false t1 in
          refs, Field(t1', s)
      | SetField(t1,s,t2) ->
          let refs,t1',t2' =
            match tr_list Flag.EvalStrategy.setfield_left_to_right [t1;t2] with
            | refs, [t1'; t2'], _ -> refs, t1', t2'
            | _ -> assert false
          in
          refs, SetField(t1', s, t2')
      | Cons(t1,t2) ->
          let refs,t1',t2' =
            match tr_list Flag.EvalStrategy.constr_left_to_right [t1;t2] with
            | refs, [t1'; t2'], _ -> refs, t1', t2'
            | _ -> assert false
          in
          refs, Cons(t1', t2')
      | Constr(s,ts) ->
          let refs,ts',_ = tr_list Flag.EvalStrategy.constr_left_to_right ts in
          refs, Constr(s, ts')
      | Match(t1,pats) ->
          let refs1,t1',update = tr_aux false t1 in
          let aux (p,t) (refs_acc,pats_acc) =
            let refs,t',_ = tr_aux update t in
            let bv = get_bv_pat p in
            let refs1,refs2 = List.partition (Triple.snd |- Id.mem -$- bv) refs in
            let t'' = let_refs refs1 t' in
            refs2++refs_acc, (p,t'')::pats_acc
          in
          let refs,pats' = List.fold_right aux pats ([],[]) in
          refs1++refs, Match(t1',pats')
      | Raise t1 ->
          let refs,t1',_ = tr_aux false t1 in
          refs, Raise t1'
      | TryWith(t1,t2) ->
          let refs,t1',t2' =
            match tr_list true [t1;t2] with
            | refs, [t1'; t2'], _ -> refs, t1', t2'
            | _ -> assert false
          in
          refs, TryWith(t1', t2')
      | Tuple ts ->
          let refs,ts',_ = tr_list Flag.EvalStrategy.tuple_left_to_right ts in
          refs, Tuple ts'
      | Proj(i,t1) ->
          let refs,t1',_ = tr_aux false t1 in
          refs, Proj(i, t1')
      | Ref t1 ->
          let refs,t1',_ = tr_aux false t1 in
          refs, Ref t1'
      | Deref {desc = Var r} ->
          let x =
            let name = "v_" ^ Id.name r in
            Id.new_var ~name t.typ
          in
          Term.[x, r, !(var r)], Var x
      | Deref t1 ->
          let refs,t1',_ = tr_aux false t1 in
          refs, Deref t1'
      | SetRef(t1,t2) ->
          let refs,t1',t2' =
            match tr_list Flag.EvalStrategy.setref_left_to_right [t1;t2] with
            | refs, [t1'; t2'], _ -> refs, t1', t2'
            | _ -> assert false
          in
          refs, SetRef(t1', t2')
      | TSome t1 ->
          let refs,t1',_ = tr_aux false t1 in
          refs, TSome t1'
      | Label _ -> unsupported "Trans.merge_deref"
      | Module _ -> unsupported "Trans.merge_deref"
      | MemSet(t1,t2) ->
          let refs,t1',t2' =
            match tr_list true [t1;t2] with
            | refs, [t1'; t2'], _ -> refs, t1', t2'
            | _ -> assert false
          in
          refs, MemSet(t1', t2')
      | AddSet(t1,t2) ->
          let refs,t1',t2' =
            match tr_list true [t1;t2] with
            | refs, [t1'; t2'], _ -> refs, t1', t2'
            | _ -> assert false
          in
          refs, AddSet(t1', t2')
      | Subset(t1,t2) ->
          let refs,t1',t2' =
            match tr_list true [t1;t2] with
            | refs, [t1'; t2'], _ -> refs, t1', t2'
            | _ -> assert false
          in
          refs, Subset(t1', t2')
    in
    let attr = List.remove t.attr update_attr in
    let_refs refs {t with desc; attr}
  in
  infer_ref_update |- tr |- inline_var

let abstract_exn =
  let tr = make_trans2 () in
  let tr_term (ty_exn,target,_ as env) t =
    let t' = tr.tr2_term_rec env t in
    match t'.desc with
    | Constr(s, ts) when t.typ = ty_exn ->
        let b = List.mem s target in
        Term.(seqs ts (bool b))
    | Match(t1, pats) ->
        let pats_old =
          match t.desc with
          | Match(_,pats) -> pats
          | _ -> assert false
        in
        let pats' =
          let aux (p1,_) (p2,t) =
            let make x =
              let ty = tr.tr2_typ env @@ Id.typ x in
              Id.set_typ x ty, make_rand_unit ty
            in
            let bindings =
              let (-) = List.Set.diff ~eq:Id.eq in
              (get_bv_pat p1 - get_bv_pat p2)
              |> List.map make
            in
            p2, make_lets_s bindings t
          in
          List.map2 aux pats_old pats
        in
        let desc = Match(t1, pats') in
        {t' with desc}
    | _ -> t'
  in
  let tr_typ (ty_exn,_,_ as env) ty =
    if ty = ty_exn then Ty.bool else tr.tr2_typ_rec env ty
  in
  let tr_pat (ty_exn,target,non_target as env) p =
    let p' = tr.tr2_pat_rec env p in
    if p.pat_typ = ty_exn then
      if target = [] then
        Pat.nondet p'.pat_typ
      else
        let rec match_any p =
          match p.pat_desc with
          | PVar _ -> true
          | PAny -> true
          | PAlias(p,_) -> match_any p
          | _ -> false
        in
        match p.pat_desc with
        | PConstr(s,ps) when List.for_all match_any ps ->
            let b = Id.new_var ~name:"b" Ty.bool in
            if List.mem s target then
              if [s] = target then
                Pat.(const Term.true_)
              else
                Pat.(when_ (var b) Term.(if_ (not (var b)) false_ randb))
            else
              if [s] = non_target then
                Pat.(const Term.false_)
              else
                Pat.(when_ (var b) Term.(if_ (var b) false_ randb))
        | _ -> Pat.nondet p'.pat_typ
    else
      p'
  in
  tr.tr2_term <- tr_term;
  tr.tr2_typ <- tr_typ;
  tr.tr2_pat <- tr_pat;
  fun t ->
  match find_exn_typ t with
  | None -> t
  | Some ty_exn ->
      let target = !Flag.Method.target_exn in
      let non_target =
        let constrs =
          match ty_exn with
          | TVariant(_,labels) -> List.map fst labels
          | _ -> assert false
        in
        List.Set.diff constrs target
      in
      tr.tr2_term (ty_exn,target,non_target) t


(* Make top definitions not to have side-effects *)
let top_def_to_funs t =
  let decls,body = decomp_decls t in
  let has_effect decl =
    match decl with
    | Decl_type _ -> None
    | Decl_let [x, t] when not (has_no_effect t) ->
        assert (not (Id.mem x (get_fv t)));
        let x' = Id.new_var ~name:(Id.name x) Ty.(fun_ unit (Id.typ x)) in
        Some (decl, (x, x', t))
    | Decl_let defs ->
        if List.exists (not -| has_no_effect -| snd) defs then unsupported "Trans.top_def_to_funs";
        None
    | Open _ -> None
  in
  let map = List.filter_map has_effect decls in
  if map = [] then
    t
  else
    let body' =
      let defs = List.map (fun (_,(x,x',_)) -> Id.new_var_id x, Term.(var x' @ [unit])) map in
      let main = Id.new_var ~name:"main" body.typ in
      Term.(let_ [main, lets defs body] (var main))
    in
    let aux decl t =
      match List.assoc_opt decl map with
      | None -> Term.(local decl t)
      | Some(x, x', tx) ->
          let tx' =
            let u = Id.new_var ~name:"u" Ty.unit in
            Term.(fun_ u tx)
          in
          let t' = subst x Term.(var x' @ [unit]) t in
          let decl' = Decl_let [x', tx'] in
          Term.(local decl' t')
    in
    List.fold_right aux decls body'

let set_to_primitive =
  let tr = make_trans2 () in
  let tr_desc set_modules desc =
    let is_set_op x = List.exists (fun (m,_) -> Id.is_in_module ~m x) set_modules in
    let name x =
      let m,_ = List.find (fun (m,_) -> Id.is_in_module ~m x) set_modules in
      x
      |> Id.remove_module_prefix ~m
      |> Id.name
    in
    match desc with
    | Var x when is_set_op x ->
        begin
          match name x with
          | "empty" -> Const Empty
          | _ -> Var x
        end
    | App({desc=Var x} as tx, [t1]) when is_set_op x ->
        let t1' = tr.tr2_term set_modules t1 in
        begin
          match name x with
          | "singleton" -> AddSet(t1', Term.empty t1.typ)
          | _ -> App(tx, [t1'])
        end
    | App({desc=Var x} as tx, [t1;t2]) when is_set_op x ->
        let t1' = tr.tr2_term set_modules t1 in
        let t2' = tr.tr2_term set_modules t2 in
        begin
          match name x with
          | "mem" -> MemSet(t1', t2')
          | "add" -> AddSet(t1', t2')
          | "subset" -> Subset(t1', t2')
          | _ -> App(tx, [t1'; t2'])
        end
    | Local(Decl_let [m, {desc=App({desc=Var make}, [elt])}] as decl, t) when Id.name make = "Stdlib.Set.Make" ->
        let set_modules' =
          let ty =
            match elt.typ with
            | TModule {sig_types} -> List.assoc "t" sig_types
            | _ -> assert false
          in
          (m,ty)::set_modules
        in
        let t' = tr.tr2_term set_modules' t in
        Local(decl, t')
    | _ -> tr.tr2_desc_rec set_modules desc
  in
  let tr_typ set_modules ty =
    match ty with
    | TData s when List.exists (fun (m,_) -> Id.is_in_module_string ~m s) set_modules ->
        let _,ty = List.find (fun (m,_) -> Id.is_in_module_string ~m s) set_modules in
        Ty.set ty
    | _ -> tr.tr2_typ_rec set_modules ty
  in
  tr.tr2_desc <- tr_desc;
  tr.tr2_typ <- tr_typ;
  tr.tr2_term []
