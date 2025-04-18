open Util
open Type
open Syntax
open Type_util
open Term_util

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

type get_rtyp = Syntax.id -> Ref_type.t
type make_get_rtyp = get_rtyp list -> get_rtyp
type make_get_rtyp_single = get_rtyp -> get_rtyp
type attr_info += Removed of (id * term) list
type attr_info += Replaced of term
type attr_info += Inserted of string
type attr_info += External

let () =
  update_pp_attr_info (fun fm info ->
      match info with
      | Removed ts ->
          Format.fprintf fm "Removed %a" Print.(list (id * term)) ts;
          true
      | Replaced t ->
          Format.fprintf fm "Replaced %a" Print.term t;
          true
      | Inserted s ->
          Format.fprintf fm "Inserted %s" s;
          true
      | External ->
          Format.fprintf fm "External";
          true
      | _ -> false)

let flatten_tvar, flatten_tvar_typ =
  let tr = Tr.make () in
  (tr.term, tr.typ)

(* The order of the applications of f and map_var itself may matter *)
let map_var : (id -> id) -> term -> term =
  let tr = Tr2.make () in
  tr.var <- (fun f x -> f @@ Id.map_typ (tr.typ f) x);
  tr.typ <-
    (fun f ty ->
      match ty with
      | TModSig sgn ->
          sgn
          |> List.map (function
               | Sig_value x -> Sig_value (f @@ Id.map_typ (tr.typ f) x)
               | item -> item)
          |> _TModSig
      | _ -> tr.typ_rec f ty);
  tr.term

let remove_var_let : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match tr.desc_rec desc with
      | Local (Decl_let [ (x, t) ], { desc = Var y })
        when Lid.(LId x = y) && not (Id.List.mem x (get_fv t)) ->
          t.desc
      | desc' -> desc');
  tr.term

let alpha_rename : ?whole:bool -> ?set_counter:bool -> term -> term =
  let prefix = '?' in
  (* must not occur as a prefix of the name of each variable *)
  let tr = Tr2.make () in
  tr.desc <-
    (fun (whole, cnt, names) desc ->
      let new_id x =
        if whole then (
          let x' =
            let rec fresh var =
              let s = Id.to_string var in
              if s = "" || StringSet.mem s !names then fresh @@ Id.set_id x cnt#gen else var
            in
            fresh @@ Id.set_id x 0
          in
          Ref.map (StringSet.add (Id.to_string x')) names;
          Id.add_name_before (String.of_char prefix) x')
        else Id.new_var_id x
      in
      let desc' = tr.desc_rec (whole, cnt, names) desc in
      match desc' with
      | Local (Decl_let bindings, t1) ->
          let map = List.map (fun (f, _) -> (f, new_id f)) bindings in
          let sbst =
            let map' = Fmap.(list (snd _LId)) map |> IdMap.of_list in
            subst_var_map_without_typ map'
          in
          let bindings' = List.map2 (fun (_, f') (_, t) -> (f', sbst t)) map bindings in
          Local (Decl_let bindings', sbst t1)
      | Fun (x, t1) ->
          let x' = new_id x in
          let t1' = subst_var_without_typ x (_LId x') t1 in
          Fun (x', t1')
      | Match (t1, pats) ->
          let pats' =
            pats
            |> List.map (fun (p, t2) ->
                   let map =
                     List.map (Pair.add_right new_id) @@ List.unique ~eq:Id.eq @@ get_bv_pat p
                   in
                   let map' = Fmap.(list (snd _LId)) map |> IdMap.of_list in
                   (rename_pat map p, subst_var_map_without_typ map' t2))
          in
          Match (t1, pats')
      | _ -> desc');
  tr.term <- set_afv_shallowly --| tr.term_rec;
  tr.typ <- Fun.snd;
  let remove_prefix = Id.map_name (fun s -> if s <> "" && s.[0] = prefix then String.tl s else s) in
  fun ?(whole = false) ?(set_counter = false) t ->
    let cnt = new counter in
    let names = ref StringSet.empty in
    t
    |@> Dbg.printf "INPUT: %a@." Print.term
    |> tr.term (whole, cnt, names)
    |@> Dbg.printf "OUTPUT: %a@." Print.term
    |> map_var remove_prefix
    |@> set_counter @> set_id_counter_to_max

(** Instansiate all the type variables with the first argument *)
let instansiate_tvar, instansiate_tvar_typ =
  let it = Iter2.make () in
  it.typ <-
    (fun ty typ ->
      match typ with
      | TVar (_, ({ contents = None } as r), _) ->
          Dbg.printf "INSTANSIATE_TVAR: %a := %a@." Print.typ typ Print.typ ty;
          r := Some ty
      | _ -> it.typ_rec ty typ);
  (it.term, it.typ)

let rename_tvar, rename_tvar_var, rename_tvar_typ =
  let tr = Tr2.make () in
  tr.typ <-
    (fun map typ ->
      match typ with
      | TVar (b, ({ contents = None } as x), n) when List.mem_assq x map ->
          TVar (b, List.assq x map, n)
      | _ -> tr.typ_rec map typ);
  (tr.term, tr.var, tr.typ)

let get_tvars : typ -> term t option ref list =
  let col = Col.make [] (List.fold_left (fun xs y -> if List.memq y xs then xs else y :: xs)) in
  col.typ <-
    (fun typ ->
      match typ with
      | TVar (_, ({ contents = None } as x), _) -> [ x ]
      | TAttr (_, typ) -> col.typ typ
      | _ -> col.typ_rec typ);
  col.typ

(* TODO: Fix for polymorphic variants? *)
let unify_pattern_var : term -> unit =
  let it = Iter2.make () in
  it.term <-
    (fun env t ->
      match t.desc with
      | Match (t, pats) ->
          it.term env t;
          pats
          |> List.iter (fun (pat, t') ->
                 let fv = get_fv ~force:true t' in
                 get_bv_pat pat
                 |> List.iter (fun x ->
                        let ty = Id.typ x in
                        if is_weak_poly_typ ty then
                          fv
                          |> List.filter (Id.same x)
                          |> List.filter (is_weak_poly_typ -| Id.typ)
                          |> List.iter (unify ~env ty -| Id.typ)))
      | Local (Decl_type decls, _) ->
          let env' = Tenv.add_typ_decl decls env in
          it.term_rec env' t
      | _ -> it.term_rec env t);
  it.term !!Tenv.init

let rec define_rand ?(name = "") ((env, defs) as ed) typ =
  match List.assoc_opt ~eq:Type.eq typ env with
  | Some f -> ((env, defs), [%term f ()])
  | None -> (
      match elim_tattr typ with
      | TBase _ -> ((env, defs), make_rand_unit typ)
      | TVar (_, ({ contents = None } as r), _) ->
          r := Some Ty.int;
          define_rand ed Ty.int
      | TVar (_, { contents = Some typ }, _) -> define_rand ed typ
      | TFun _ when is_raise_tfun typ ->
          let ty_exn, x, typ = Option.get @@ decomp_raise_tfun typ in
          let ed, t_typ = define_rand ed typ in
          let t = Term_util.make_use_var x t_typ in
          let ed, exn = define_rand ed ty_exn in
          (ed, [%term fun x -> raise `exn |+| `t])
      | TFun (x, typ) ->
          let ed', t = define_rand ed typ in
          let t = Term_util.make_use_var x t in
          (ed', [%term fun x -> `t])
      | TConstr (c, [ TVar (_, ({ contents = None } as r), _) ]) when c = C.list ->
          r := Some Ty.unit;
          define_rand ed typ
      | TConstr (c, [ typ' ]) when c = C.list ->
          let u = Id.new_var Ty.unit in
          let f = Id.new_var ~name:("make_" ^ to_id_string typ) (TFun (u, typ)) in
          let env' = (typ, f) :: env in
          let (env'', defs'), t_typ' = define_rand (env', defs) typ' in
          let t_typ = [%term ([] [@ty typ']) |+| `t_typ' :: f ()] in
          let t_f = [%term fun u -> `t_typ] in
          ((env'', (f, t_f) :: defs'), [%term f ()])
      | TTuple xs ->
          let aux x (ed, ts) =
            let ed', t = define_rand ed @@ Id.typ x in
            (ed', t :: ts)
          in
          let (env', defs'), ts = List.fold_right aux xs ((env, defs), []) in
          ((env', defs'), make_tuple ts)
      | TConstr (c, [ typ ]) when c = C.ref ->
          let ed', t = define_rand ed typ in
          (ed', Term.ref t)
      | TConstr (c, [ typ ]) when c = C.array ->
          let ed', t = define_rand ed @@ make_tlist typ in
          let f = PrimId.array_of_list typ in
          (ed', [%term f `t])
      | TConstr (c, [ typ' ]) when c = C.option ->
          let (env', defs'), t_typ' = define_rand (env, defs) typ' in
          let t = make_br (make TNone typ) (make (TSome t_typ') typ) in
          ((env', defs'), t)
      | TConstr _ -> ((env, defs), make_rand_unit typ)
      | TVariant (_, rows) ->
          let u = Id.new_var Ty.unit in
          let f = Id.new_var ~name:("make_" ^ to_id_string typ) (TFun (u, typ)) in
          let c = lid_of_string name in
          let env' = (TConstr (c, []), f) :: (typ, f) :: env in
          let n = List.length rows in
          let aux1 row (ed, itss, i) =
            let aux2 typ (ed, ts) =
              let ed', t = define_rand ed typ in
              (ed', t :: ts)
            in
            let ed', ts' = List.fold_right aux2 row.row_args (ed, []) in
            (ed', (i - 1, ts') :: itss, i - 1)
          in
          let (env'', defs'), itss, _ = List.fold_right aux1 rows ((env', defs), [], n) in
          let aux row (i, ts) =
            let p = if i < n - 1 then make_pconst (make_int i) else make_pany Ty.int in
            (p, make (Constr (false, Type.LId row.row_constr, ts)) typ)
          in
          let (env'', defs'), t = ((env'', defs'), Term.(match_ randi (List.map2 aux rows itss))) in
          ((env'', (f, [%term fun u -> `t]) :: defs'), [%term f ()])
      | TRecord fields ->
          let u = Id.new_var Ty.unit in
          let f = Id.new_var ~name:("make_" ^ to_id_string typ) (TFun (u, typ)) in
          let c = lid_of_string name in
          let env' = (TConstr (c, []), f) :: (typ, f) :: env in
          let (env'', defs'), t =
            let aux (field, (_flag, typ)) (ed, sfts) =
              let ed', t = define_rand ed typ in
              (ed', (field, t) :: sfts)
            in
            let ed', sfts = List.fold_right aux fields ((env', defs), []) in
            (ed', make (Record sfts) typ)
          in
          ((env'', (f, make_fun u t) :: defs'), [%term f ()])
      | _ -> unsupported "define_rand: %a" Print.typ typ)

let define_rand ed typ = define_rand ~name:"" ed typ

(* INPUT: type declarations must be on top *)
let instansiate_randval : term -> term =
  let fld = Fold_tr.make () in
  fld.term <-
    (fun ed t ->
      match t.desc with
      | App ({ desc = Const (Rand (TBase TInt, false)); attr }, [ t' ])
        when t'.desc = Const Unit && List.mem AAbst_under attr ->
          (* for disproving termination  *)
          (ed, t)
      | App ({ desc = Const (Rand (typ, false)) }, t' :: ts) when t'.desc = Const Unit ->
          let ed, t_rand = define_rand ed typ in
          let ed, ts' = Fold_tr.list ~f:fld.term ~acc:ed ts in
          (ed, Term.(t_rand @ ts'))
      | Const (Rand _) -> assert false
      | _ ->
          let ed, t = fld.term_rec ed t in
          (ed, set_afv_shallowly t));
  fun t ->
    let (_, defs), t' = fld.term ([], []) t in
    let defs' =
      let edges =
        defs
        |> List.map (fun (f, t) -> (f, List.filter_out (Id.eq f) @@ get_fv t))
        |> List.flatten_map (fun (f, fv) -> List.map (fun g -> (g, f)) fv)
      in
      let cmp = Compare.topological ~eq:Id.eq ~dom:(List.map fst defs) edges in
      List.sort (Compare.on ~cmp fst) defs
    in
    let tdecls, t'' = decomp_type_decls t' in
    make_lets defs' t'' |> List.fold_right make_let_type tdecls

let part_eval (t : term) : term =
  let is_apply t =
    let xs, t' = decomp_funs t in
    match (t'.desc, xs) with
    | Var x, [ y ] -> Lid.(x = LId y)
    | App (t, ts), _ ->
        let rec aux xs ts =
          match (xs, ts) with
          | [], [] -> true
          | x :: xs', { desc = Var y } :: ts' when Lid.(LId x = y) -> aux xs' ts'
          | _ -> false
        in
        aux xs (t :: ts)
    | _ -> false
  in
  let is_alias t =
    let xs, t' = decomp_funs t in
    match t'.desc with
    | Var (LId x) -> if xs = [] then Some x else None
    | Var _ -> unsupported "Trans.part_eval"
    | App ({ desc = Var (LId f) }, ts) ->
        let rec aux xs ts =
          match (xs, ts) with
          | [], [] -> true
          | x :: xs', { desc = Var y } :: ts' when Lid.(LId x = y) -> aux xs' ts'
          | _ -> false
        in
        if aux xs ts then Some f else None
    | App ({ desc = Var _ }, _) -> unsupported "Trans.part_eval"
    | _ -> None
  in
  let rec aux apply t =
    let desc =
      match t.desc with
      | End_of_definitions -> End_of_definitions
      | Const c -> Const c
      | Var (LId x) -> (
          try Local (Decl_let [ (x, Id.List.assoc x apply) ], make_var x)
          with Not_found -> Var (LId x))
      | Var _ -> unsupported "Trans.part_eval"
      | Fun (x, t) -> Fun (x, aux apply t)
      | App ({ desc = Var (LId f) }, ts) ->
          if List.mem_assoc f apply then
            match ts with
            | [] -> Local (Decl_let [ (f, Id.List.assoc f apply) ], make_var f)
            | [ t ] -> t.desc
            | t :: ts' -> App (t, ts')
          else
            let ts' = List.map (aux apply) ts in
            App (make_var f, ts')
      | App (({ desc = Fun (x, t1); typ = typ' } as t), ts) -> (
          if is_apply t then
            match ts with [] -> Fun (x, t1) | [ t ] -> t.desc | t :: ts' -> App (t, ts')
          else
            match ts with
            | [ { desc = Const (True | False) } ] -> (aux apply (subst x (List.hd ts) t1)).desc
            | _ ->
                let t' = aux apply t1 in
                let ts' = List.map (aux apply) ts in
                App (make (Fun (x, t')) typ', ts'))
      | App (t, ts) -> App (aux apply t, List.map (aux apply) ts)
      | If ({ desc = Const True }, t2, _) -> (aux apply t2).desc
      | If ({ desc = Const False }, _, t3) -> (aux apply t3).desc
      | If ({ desc = Not t1 }, t2, t3) -> If (aux apply t1, aux apply t3, aux apply t2)
      | If (t1, t2, t3) -> if t2 = t3 then t2.desc else If (aux apply t1, aux apply t2, aux apply t3)
      | Local (Decl_let [ (f, t1) ], t2) -> (
          if is_apply t1 then (aux ((f, t1) :: apply) (aux apply t2)).desc
          else
            match is_alias t1 with
            | Some x when not @@ List.mem f @@ get_fv t1 -> (subst_var f x @@ aux apply t2).desc
            | _ -> Local (Decl_let [ (f, aux apply t1) ], aux apply t2))
      | BinOp (op, t1, t2) -> BinOp (op, aux apply t1, aux apply t2)
      | Not t -> Not (aux apply t)
      | Event (s, b) -> Event (s, b)
      | Record fields -> Record (List.map (Pair.map_snd @@ aux apply) fields)
      | Field (t, s) -> Field (aux apply t, s)
      | Nil -> Nil
      | Cons (t1, t2) -> Cons (aux apply t1, aux apply t2)
      | Constr (b, c, ts) -> Constr (b, c, List.map (aux apply) ts)
      | Match (t, pats) ->
          let aux' (pat, t) = (pat, aux apply t) in
          Match (aux apply t, List.map aux' pats)
      | _ -> unsupported "Trans.part_eval (%a)" Print.desc_constr t.desc
    in
    make desc t.typ
  in
  aux [] t

let trans_let : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Local (Decl_let [ (f, t1) ], t2) when not @@ is_fun t1 ->
          App (make_fun f @@ tr.term t2, [ tr.term t1 ])
      | Local (Decl_let bindings, _t2) when List.exists (not -| is_fun -| snd) bindings ->
          assert false
      | _ -> tr.desc_rec desc);
  tr.term

let propagate_typ_arg : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Local (Decl_let bindings, t2) ->
          let aux (f, t) =
            let xs, t' = decomp_funs t in
            let xs' =
              let ys = List.take (List.length xs) (get_args @@ Id.typ f) in
              let aux x y ys =
                let ys' = List.map (Id.map_typ @@ subst_type_var y x) ys in
                Id.set_typ x (Id.typ y) :: ys'
              in
              List.fold_right2 aux xs ys []
            in
            let t'' = t' |> tr.term |> List.fold_right2 subst_var xs xs' in
            (f, make_funs xs' t'')
          in
          let bindings' = List.map aux bindings in
          let t2' = tr.term t2 in
          Local (Decl_let bindings', t2')
      | _ -> tr.desc_rec desc);
  tr.term

let replace_typ_var env x = Id.set_typ x @@ List.assoc_default ~eq:Id.eq (Id.typ x) x env

let replace_typ : (id * typ) list -> term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun env desc ->
      match desc with
      | Local (Decl_let bindings, t2) ->
          let aux (f, t) =
            let xs, t' = decomp_funs t in
            let f' = replace_typ_var env f in
            if not @@ can_unify (Id.typ f) (Id.typ f') then (
              let f'' = Id.set_typ f @@ elim_tattr_all @@ Id.typ f' in
              Format.eprintf "Prog: %a@.Spec: %a@." Print.id_typ f Print.id_typ f'';
              failwith
                "Type of %a in %s is wrong? (please specify monomorphic types if polymorphic types \
                 exist)"
                Print.id f !Flag.IO.spec);
            let xs' =
              let ys = List.take (List.length xs) (get_args @@ Id.typ f') in
              List.map2 (fun x y -> Id.set_typ x @@ Id.typ y) xs ys
            in
            let t'' = t' |> tr.term env |> subst_var f f' |> List.fold_right2 subst_var xs xs' in
            (f', make_funs xs' t'')
          in
          let bindings' = List.map aux bindings in
          let t2' = tr.term env t2 in
          let t2'' =
            List.fold_left2 (fun t (f, _) (f', _) -> subst_var f f' t) t2' bindings bindings'
          in
          Local (Decl_let bindings', t2'')
      | _ -> tr.desc_rec env desc);
  fun env t -> t |> tr.term env |> propagate_typ_arg

let rec eval t : term =
  let desc =
    match t.desc with
    | Const c -> Const c
    | Var x -> Var x
    | App ({ desc = Fun (x, t) }, t' :: ts) ->
        (eval (make (App (subst_map [ (x, t') ] t, ts)) t.typ)).desc
    | App (t, []) -> (eval t).desc
    | App (t, ts) -> App (eval t, List.map eval ts)
    | If ({ desc = Const True }, t2, _) -> (eval t2).desc
    | If ({ desc = Const False }, _, t3) -> (eval t3).desc
    | If (t1, t2, t3) -> If (eval t1, eval t2, eval t3)
    | Local _ -> assert false
    | BinOp (Add, { desc = Const (Int 0) }, t) -> (eval t).desc
    | BinOp (Mult, { desc = Const (Int 1) }, t) -> (eval t).desc
    | BinOp (Div, t, { desc = Const (Int 1) }) -> (eval t).desc
    | BinOp (Sub, t1, t2) -> (eval (make_add (eval t1) (eval (make_mul (make_int (-1)) t2)))).desc
    | BinOp (Mult, { desc = Const (Int n) }, { desc = BinOp (Mult, { desc = Const (Int m) }, t) })
      ->
        (eval (make_mul (make_int (n * m)) t)).desc
    | BinOp (op, t1, t2) -> BinOp (op, eval t1, eval t2)
    | Not t -> Not (eval t)
    | Fun (x, { desc = App (t, ts) }) ->
        let t' = eval t in
        let ts' = List.map eval ts in
        let ts'', t_last = List.decomp_snoc ts' in
        if t_last.desc = Var (LId x) && (not @@ List.mem x @@ get_fv @@ make_app t' ts'') then
          (eval @@ make_app t' ts'').desc
        else Fun (x, make_app t' ts')
    | Fun (x, t) -> Fun (x, eval t)
    | Event (s, b) -> Event (s, b)
    | _ -> assert false
  in
  make desc t.typ

let normalize_binop_exp op t1 t2 : desc =
  let neg xs = List.map (fun (x, n) -> (x, -n)) xs in
  let rec decomp t =
    match t.desc with
    | Const (Int n) -> [ (None, n) ]
    | Var (LId x) -> [ (Some [%term x], 1) ]
    | Var _ -> [%unsupported]
    | BinOp (Add, t1, t2) -> decomp t1 @@@ decomp t2
    | BinOp (Sub, t1, t2) -> decomp t1 @@@ neg (decomp t2)
    | BinOp (Mult, t1, t2) -> (
        let xns1 = decomp t1 in
        let xns2 = decomp t2 in
        let reduce xns = List.fold_left (fun acc (_, n) -> acc + n) 0 xns in
        let aux (x, _) = x <> None in
        match (List.exists aux xns1, List.exists aux xns2) with
        | true, true ->
            Format.eprintf "Nonlinear expression not supported: %a@." Print.term
              (make_binop op t1 t2);
            assert false
        | false, true ->
            let k = reduce xns1 in
            List.rev_map (fun (x, n) -> (x, n * k)) xns2
        | true, false ->
            let k = reduce xns2 in
            List.rev_map (fun (x, n) -> (x, n * k)) xns1
        | false, false -> [ (None, reduce xns1 + reduce xns2) ])
    | _ -> assert false
  in
  let xns1 = decomp t1 in
  let xns2 = decomp t2 in
  let xns =
    let compare (x1, _) (x2, _) =
      let aux = function
        | None -> "\255"
        | Some { desc = Var x } -> Lid.to_string x
        | _ -> assert false
      in
      compare (aux x2) (aux x1)
    in
    List.sort compare (xns1 @@@ neg xns2)
  in
  let rec aux = function
    | [] -> []
    | (x, n) :: xns ->
        let xns1, xns2 = List.partition (fun (y, _) -> x = y) xns in
        let n' = List.fold_left (fun acc (_, n) -> acc + n) 0 ((x, n) :: xns1) in
        (x, n') :: aux xns2
  in
  let xns' = aux xns in
  let xns'' = List.filter (fun (_, n) -> n <> 0) xns' in
  let x, n = List.hd xns'' in
  let xns = List.rev @@ List.tl xns'' in
  let op', t1', t2' =
    let aux = function
      | None, n -> make_int n
      | Some x, n -> if n = 1 then x else make_mul (make_int n) x
    in
    let t1, xns', op' =
      if n < 0 then
        let op' =
          match op with
          | Eq -> Eq
          | Lt -> Gt
          | Gt -> Lt
          | Leq -> Geq
          | Geq -> Leq
          | _ -> assert false
        in
        (aux (x, -n), xns, op')
      else (aux (x, n), neg xns, op)
    in
    let ts = List.map aux xns' in
    let t2 = match ts with [] -> make_int 0 | t :: ts' -> List.fold_left make_add t ts' in
    (op', t1, t2)
  in
  let rec simplify t =
    let desc =
      match t.desc with
      | BinOp (Add, t1, { desc = BinOp (Mult, { desc = Const (Int n) }, t2) }) when n < 0 ->
          let t1' = simplify t1 in
          BinOp (Sub, t1', make_mul (make_int (-n)) t2)
      | BinOp (Add, t1, { desc = Const (Int n) }) when n < 0 ->
          let t1' = simplify t1 in
          BinOp (Sub, t1', make_int (-n))
      | BinOp (Add, t1, t2) ->
          let t1' = simplify t1 in
          BinOp (Add, t1', t2)
      | t -> t
    in
    make desc t.typ
  in
  BinOp (op', t1', simplify t2')

let rec normalize_bool_exp t : term =
  let desc =
    match t.desc with
    | Const True -> Const True
    | Const False -> Const False
    | Var x -> Var x
    | BinOp (((Or | And) as op), t1, t2) ->
        let t1' = normalize_bool_exp t1 in
        let t2' = normalize_bool_exp t2 in
        BinOp (op, t1', t2')
    | ( BinOp (Eq, { desc = Const (True | False) }, _)
      | BinOp (Eq, _, { desc = Const (True | False) })
      | BinOp (Eq, { desc = Nil | Cons _ }, _)
      | BinOp (Eq, _, { desc = Nil | Cons _ }) ) as t ->
        t
    | BinOp (((Eq | Lt | Gt | Leq | Geq) as op), t1, t2) -> normalize_binop_exp op t1 t2
    | Not t -> Not (normalize_bool_exp t)
    | _ -> assert false
  in
  make desc t.typ

let rec merge_geq_leq t : term =
  let desc =
    match t.desc with
    | Const True -> Const True
    | Const False -> Const False
    | Var x -> Var x
    | BinOp (And, _, _) ->
        let ts = decomp_and t in
        let is_dual t1 t2 =
          match (t1.desc, t2.desc) with
          | BinOp (op1, t11, t12), BinOp (op2, t21, t22) when t11 = t21 && t12 = t22 ->
              (op1 = Leq && op2 = Geq) || (op1 = Geq && op2 = Leq)
          | _ -> false
        in
        let get_eq t =
          match t.desc with BinOp ((Leq | Geq), t1, t2) -> make_eq t1 t2 | _ -> assert false
        in
        let rec aux = function
          | [] -> []
          | t :: ts ->
              if List.exists (is_dual t) ts then
                let t' = get_eq t in
                let ts' = List.filter_out (is_dual t) ts in
                t' :: aux ts'
              else t :: aux ts
        in
        let ts' = aux ts in
        let t =
          match ts' with [] -> assert false | [ t ] -> t | t :: ts -> List.fold_left make_and t ts
        in
        t.desc
    | BinOp (Or, t1, t2) ->
        let t1' = merge_geq_leq t1 in
        let t2' = merge_geq_leq t2 in
        BinOp (Or, t1', t2')
    | BinOp (((Eq | Lt | Gt | Leq | Geq) as op), t1, t2) -> BinOp (op, t1, t2)
    | Not t -> Not (merge_geq_leq t)
    | _ ->
        Format.eprintf "%a@." Print.term t;
        assert false
  in
  make desc t.typ

let elim_fun : term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun fun_name t ->
      match t.desc with
      | Fun (y, t1) ->
          let f = Id.new_var ~name:fun_name t.typ in
          make_let [ (f, make_fun y @@ tr.term fun_name t1) ] @@ make_var f
      | Local (Decl_let bindings, t2) ->
          let aux (f, t) =
            let xs, t' = decomp_funs t in
            (f, make_funs xs @@ tr.term ("f_" ^ Id.name f) t')
          in
          let bindings' = List.map aux bindings in
          let t2' = tr.term fun_name t2 in
          make_let bindings' t2'
      | _ -> tr.term_rec fun_name t);
  tr.term "f"

let make_ext_env : term -> (id * typ) list =
  let col = Col2.make [] ( @@@ ) in
  let col_desc funs desc =
    match desc with
    | Var (LId x) when Fpat.RefTypInfer.is_parameter (Id.name x) -> []
    | Var (LId x) when Id.is_coefficient x -> []
    | Var (LId x) when Id.List.mem x funs -> [ (x, Id.typ x) ]
    | Var (LId _) -> []
    | Var _ -> unsupported "Tr.make_ext_env"
    | _ -> col.desc_rec funs desc
  in
  col.desc <- col_desc;
  fun t -> col.term (get_fv t) t

let init_base_rand =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | App ({ desc = Const (Rand (typ, false)) }, [ { desc = Const Unit } ]) when is_base_typ typ
        ->
          let name = match typ with TBase TInt -> "_ri" | TBase TBool -> "_rb" | _ -> "_r" in
          make_var @@ Id.new_var ~name typ
      | Const (Rand (TBase TInt, _)) -> assert false
      | _ -> tr.term_rec t);
  tr.term

(* TODO: Rewrite by using Tr & Refactor *)
let rec inlined_f inlined fs t : term =
  let desc =
    match t.desc with
    | Const c -> Const c
    | Var (LId y) -> (
        match List.find_opt (Triple.fst |- Id.eq y) fs with
        | Some (_, xs, t') ->
            let f, _ =
              List.L.fold_left xs ~init:(Fun.id, t.typ) ~f:(fun (f, ty) y ->
                  ((fun t -> f (make (Fun (y, t)) ty)), snd @@ Type.ValE._TFun ty))
            in
            let t' = inlined_f inlined fs t' in
            (f t').desc
        | None -> Var (LId y))
    | Var _ -> unsupported "Trans.inlined_f"
    | Fun (y, t1) -> Fun (y, inlined_f inlined fs t1)
    | App (t1, ts) -> (
        match t1.desc with
        | Var (LId f) when List.exists (Triple.fst |- Id.same f) fs ->
            let _, xs, t =
              try List.find (Triple.fst |- Id.same f) fs with Not_found -> assert false
            in
            let ts = List.map (inlined_f inlined fs) ts in
            let ys =
              List.map
                (fun t ->
                  match t.desc with
                  | Const (Unit | True | False | Int _) | Var _ -> `L t
                  | _ -> `R (Id.new_var ~name:"arg" t.typ))
                ts
            in
            let ys1, ys2 =
              if List.length ys <= List.length xs then (ys, [])
              else Fpat.Util.List.split_nth (List.length xs) ys
            in
            let xs1, xs2 = Fpat.Util.List.split_nth (List.length ys1) xs in
            let map =
              List.map2 (fun x y -> match y with `L t -> (x, t) | `R y -> (x, make_var y)) xs1 ys1
            in
            let t' = subst_map map t in
            let f, _ =
              List.fold_left
                (fun (f, ty) x ->
                  ( (fun t -> f (make (Fun (x, t)) ty)),
                    match ty with Type.TFun (_, ty') -> ty' | _ -> assert false ))
                ((fun t -> t), Type_util.app_typ t1.typ (List.map Syntax.typ ts))
                xs2
            in
            let bindings =
              Fpat.Util.List.filter_map2
                (fun y t -> match y with `L _ -> None | `R y -> Some (y, t))
                ys ts
            in
            (make_lets bindings
               (make_app (f t')
                  (List.map (fun y -> match y with `L t -> t | `R y -> make_var y) ys2)))
              .desc
        | _ ->
            let t1' = inlined_f inlined fs t1 in
            let ts' = List.map (inlined_f inlined fs) ts in
            App (t1', ts'))
    | If (t1, t2, t3) ->
        If (inlined_f inlined fs t1, inlined_f inlined fs t2, inlined_f inlined fs t3)
    | Local (Decl_let bindings, t2) ->
        let aux (f, t) = `L (f, inlined_f inlined fs t) in
        let bindings', fs' = Fpat.Util.List.partition_map aux bindings in
        let t2' = inlined_f inlined (fs @ fs') t2 in
        if bindings' = [] then t2'.desc else Local (Decl_let bindings', t2')
    | Local (Decl_type decls, t2) -> Local (Decl_type decls, inlined_f inlined fs t2)
    | BinOp (op, t1, t2) -> BinOp (op, inlined_f inlined fs t1, inlined_f inlined fs t2)
    | Not t1 -> Not (inlined_f inlined fs t1)
    | Event (s, b) -> Event (s, b)
    | Record fields -> Record (List.map (Pair.map_snd @@ inlined_f inlined fs) fields)
    | Field (t1, s) -> Field (inlined_f inlined fs t1, s)
    | SetField (t1, s, t2) -> SetField (inlined_f inlined fs t1, s, inlined_f inlined fs t2)
    | Nil -> Nil
    | Cons (t1, t2) -> Cons (inlined_f inlined fs t1, inlined_f inlined fs t2)
    | Constr (b, s, ts) -> Constr (b, s, List.map (inlined_f inlined fs) ts)
    | Match (t1, pats) ->
        let aux (pat, t1) = (pat, inlined_f inlined fs t1) in
        Match (inlined_f inlined fs t1, List.map aux pats)
    | Raise t -> Raise (inlined_f inlined fs t)
    | TryWith (t1, t2) -> TryWith (inlined_f inlined fs t1, inlined_f inlined fs t2)
    | Tuple ts -> Tuple (List.map (inlined_f inlined fs) ts)
    | Proj (i, t) -> Proj (i, inlined_f inlined fs t)
    | Bottom -> Bottom
    | MemSet (t1, t2) -> MemSet (inlined_f inlined fs t1, inlined_f inlined fs t2)
    | AddSet (t1, t2) -> AddSet (inlined_f inlined fs t1, inlined_f inlined fs t2)
    | Subset (t1, t2) -> Subset (inlined_f inlined fs t1, inlined_f inlined fs t2)
    | _ ->
        Format.eprintf "inlined_f: %a@." Print.desc_constr t.desc;
        assert false
  in
  make desc t.typ

let inlined_f inlined t = inlined_f inlined [] t |@> Type_check.check

let lift_fst_snd : term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun fs t ->
      match t.desc with
      | Fun (y, t1) -> make_fun y @@ tr.term fs t1 (* ommit the case where y is a pair *)
      | Local (Decl_let bindings, t2) ->
          let bindings' =
            List.map
              (fun (f, t) ->
                let xs, t = decomp_funs t in
                ( f,
                  make_funs xs
                    (let fs' =
                       List.flatten
                         (List.filter_map
                            (fun x ->
                              match x.Id.typ with
                              | TTuple [ _; _ ] ->
                                  Some
                                    [
                                      (Id.new_var ~name:x.Id.name (fst_typ x.Id.typ), true, x);
                                      (Id.new_var ~name:x.Id.name (snd_typ x.Id.typ), false, x);
                                    ]
                              | _ -> None)
                            xs)
                     in
                     if fs' = [] then tr.term fs t
                     else
                       make_lets
                         (List.map
                            (fun (x, bfst, xorig) ->
                              (* ommit the case where x is a pair *)
                              ( x,
                                if bfst then make_fst (make_var xorig)
                                else make_snd (make_var xorig) ))
                            fs')
                         (tr.term (fs @ fs') t)) ))
              (* ommit the case where f is a pair *)
              bindings
          in
          make_let bindings' @@ tr.term fs t2
      | Proj (0, { desc = Var x }) when tuple_num (Lid.typ x) = Some 2 -> (
          try
            let x, _, _ = List.find (fun (_, bfst, x') -> bfst && Lid.(LId x' = x)) fs in
            make_var x
          with Not_found -> make_fst @@ tr.term fs t)
      | Proj (1, { desc = Var x }) when tuple_num (Lid.typ x) = Some 2 -> (
          try
            let x, _, _ = List.find (fun (_, bfst, x') -> (not bfst) && Lid.(LId x' = x)) fs in
            make_var x
          with Not_found -> make_snd @@ tr.term fs t)
      | _ -> tr.term_rec fs t);
  tr.term []

let should_insert typs = List.for_all (function TFun _ -> true | _ -> false) typs

(** Insert extra parameters before function arguments.
    Input must be in CPS *)
let insert_param_funarg : term -> term =
  let tr = Tr.make () in
  tr.typ <-
    (fun typ ->
      match typ with
      | TFun _ as typ ->
          let xs, typ' = decomp_tfun typ in
          let xs' = List.map tr.var xs in
          let xs'' =
            if should_insert @@ List.map Id.typ xs then Id.new_var Ty.unit :: xs' else xs'
          in
          List.fold_right _TFun xs'' @@ tr.typ typ'
      | _ -> tr.typ_rec typ);
  tr.term <-
    (fun t ->
      let typ = tr.typ t.typ in
      let desc =
        match t.desc with
        | Fun _ ->
            let xs, t' = decomp_funs t in
            let xs' = List.map tr.var xs in
            let xs'' =
              if should_insert @@ List.map Id.typ xs then Id.new_var Ty.unit :: xs' else xs'
            in
            (make_funs xs'' @@ tr.term t').desc
        | App (t1, ts) ->
            let ts' = List.map tr.term ts in
            let ts'' = if should_insert @@ get_argtyps t1.typ then unit_term :: ts' else ts' in
            App (tr.term t1, ts'')
        | _ -> tr.desc_rec t.desc
      in
      make desc typ ~attr:t.attr);
  fun t -> t |> tr.term |@> Type_check.check ~ty:Ty.result

let remove_defs : id list -> term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun xs desc ->
      match desc with
      | Local (Decl_let bindings, t) ->
          let bindings' = List.filter_out (fun (f, _) -> Id.List.mem f xs) bindings in
          (make_let bindings' @@ tr.term xs t).desc
      | _ -> tr.desc_rec xs desc);
  tr.term

let rename_ext_funs : id list -> term -> id list * term =
  let fld = Fold_tr.make () in
  fld.desc <-
    (fun (funs, env, map) desc ->
      match desc with
      | Var (LId x) when Id.List.mem x funs ->
          let map', x' =
            try
              let eq x y = can_unify ~env (Id.typ x) (Id.typ y) && Id.name x = Id.name y in
              (map, List.find (eq x) map)
            with Not_found ->
              let x' = Id.new_var_id x in
              (x' :: map, x')
          in
          ((funs, env, map'), Var (LId x'))
      | Local (Decl_type decls, _) ->
          let env' = Tenv.add_typ_decl decls env in
          fld.desc_rec (funs, env', map) desc
      | _ -> fld.desc_rec (funs, env, map) desc);
  fld.term <-
    (fun env t ->
      let map, desc = fld.desc env t.desc in
      (map, make desc t.typ));
  fun funs t ->
    let (_, _, map), t' = fld.term (funs, !!Tenv.init, []) t in
    (map, t')

let remove_ext_attr : term -> term =
  let tr = Tr.make () in
  tr.var <- Id.map_attr (List.remove_all -$- Id.External);
  tr.term

let remove_type_decl : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Local (Decl_type _, t1) | Local (Type_ext (Ext_type _), t1) -> tr.desc t1.desc
      | _ -> tr.desc_rec desc);
  tr.term

let lift_type_decl t =
  let decls =
    col_type_decl t
    |> List.flatten
    |> List.L.fold_right ~init:[] ~f:(fun (s, (params, ty)) acc ->
           match Id.List.assoc_opt s acc with
           | None -> (s, (params, ty)) :: acc
           | Some ([], TVariant (VNonPoly, rows)) when C.is_exn (Type.LId s) ->
               let _, rows' = Type.ValE._TVariant ty in
               let updated = (Path.id_of C.exn, ([], TVariant (VNonPoly, rows @ rows'))) in
               updated :: List.remove_assoc s acc
           | Some (_, ty') ->
               if not @@ Type_util.same_shape ty ty' then
                 Format.eprintf "[%a] Assume %a is the same as %a@." Print.tconstr s Print.typ ty
                   Print.typ ty';
               acc)
  in
  t |> remove_type_decl |> make_let_type decls

(* order of "env" matters *)
let make_ext_funs ?(annot = false) ?(fvs = []) env t : term =
  let typ_exn = find_exn_typ t in
  let t' = remove_defs (List.map fst env) t in
  Dbg.printf "MEF t': %a@." Print.term t';
  Dbg.printf "MEF env: %a@." [%pr: (id * Ref_type.t) list] env;
  let funs =
    t'
    |> get_fv_unique ~eq:(Id.eq_ty ~eq:can_unify)
    |> List.filter Id.is_external
    |@> Dbg.printf "MEF fv: %a@." [%pr: id list]
    |> List.filter Id.is_external
    |> List.filter_out Id.is_coefficient
    |> List.filter_out (List.mem_assoc -$- env)
    |> List.filter_out (Id.List.mem -$- fvs)
    |@> Dbg.printf "MEF: %a@." Print.(list id_typ)
    |> List.filter_out (Id.List.mem_assoc -$- env)
  in
  if List.exists (is_poly_typ -| Id.typ) funs then
    unsupported "Tr.make_ext_funs (polymorphic functions)";
  let map, t'' = rename_ext_funs funs t' in
  Dbg.printf "MEF t'': %a@." Print.term' t'';
  let defs1 =
    let annot = annot ^> add_attr (AInfo External) in
    map |> List.map (Pair.add_right (annot -| make_rand_unit -| Id.typ))
  in
  let (genv, cenv), defs2 =
    List.L.fold_right_map env ~init:([], []) ~f:(fun (f, typ) (genv, cenv) ->
        let genv', cenv', t = Ref_type_gen.generate ~typ_exn ~genv ~cenv typ in
        let f' = Id.set_typ f @@ Ref_type.to_abst_typ ~with_pred:true typ in
        ((genv', cenv'), (f', t)))
  in
  let defs = List.map snd (genv @ cenv) @ defs2 in
  t'' |> make_lets defs1 |> make_lets defs |> remove_var_let |> remove_ext_attr |> lift_type_decl

let assoc_typ : id -> term -> typ =
  let col = Col2.make [] ( @@@ ) in
  col.desc <-
    (fun f desc ->
      match desc with
      | Local (Decl_let bindings, t1) ->
          let aux (g, t) =
            let typs1 = if Id.(f = g) then [ Id.typ g ] else [] in
            typs1 @@@ col.term f t
          in
          col.term f t1 @@@ List.rev_flatten_map aux bindings
      | _ -> col.desc_rec f desc);
  fun f t ->
    match col.term f t with
    | [] -> raise Not_found
    | [ typ ] -> typ
    | _ ->
        Dbg.printf "VAR:%a@.PROG:%a@." Id.print f Print.term t;
        assert false

let inline_no_effect : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Local (Decl_let [ (x, t) ], { desc = Var y })
        when Lid.(LId x = y) && (not @@ Id.List.mem x @@ get_fv t) ->
          (tr.term t).desc
      | Local (Decl_let [ (x, t) ], t2)
        when Id.List.mem x (get_fv t2) && has_no_effect t && (not @@ Id.List.mem x @@ get_fv t) ->
          let t' = tr.term t in
          let t2' = tr.term t2 in
          (subst x t' t2').desc
      | _ -> tr.desc_rec desc);
  tr.term

let beta_no_effect : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | App (t1, [ t2 ]) -> (
          let t1' = tr.term t1 in
          let t2' = tr.term t2 in
          match t1'.desc with
          | Fun (x, t1'') when has_no_effect t2' -> (subst x t2' t1'').desc
          | _ -> App (t1', [ t2' ]))
      | _ -> tr.desc_rec desc);
  tr.term

let rec diff_terms t1 t2 = diff_descs t1.desc t2.desc

and diff_descs desc1 desc2 =
  match (desc1, desc2) with
  | Const (Rand (typ1, b1)), Const (Rand (typ2, b2)) ->
      if Type_util.same_shape typ1 typ2 && b1 = b2 then [] else [ (desc1, desc2) ]
  | Const c1, Const c2 -> if c1 = c2 then [] else [ (desc1, desc2) ]
  | Var x1, Var x2 -> if Lid.(x1 = x2) then [] else [ (desc1, desc2) ]
  | Fun _, Fun _ -> [ (desc1, desc2) ]
  | App (t11, [ t12 ]), App (t21, [ t22 ]) -> diff_terms t11 t21 @ diff_terms t12 t22
  | App (t1, ts1), App (t2, ts2) ->
      let ts1', t12 = List.decomp_snoc ts1 in
      let ts2', t22 = List.decomp_snoc ts2 in
      let desc1 = App (make_app t1 ts1', [ t12 ]) in
      let desc2 = App (make_app t2 ts2', [ t22 ]) in
      diff_descs desc1 desc2
  | If (t11, t12, t13), If (t21, t22, t23) ->
      diff_terms t11 t21 @ diff_terms t12 t22 @ diff_terms t13 t23
  | Local (Decl_let _bindings1, t1), Local (Decl_let _bindings2, t2) -> [ (t1.desc, t2.desc) ]
  | BinOp (op1, t11, t12), BinOp (op2, t21, t22) ->
      if op1 = op2 then diff_terms t11 t21 @ diff_terms t12 t22 else [ (desc1, desc2) ]
  | Not t1, Not t2 -> diff_terms t1 t2
  | Event (s1, b1), Event (s2, b2) -> if s1 = s2 && b1 = b2 then [] else [ (desc1, desc2) ]
  | Record _, Record _ -> [ (desc1, desc2) ] (* Not implemented *)
  | Field _, Field _ -> [ (desc1, desc2) ] (* Not implemented *)
  | SetField _, SetField _ -> [ (desc1, desc2) ] (* Not implemented *)
  | Nil, Nil -> []
  | Cons (t11, t12), Cons (t21, t22) -> diff_terms t11 t21 @ diff_terms t12 t22
  | Constr _, Constr _ -> [ (desc1, desc2) ] (* Not implemented *)
  | Match _, Match _ -> [ (desc1, desc2) ] (* Not implemented *)
  | Raise _, Raise _ -> [ (desc1, desc2) ] (* Not implemented *)
  | TryWith _, TryWith _ -> [ (desc1, desc2) ] (* Not implemented *)
  | Tuple ts1, Tuple ts2 -> List.flatten @@ List.map2 diff_terms ts1 ts2
  | Proj (i, t1), Proj (j, t2) when i = j -> diff_terms t1 t2
  | Bottom, Bottom -> []
  | _ -> [ (desc1, desc2) ]

let subst_let_xy : term -> term =
  let tr = Tr.make () in
  let tr_desc desc =
    let desc' = tr.desc_rec desc in
    match desc with
    | Local (Decl_let bindings, _) when is_non_rec bindings ->
        let bindings', t' =
          match desc' with
          | Local (Decl_let bindings', t') when is_non_rec bindings' -> (bindings', t')
          | _ -> assert false
        in
        let sbst bind t =
          match bind with x, ({ desc = Var _ } as t') -> subst x t' t | _ -> raise Not_found
        in
        let bindings1, bindings2 =
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
  tr.desc <- tr_desc;
  tr.term

let flatten_let : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | Local (Decl_let [ (x, t1) ], t2) when is_non_rec [ (x, t1) ] -> (
          let t1' = tr.term t1 in
          let t2' = tr.term t2 in
          match t1'.desc with
          | Local _ ->
              let fbindings, t12 = decomp_lets t1' in
              let fbindings' = fbindings @ [ [ (x, t12) ] ] in
              List.fold_right make_let fbindings' t2'
          | _ -> make_let [ (x, t1') ] t2')
      | _ -> tr.term_rec t);
  tr.term

let normalize_let : ?is_atom:(term -> bool) -> term -> term =
  let tr = Tr2.make () in
  let tr_aux is_atom t =
    match t.desc with
    | Var _ -> (t, Fun.id)
    | _ when is_atom t -> (t, Fun.id)
    | _ ->
        let post t' =
          match t'.desc with
          | BinOp _ | App _ | Tuple _ | Proj _ ->
              let y = new_var_of_term t' in
              [%term
                let y = `t' in
                y]
          | _ -> t'
        in
        let x = new_var_of_term t in
        let t' = tr.term is_atom t in
        (Term.var x, Term.let_ [ (x, t') ] -| post)
  in
  tr.term <-
    (fun is_atom t ->
      let aux t = tr_aux is_atom t in
      match t.desc with
      | _ when is_atom t -> t
      | BinOp (op, t1, t2) ->
          let t1', post1 = aux t1 in
          let t2', post2 = aux t2 in
          post1 @@ post2 @@ make_binop op t1' t2'
      | Not t1 ->
          let t1', post = aux t1 in
          post @@ make_not t1'
      | App (t, ts) ->
          let ts', posts = List.split_map (tr_aux is_atom) ts in
          let t', post = aux t in
          let post' = List.fold_left ( |- ) post posts in
          post' @@ make_app t' ts'
      | Tuple ts ->
          let ts', posts = List.split_map (tr_aux is_atom) ts in
          List.fold_right ( @@ ) posts @@ make_tuple ts'
      | Proj (i, t) ->
          let t', post = aux t in
          post @@ make_proj i t'
      | If (t1, t2, t3) ->
          let t1', post = aux t1 in
          let t2' = tr.term is_atom t2 in
          let t3' = tr.term is_atom t3 in
          let add_attrs' =
            List.filter_out (function AFV _ -> true | _ -> false) t.attr |> add_attrs
          in
          post @@ add_attrs' @@ make_if t1' t2' t3'
      | Raise t1 ->
          let t1', post = aux t1 in
          post @@ make_raise t1' ~typ:t.typ
      | _ -> t |> tr.term_rec is_atom |> set_afv_shallowly);
  tr.typ <- Fun.snd;
  fun ?(is_atom = fun _ -> false) -> tr.term is_atom

let inline_var : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t' = tr.term_rec t in
      match t'.desc with
      | Local (Decl_let [ (x, ({ desc = Var _ } as t1)) ], t2) -> subst x t1 t2
      | _ -> set_afv_shallowly t');
  tr.term

let rec is_const t : bool =
  match t.desc with
  | Var _ -> true
  | Const _ -> true
  | Tuple ts -> List.for_all is_const ts
  | _ -> false

let inline_var_const : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | Local (Decl_let [ (x, t1) ], t2) when is_const t1 && (not @@ List.mem ADoNotInline t.attr)
        ->
          subst x t1 @@ tr.term t2
      | _ -> tr.term_rec t);
  tr.term

let map_attr : (attr list -> attr list) -> term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun f t ->
      let t' = tr.term_rec f t in
      (set_attr t' (f t.attr) [@alert "-unsafe"]));
  tr.term
[@@alert unsafe "This function must be used carefully"]

let filter_attr f t = map_attr (List.filter f) t
let filter_out_attr f t = map_attr (List.filter_out f) t

let map_tattr : (tattr list -> tattr list) -> term -> term =
  let tr = Tr2.make () in
  tr.typ <-
    (fun f ty ->
      match ty with
      | TAttr (attr, ty') ->
          let attr' = f attr in
          let ty'' = tr.typ f ty' in
          if attr' = [] then ty'' else TAttr (attr', ty'')
      | _ -> tr.typ_rec f ty);
  tr.term

let filter_tattr f t = map_tattr (List.filter f) t

let remove_label : ?label:string -> term -> term =
 fun ?(label = "") t ->
  map_attr
    (List.filter_out (function
      | AInfo (Label (l, _)) -> l = label
      | AInfo _ -> label = ""
      | _ -> false))
    t

let decomp_pair_eq : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | BinOp (Eq, t1, t2) -> (
          match t1.typ with
          | TTuple xs ->
              let aux t =
                match t with
                | { desc = Var y } -> (y, Fun.id)
                | _ ->
                    let y = new_var_of_term t in
                    (LId y, make_let [ (y, t) ])
              in
              let y1, post1 = aux @@ tr.term t1 in
              let y2, post2 = aux @@ tr.term t2 in
              let ts = List.mapi (fun i _ -> [%term (lid y1)##i = (lid y2)##i]) xs in
              post2 @@ post1 @@ make_ands ts
          | _ -> tr.term_rec t)
      | _ -> set_afv_shallowly @@ tr.term_rec t);
  tr.term

let remove_info_removed = filter_out_attr (function AInfo (Removed _) -> true | _ -> false)
let remove_info_replaced = filter_out_attr (function AInfo (Replaced _) -> true | _ -> false)
let remove_info_inserted = filter_out_attr (function AInfo (Inserted _) -> true | _ -> false)

let remove_info_trans =
  filter_out_attr (function AInfo (Removed _ | Replaced _ | Inserted _) -> true | _ -> false)

let elim_unused_let :
    ?leave_last:bool -> ?cbv:bool -> ?elim_may_div:bool -> ?annot:bool -> term -> term =
  let tr = Tr2.make () in
  let has_no_effect' t = has_no_effect t || has_safe_attr t in
  tr.term <-
    (fun (leave, cbv, div, annot) t ->
      let t' = tr.term_rec (leave, cbv, div, annot) t in
      match t'.desc with
      | Local (Decl_let [], t) -> t
      | Local (Decl_let bindings, t1)
        when (not (List.mem ADoNotInline t.attr)) && not (is_mod_var (fst (List.hd bindings)))
             (* WORKAROUND: Must see the occurences of modules in types *) ->
          let fv = IdSet.of_list @@ get_fv_unique t1 in
          let used =
            let rec aux reachable rest dep =
              match IdSet.choose_opt rest with
              | None -> reachable
              | Some x -> (
                  let rest' = IdSet.remove x rest in
                  match IdMap.find_opt x dep with
                  | None -> aux reachable rest' dep
                  | Some xs ->
                      let xs' = IdSet.diff xs reachable in
                      let reachable' = IdSet.union xs' reachable in
                      let rest = IdSet.union rest' xs' in
                      aux reachable' rest dep)
            in
            bindings
            |> List.fold_left
                 (fun dep (f, t) -> IdMap.add f (IdSet.of_list @@ get_fv_unique t) dep)
                 IdMap.empty
            |> aux fv fv
          in
          let necessary (f, t) =
            Id.List.mem f leave
            || IdSet.mem f used
            || (cbv && if div then not (has_safe_attr t) else not (has_no_effect' t))
          in
          let bindings', removed = List.partition necessary bindings in
          let flag = annot && removed <> [] in
          make_let bindings' t1 |> flag ^> add_attr (AInfo (Removed removed))
      | _ -> make t'.desc t'.typ ~attr:t.attr);
  tr.typ <- Fun.snd;
  fun ?(leave_last = false) ?(cbv = true) ?(elim_may_div = false) ?(annot = false) t ->
    let leave = if leave_last then List.map (fst |- Lid.id_of) @@ get_last_definition t else [] in
    tr.term (leave, cbv, elim_may_div, annot) t

let subst_with_rename_map : ?check:bool -> (id * term) list -> term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun map desc ->
      if map = [] then desc
      else
        match desc with
        | Var y -> (
            match List.find_opt (fun (x, _) -> Lid.(LId x = y)) map with
            | None -> desc
            | Some (_, (t1, _)) -> (alpha_rename t1).desc)
        | Fun (y, t) ->
            let map' = List.filter_out (fst |- Id.( = ) y) map in
            Fun (y, tr.term map' t)
        | Local (Decl_let bindings, t2) ->
            let map2 = List.filter_out (fst |- Id.List.mem_assoc -$- bindings) map in
            let map1 = if is_non_rec bindings then map else map2 in
            let bindings' = Fmap.(list (snd (tr.term map1))) bindings in
            let t2' = tr.term map2 t2 in
            Local (Decl_let bindings', t2')
        | Match (t1, pats) ->
            let pats' =
              List.L.map pats ~f:(fun (pat, t1) ->
                  let xs = get_bv_pat pat in
                  let map' = List.filter_out (fst |- Id.List.mem -$- xs) map in
                  (pat, tr.term map' t1))
            in
            Match (tr.term map t1, pats')
        | _ -> tr.desc_rec map desc);
  tr.term <- set_afv_shallowly --| tr.term_rec;
  tr.attr <-
    (fun map attrs ->
      let sbst y = match Id.List.assoc_opt y map with None -> [ y ] | Some (_, fv) -> fv in
      List.map (function AFV xs -> AFV (List.rev_flatten_map sbst xs) | a -> a) attrs);
  fun ?(check = false) map t2 ->
    if check && List.for_all (fst |- count_occurrence -$- t2 |- ( = ) 1) map then subst_map map t2
    else tr.term (List.map (Pair.map_snd (Pair.add_right get_fv)) map) t2

let subst_with_rename ?(check = false) x t1 t2 = subst_with_rename_map ~check [ (x, t1) ] t2

let elim_unused_branch : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | If ({ desc = Const True }, t1, _) -> tr.term t1
      | If ({ desc = Const False }, _, t2) -> tr.term t2
      | If ({ desc = BinOp (Eq, { desc = Var x }, { desc = Var y }) }, t1, _) when Lid.(x = y) ->
          tr.term t1
      | _ -> tr.term_rec t);
  tr.term

let inline_simple_exp : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | Local (Decl_let [ (x, t1) ], t2) when is_simple_aexp t1 || is_simple_bexp t1 ->
          tr.term @@ subst x t1 t2
      | _ -> tr.term_rec t);
  tr.term

let replace_base_with_int, replace_base_with_int_typ =
  let hash_of_const c = match c with Char c -> int_of_char c | _ -> Hashtbl.hash c in
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Const (Char _ as c) -> Const (Int (hash_of_const c))
      | Const ((String _ | Float _ | Int32 _ | Int64 _ | Nativeint _) as c) ->
          Flag.Abstract.over "Base with int";
          Const (Int (hash_of_const c))
      | Const (Rand (TConstr (c, []), b)) when is_base_prim c ->
          Flag.Abstract.over "Base with int";
          Const (Rand (Ty.int, b))
      | _ -> tr.desc_rec desc);
  tr.typ <-
    (fun typ ->
      match typ with TConstr (c, []) when is_base_prim c -> Ty.int | _ -> tr.typ_rec typ);
  tr.pat <-
    (fun p ->
      match p.pat_desc with
      | PConst
          { desc = Const ((Char _ | String _ | Float _ | Int32 _ | Int64 _ | Nativeint _) as c) } ->
          Pat.const (Term.int (hash_of_const c))
      | _ -> tr.pat_rec p);
  (tr.term, tr.typ)

let short_circuit_eval : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | _ when has_no_effect t -> tr.term_rec t
      | BinOp (And, t1, t2) -> make_if (tr.term t1) (tr.term t2) false_term
      | BinOp (Or, t1, t2) -> make_if (tr.term t1) true_term (tr.term t2)
      | _ -> tr.term_rec t);
  tr.term

(* input is assumed to be a CBN-program *)
let expand_let_val : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | Local (Decl_let bindings, t2) ->
          let bindings' = List.map (Pair.map_snd tr.term) bindings in
          let t2' = tr.term t2 in
          let bindings2, bindings1 = List.partition (is_fun -| snd) bindings' in
          let t2'' = subst_with_rename_map bindings1 t2' in
          let attr = if bindings2 = [] then t.attr @ t2''.attr else t.attr in
          make_let bindings2 t2'' |> merge_attrs attr |> set_afv_shallowly
      | _ -> set_afv_shallowly @@ tr.term_rec t);
  tr.typ <- Fun.id;
  tr.term

let rec eval_aexp t : int =
  match t.desc with
  | Const (Int n) -> n
  | Var _ -> invalid_arg "eval_aexp"
  | BinOp (op, t1, t2) ->
      let f =
        match op with
        | Add -> ( + )
        | Sub -> ( - )
        | Mult -> ( * )
        | Div -> ( / )
        | _ -> invalid_arg "eval_aexp"
      in
      f (eval_aexp t1) (eval_aexp t2)
  | _ -> invalid_arg "eval_aexp"

let rec eval_bexp t : bool =
  match t.desc with
  | Const True -> true
  | Const False -> false
  | Var _ -> invalid_arg "eval_bexp"
  | BinOp (((Eq | Lt | Gt | Leq | Geq) as op), t1, t2) ->
      let f =
        match op with
        | Eq -> ( = )
        | Lt -> ( < )
        | Gt -> ( > )
        | Leq -> ( <= )
        | Geq -> ( >= )
        | _ -> invalid_arg "eval_bexp"
      in
      f (eval_aexp t1) (eval_aexp t2)
  | BinOp (((And | Or) as op), t1, t2) ->
      let f = match op with And -> ( && ) | Or -> ( || ) | _ -> invalid_arg "eval_bexp" in
      f (eval_bexp t1) (eval_bexp t2)
  | Not t -> not @@ eval_bexp t
  | _ -> false

(* input is assumed to be a CBN-program *)
let beta_reduce : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | Local (Decl_let [ (x, ({ desc = Var _ } as t1)) ], t2) -> tr.term @@ subst x t1 t2
      | App (t1, []) -> tr.term t1
      | App (t1, t2 :: ts) -> (
          match tr.term t1 with
          | { desc = Fun (x, t1') } ->
              tr.term @@ make_app (subst_with_rename ~check:true x t2 t1') ts
          | t1' -> make_app t1' @@ List.map tr.term (t2 :: ts))
      | Proj (i, { desc = Tuple ts }) -> tr.term @@ List.nth ts i
      | If (t1, t2, t3) when is_simple_bexp t1 && get_fv t1 = [] ->
          tr.term @@ if eval_bexp t1 then t2 else t3
      | _ -> set_afv_shallowly @@ tr.term_rec t);
  tr.typ <- Fun.id;
  tr.term

let replace_bottom_def : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Local (Decl_let [ (f, t1) ], t2) when is_bottom_def f t1 ->
          let xs, t1 = decomp_funs t1 in
          Local (Decl_let [ (f, make_funs xs @@ make_bottom t1.typ) ], tr.term t2)
      | _ -> tr.desc_rec desc);
  tr.term

let flatten_tuple : term -> term =
  let tr = Tr.make () in
  tr.typ <-
    (fun typ ->
      match typ with
      | TTuple xs ->
          let xs' = List.map tr.var xs in
          let ys =
            List.flatten_map (fun x -> match Id.typ x with TTuple xs -> xs | _ -> [ x ]) xs'
          in
          TTuple ys
      | _ -> tr.typ_rec typ);
  let make_proj' i t =
    match t.typ with
    | TTuple _ -> make_proj i t
    | _ ->
        assert (i = 0);
        t
  in
  let make_tuple' ts = match ts with [] -> assert false | [ t ] -> t | _ -> make_tuple ts in
  tr.term <-
    (fun t ->
      match t.desc with
      | Match _ -> unsupported "not implemented: flatten_tuple (match)"
      | Proj (i, t1) ->
          let t1' = tr.term t1 in
          let x = Id.add_name_after (string_of_int i) (new_var_of_term t1') in
          let ns =
            List.map (fun typ -> match tr.typ typ with TTuple xs' -> List.length xs' | _ -> 1)
            @@ decomp_ttuple t1.typ
          in
          let rec new_pos i j acc ns =
            match ns with
            | [] -> assert false
            | n :: ns' ->
                if i = j then List.map (( + ) acc) @@ List.fromto 0 n
                else new_pos i (j + 1) (n + acc) ns'
          in
          make_let [ (x, t1') ]
          @@ make_tuple'
          @@ List.map (make_proj' -$- make_var x)
          @@ new_pos i 0 0 ns
      | Tuple ts ->
          let ts' = List.map tr.term ts in
          let xs' = List.map new_var_of_term ts' in
          let aux y =
            let ys = match Id.typ y with TTuple ys -> ys | _ -> [ y ] in
            let aux2 i _ =
              let t = make_proj' i @@ make_var y in
              let y' = new_var_of_term t in
              (y', (y', t))
            in
            let ys', defs = List.split @@ List.mapi aux2 ys in
            (make_lets defs, List.map make_var ys')
          in
          let conts, tss = List.split @@ List.map aux xs' in
          make_lets (List.combine xs' ts')
          @@ List.fold_left ( |> ) (make_tuple' @@ List.flatten tss) conts
      | _ -> tr.term_rec t);
  tr.term

let rec is_in_redex x t : bool option =
  match t.desc with
  | Var y -> Some Lid.(x = y)
  | Const _ -> Some false
  | Tuple ts ->
      let rs = List.map (is_in_redex x) ts in
      List.fold_right
        (fun r acc -> match acc with None -> None | Some b -> Option.map (( || ) b) r)
        rs (Some false)
  | Proj (_, t1) -> is_in_redex x t1
  | Local (Decl_let bindings, t1)
    when List.for_all (function _, { desc = Fun _ } -> true | _ -> false) bindings ->
      is_in_redex x t1
  | _ -> None

let inline_next_redex : term -> term =
  let tr = Tr.make () in
  let can_inline x t =
    count_occurrence x t = 1 && (Option.default false @@ is_in_redex (LId x) t)
  in
  tr.term <-
    (fun t ->
      match t.desc with
      | Local (Decl_let [ (x, t1) ], t2) when is_non_rec [ (x, t1) ] ->
          let t1' = tr.term t1 in
          let t2' = tr.term t2 in
          if can_inline x t2' then subst x t1' t2' else tr.term_rec t
      | _ -> tr.term_rec t);
  tr.term

let beta_var_tuple : term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun env t ->
      match t.desc with
      | Local (Decl_let [ (x, ({ desc = Tuple ts } as t1)) ], t2) when is_non_rec [ (x, t1) ] ->
          let xs = List.map (function { desc = Var x } -> Some x | _ -> None) ts in
          if List.for_all Option.is_some xs then
            let xs' = List.map Option.get xs in
            make_let [ (x, t1) ] @@ tr.term ((x, xs') :: env) t2
          else tr.term_rec env t
      | Proj (i, { desc = Var (LId x) }) when Id.List.mem_assoc x env ->
          make_var_lid @@ List.nth (Id.List.assoc x env) i
      | _ -> tr.term_rec env t);
  tr.term []

let beta_no_effect_tuple : term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun env t ->
      match t.desc with
      | Local (Decl_let [ (x, ({ desc = Tuple ts } as t1)) ], t2) when is_non_rec [ (x, t1) ] ->
          if List.for_all has_no_effect ts then make_let [ (x, t1) ] @@ tr.term ((x, ts) :: env) t2
          else tr.term_rec env t
      | Proj (i, { desc = Var (LId x) }) when Id.List.mem_assoc x env ->
          List.nth (Id.List.assoc x env) i
      | _ -> tr.term_rec env t);
  tr.term []

let reduce_bottom : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t' = tr.term_rec t in
      match t'.desc with
      | Local (Decl_let [ (_, { desc = Bottom }) ], _) -> make_bottom t.typ
      | _ -> t');
  tr.term

let merge_bound_var_typ : (id * typ) list -> term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun map desc ->
      match desc with
      | Local (Decl_let bindings, t) ->
          let aux (f, t) =
            let f' =
              try
                let typ = Id.List.assoc f map in
                Id.map_typ (merge_typ typ) f
              with Not_found -> f
            in
            let t' = tr.term map t in
            (f', t')
          in
          let bindings' = List.map aux bindings in
          let t' = tr.term map t in
          Local (Decl_let bindings', t')
      | _ -> tr.desc_rec map desc);
  fun map t -> t |> tr.term map |> propagate_typ_arg

let unify_app_args : term -> unit =
  let it = Iter.make () in
  it.desc <-
    (fun desc ->
      match desc with
      | App ({ desc = Var _; typ }, ts) ->
          let rec uni typ ts =
            match (typ, ts) with
            | TFun ({ Id.typ = ty1 }, ty2), t1 :: ts' ->
                unify ty1 t1.typ;
                uni ty2 ts'
            | _ -> ()
          in
          uni typ ts
      | _ -> it.desc_rec desc);
  it.term

let rename_poly_values : ?env:env -> id list -> term -> (id * typ Id.t) list list * term =
  let fld = Fold_tr.make () in
  let can_unify env f (f', g) = Id.(f = f') && can_unify ~env (Id.typ f) (Id.typ g) in
  let find_and_copy fs map env x x_ty =
    match List.find_opt (List.exists (can_unify env x)) map with
    | None ->
        let _, x_map =
          let copy f (tvar_env, acc) =
            let tvar_env, ty = copy_tvar_typ ~env:tvar_env @@ Id.typ f in
            if Id.(x = f) then unify ~env ~ignore_non_poly_fail:true x_ty ty;
            let f' = Id.set_typ f ty in
            let g = Id.new_var_id f' in
            (tvar_env, (f', g) :: acc)
          in
          List.fold_right copy fs ([], [])
        in
        let x' = Id.List.assoc x x_map in
        (x_map :: map, x')
    | Some x_map ->
        let x' = Id.List.assoc x x_map in
        unify ~env x_ty (Id.typ x');
        (map, x')
  in
  let fld_list focus fs map env xs =
    List.L.fold_right_map xs ~init:map ~f:(fun x map ->
        let ctx, t = focus x in
        let (_, map', _), t' = fld.term (fs, map, env) t in
        (map', ctx t'))
  in
  let filter_bv ~fs bv = Id.List.Set.(fs - bv) in
  fld.term <-
    (fun ((fs, map, env) as acc) t ->
      match t.desc with
      | Var (LId x) when Id.List.mem x fs ->
          let map', x' = find_and_copy fs map env x t.typ in
          ((fs, map', env), Term.var x')
      | Fun (x, t) ->
          let fs' = filter_bv ~fs [ x ] in
          let (_, map', _), t' = fld.term (fs', map, env) t in
          ((fs, map', env), Term.fun_ x t')
      | Local (Decl_let bindings, t) ->
          let fs' = filter_bv ~fs (List.map fst bindings) in
          let (_, map, _), t' = fld.term (fs', map, env) t in
          let map, bindings' = fld_list Focus.snd fs' map env bindings in
          ((fs, map, env), Term.local (Decl_let bindings') t')
      | App ({ desc = Var (LId x); typ }, ts) when Id.List.mem x fs ->
          let map, ts' = fld_list Focus.id fs map env ts in
          let map', x' = find_and_copy fs map env x typ in
          ((fs, map', env), Term.(var x' @ ts'))
      | Local (Decl_type decls, t) ->
          let env = Tenv.add_typ_decl decls env in
          let (_, map', _), t' = fld.term (fs, map, env) t in
          ((fs, map', env), Term.local (Decl_type decls) t')
      | Match (t1, pats) ->
          let acc, t1' = fld.term acc t1 in
          let acc, pats' =
            Fold_tr.list_left ~acc pats ~f:(fun (fs, map, env) (pat, t1) ->
                let (_, map, _), pat' = fld.pat (fs, map, env) pat in
                let fs' = filter_bv ~fs (get_bv_pat pat) in
                let (_, map, _), t1' = fld.term (fs', map, env) t1 in
                ((fs, map, env), (pat', t1')))
          in
          (acc, Term.match_ t1' pats')
      | _ ->
          let env, t = fld.term_rec (fs, map, env) t in
          (env, set_afv_shallowly t));
  fld.pat <-
    (fun ((fs, map, env) as acc) p ->
      let acc, desc =
        match p.pat_desc with
        | PWhen (p1, t) ->
            let fs' = filter_bv ~fs (get_bv_pat p1) in
            let (_, map, _), p1' = fld.pat (fs, map, env) p1 in
            let (_, map, _), t' = fld.term (fs', map, env) t in
            ((fs, map, env), PWhen (p1', t'))
        | PEval _ -> [%unsupported]
        | _ ->
            let acc, p' = fld.pat_rec acc p in
            (acc, p'.pat_desc)
      in
      (acc, make_pattern desc p.pat_typ));
  fun ?(env = !!Tenv.init) fs t ->
    let (_, map, _), t' = fld.term (fs, [], env) t in
    (map, t')

let copy_poly_ext_funs ?eq t : (id * id) list * term =
  let eq =
    eq
    |> Option.default_delayed (fun () ->
           let env = Tenv.add_typ_decl (List.flatten @@ col_type_decl t) !!Tenv.init in
           fun x y -> Id.(x = y) && can_unify ~env (Id.typ x) (Id.typ y))
  in
  let fv_map =
    let fv = get_fv_unique ~eq t in
    fv
    |> List.filter (fun x -> 2 <= List.count (Id.eq x) fv)
    |> List.map (Pair.add_right Id.new_var_id)
  in
  (fv_map, map_var (List.subst ~eq fv_map) t)

let copy_poly_values : term -> (id * id) list * (id -> id -> bool) * term * make_get_rtyp_single =
  let fld = Fold_tr.make () in
  fld.desc <-
    (fun (env, map) desc ->
      match desc with
      | Local (Decl_let bindings, t2) when List.exists (is_poly_typ -| Id.typ -| fst) bindings ->
          Dbg.printf "POLY %a:@." Print.(list id_typ) (List.map fst bindings);
          let (_, map), t2 = fld.term (env, map) t2 in
          let fs = List.map fst bindings in
          let map_renames, t2_renamed = rename_poly_values ~env fs t2 in
          let map_renames, t2 =
            match map_renames with
            | [] -> ([ List.map Pair.copy fs ], t2)
            | [ map_rename ] ->
                ([ List.map (fun (f, g) -> (f, Id.set_id g (Id.id f))) map_rename ], t2)
            | _ -> (map_renames, t2_renamed)
          in
          Dbg.printf "@[<hv 2>COPY%a:@ %a@.@."
            Print.(list id_typ)
            fs
            Print.(list (list (__ * id_typ)))
            map_renames;
          let map, bindingss =
            List.L.fold_left map_renames ~init:(map, []) ~f:(fun (map, bindingss) map_rename ->
                let _, bindings' =
                  List.L.fold_right_map bindings ~init:[] ~f:(fun (x, t) tvar_env ->
                      let tvar_env, x_ty = copy_tvar_typ ~env:tvar_env @@ Id.typ x in
                      let x' = Id.set_typ x x_ty in
                      let tvar_env, t' = copy_tvar ~env:tvar_env t in
                      (tvar_env, (x', t')))
                in
                List.iter2 (fun (f, _) (f', _) -> unify (Id.typ f) (Id.typ f')) bindings' map_rename;
                let map, bindings =
                  List.L.fold_right_map bindings' ~init:map ~f:(fun (x, t) map ->
                      let x' = Id.List.assoc x map_rename in
                      let (_, map), t' = t |> subst_var_map map_rename |> fld.term (env, map) in
                      (try unify_app_args t'
                       with CannotUnify _ ->
                         unsupported "Polymorphic use in let ... and ..." (* TODO: See TODO.md *));
                      instansiate_tvar Ty.int t';
                      (map, (x', t')))
                in
                (map_rename @ map, bindings :: bindingss))
          in
          let t = List.fold_right Term.let_ bindingss t2 in
          if !!Dbg.check then Type_check.check ~env ~ty:t.typ t;
          ((env, map), t.desc)
      | _ -> fld.desc_rec (env, map) desc);
  fld.term <-
    (fun env t ->
      let env, desc = fld.desc env t.desc in
      let env, typ = fld.typ env t.typ in
      (env, make ~attr:t.attr desc typ));
  fld.typ <- Pair.pair;
  fun t ->
    unify_pattern_var t;
    let env = Tenv.add_typ_decl (List.flatten @@ col_type_decl t) !!Tenv.init in
    let eq x y = Id.(x = y) && can_unify ~env (Id.typ x) (Id.typ y) in
    let (_, map), t' = fld.term (env, []) t in
    let make_get_rtyp get_rtyp f =
      let fs = Id.List.assoc_all f map in
      if fs = [] then get_rtyp f else Ref_type.Inter (Id.typ f, List.map get_rtyp fs)
    in
    let map, t'' = copy_poly_ext_funs ~eq t' in
    (map, eq, t'', make_get_rtyp)

let rec map_main f t : term =
  match t.desc with
  | Local (decls, t') ->
      let desc = Local (decls, map_main f t') in
      make desc t.typ
  | _ -> f t

(* the replaced main must be unit or eod if `not force` *)
let rec replace_main ?(force = false) ~main t : term =
  match t.desc with
  | Local (decl, t2) -> make_local decl @@ replace_main ~force ~main t2
  | Const Unit -> main
  | End_of_definitions -> main
  | Var x when Lid.typ x = Ty.unit -> main
  | Tuple [] -> main
  | _ when force -> main
  | _ -> assert false

let main_name = "main"

(** Same as [replace_main] but the type of the resulting program is unit *)
let replace_main_wrap ?(force = false) main t : term =
  let u = Id.new_var ~name:main_name main.typ in
  replace_main ~force ~main:Term.(let_nonrec [ (u, main) ] unit) t

let ref_to_assert ?(make_fail = make_fail ?loc:None ~force:true) ?typ_exn ref_env t : term =
  let typ_exn = match typ_exn with None -> find_exn_typ t | Some typ -> Some typ in
  let ref_env = Ref_type.Env.to_list ref_env in
  let main =
    let aux (f, typ) =
      if not @@ can_unify (Id.typ f) (Ref_type.to_simple typ) then (
        Format.eprintf "VAR: %a@." Id.print f;
        Format.eprintf "  Prog: %a@." [%pr: typ] @@ Id.typ f;
        Format.eprintf "  Spec: %a@." Ref_type.print typ;
        failwith "Type of %a in the specification is wrong?" Print.id f);
      let genv', cenv', t_typ =
        Ref_type_gen.generate_check ~typ_exn ~make_fail ~genv:[] ~cenv:[] f typ
      in
      let defs = List.map snd (genv' @ cenv') in
      make_lets defs @@ make_assert t_typ
    in
    let ts = List.map aux ref_env in
    Term.(seqs ts unit)
  in
  let map = List.map (Pair.map_snd Ref_type.to_abst_typ) ref_env in
  merge_bound_var_typ map @@ replace_main_wrap main t

let make_main catch_all f : term =
  let xs = get_args (Lid.typ f) in
  let bindings =
    let aux i x =
      let x' = Id.new_var ~name:("arg" ^ string_of_int @@ (i + 1)) @@ Id.typ x in
      let t = make_rand_unit ~expand:false @@ Id.typ x in
      (x', t)
    in
    List.mapi aux xs
  in
  let ys = List.map fst bindings in
  Term.(lets bindings (catch_all (var_lid f @ vars ys)))

(** If an argument of t is TVar, it is instansiated with TInt by defined_rand *)
let set_main t : term * lid option =
  let catch_all = make_catch_all t in
  match List.decomp_snoc_opt @@ get_last_definition t with
  | None ->
      let u = Id.new_var ~name:"main" t.typ in
      (Term.(let_ [ (u, catch_all t) ] unit), None)
  | Some (_, (f, _)) ->
      let main = make_main catch_all f in
      (replace_main_wrap main t, Some f)

let set_main_for ?(force = false) targets t : term option * term =
  let catch_all = make_catch_all t in
  match get_last_definition t with
  | [] -> (None, Term.ignore (catch_all t))
  | _ ->
      let main = Term.tuple (List.map (make_main catch_all) targets) in
      (Some main, replace_main_wrap ~force main t |> elim_unused_let)

let recover_const_attr_shallowly t : term =
  let attr =
    match t.desc with
    | BinOp (_, t1, t2) -> make_attr [ t1; t2 ]
    | Not t -> make_attr [ t ]
    | If (t1, t2, t3) -> make_attr [ t1; t2; t3 ]
    | Proj (_, t) -> make_attr [ t ]
    | _ -> []
  in
  add_attrs attr t

let recover_const_attr : term -> term =
  let tr = Tr.make () in
  tr.term <- recover_const_attr_shallowly -| tr.term_rec;
  tr.term

let beta_reduce_trivial : term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun env t ->
      match t.desc with
      | App ({ desc = Var (LId f) }, ts) -> (
          try
            let n, t = Id.List.assoc f env in
            let check t = has_no_effect t || List.Set.([ ATerminate; ANotFail ] <= t.attr) in
            let ts' = List.map (tr.term env) ts in
            if n = List.length ts && List.for_all check ts' then alpha_rename t else raise Not_found
          with Not_found -> tr.term_rec env t)
      | Local (Decl_let bindings, t1) ->
          let env' =
            let aux (f, t) =
              let xs, t = decomp_funs t in
              if get_fv t = [] then Some (f, (List.length xs, t)) else None
            in
            List.filter_map aux bindings @ env
          in
          let bindings' = List.map (Pair.map_snd @@ tr.term env') bindings in
          make_let bindings' @@ tr.term env' t1
      | _ -> recover_const_attr_shallowly @@ tr.term_rec env t);
  fun t -> t |> tr.term [] |> elim_unused_let |> inline_var_const

let exists_exception : term -> bool =
  let col = Col.make false ( || ) in
  col.desc <-
    (fun desc ->
      match desc with Event ("fail", _) -> true | Raise _ -> true | _ -> col.desc_rec desc);
  col.term

let ignore_non_termination : term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun fail_free desc ->
      match desc with
      | App ({ desc = Var (LId f) }, ts)
        when Id.List.mem f fail_free && can_unify Ty.unit (make_app (make_var f) ts).typ ->
          Const Unit
      | Local (Decl_let bindings, t1) ->
          let bindings' = List.map (Pair.map_snd @@ tr.term fail_free) bindings in
          let fv = get_fv t1 in
          let check t =
            let xs, t = decomp_funs t in
            List.for_all (Type_util.is_base_typ -| Id.typ) xs
            && List.Set.(get_fv t <= xs @@@ fail_free)
            && (not @@ exists_exception t)
          in
          let fail_free' =
            List.filter_map (fun (f, t) -> if check t then Some f else None) bindings'
          in
          let bindings'' =
            List.filter_out
              (fun (f, _) -> Id.List.mem f fail_free' && (not @@ Id.List.mem f fv))
              bindings'
          in
          (make_let bindings'' @@ tr.term (fail_free' @@@ fail_free) t1).desc
      | _ -> tr.desc_rec fail_free desc);
  tr.term []

let null_tuple_to_unit : term -> term =
  let tr = Tr.make () in
  tr.desc <- (fun desc -> match desc with Tuple [] -> Const Unit | _ -> tr.desc_rec desc);
  tr.typ <- (fun typ -> match typ with TTuple [] -> Ty.unit | _ -> tr.typ_rec typ);
  tr.term

let beta_full_app : id * id list * term * (term -> term) -> term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun ((f, xs, t1, cont) as arg) t2 ->
      match t2.desc with
      | App ({ desc = Var (LId g) }, ts) when Id.(f = g) && List.length xs = List.length ts ->
          subst_with_rename_map ~check:true (List.combine xs ts) t1 |> cont
      | Fun (g, _) when Id.(f = g) -> t2
      | Local (Decl_let bindings, _) when Id.List.mem_assoc f bindings -> t2
      | Match (t, pats) ->
          let pats' =
            List.map
              (fun (p, t) -> if Id.List.mem f (get_bv_pat p) then (p, t) else (p, tr.term arg t))
              pats
          in
          make_match (tr.term_rec arg t) pats'
      | _ -> set_afv_shallowly @@ tr.term_rec arg t2);
  tr.term

let beta_affine_fun : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t = set_afv_shallowly @@ tr.term_rec t in
      match t.desc with
      | Local (Decl_let [ (f, ({ desc = Fun _ } as t1)) ], t2)
        when (not (List.mem ADoNotInline t.attr)) && is_non_rec [ (f, t1) ] -> (
          match decomp_funs t1 with
          | xs, ({ desc = App _ } as t1) ->
              let used = Id.List.Set.(get_fv t1 && xs) in
              let not_rand_int =
                (* for non-termination *)
                match t1.desc with
                | App ({ desc = Const (Rand (TBase TInt, _)) }, _) -> false
                | _ -> true
              in
              if Id.List.is_unique used && not_rand_int && count_occurrence f t2 <= 1 then
                let t2' = beta_full_app (f, xs, t1, tr.term) t2 in
                if Id.List.mem f @@ get_fv t2' then Term.(let_ [ (f, funs xs t1) ] t2') else t2'
              else t
          | _ -> t)
      | _ -> t);
  tr.term

let beta_size1 : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      let size_1 t = match t.desc with Const _ | Var _ -> true | _ -> false in
      match desc with
      | App (t1, []) -> tr.desc t1.desc
      | App ({ desc = Fun (x, t) }, t2 :: ts) when size_1 t2 -> tr.desc @@ App (subst x t2 t, ts)
      | _ -> tr.desc_rec desc);
  tr.term <- set_afv_shallowly -| tr.term_rec;
  tr.term

let conv = Fpat.Formula.of_term -| FpatInterface.of_term
let is_sat = FpatInterface.is_sat -| conv
let is_valid = FpatInterface.is_valid -| conv
let implies ts t = FpatInterface.implies (List.map conv ts) [ conv t ]

let reconstruct : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t' =
        match t.desc with
        | Const _ -> add_attrs const_attr t
        | Var x -> make_var_lid x
        | Fun (x, t) -> make_fun x @@ tr.term t
        | App (t1, ts) -> make_app (tr.term t1) @@ List.map tr.term ts
        | If (t1, t2, t3) -> make_if (tr.term t1) (tr.term t2) (tr.term t3)
        | Local (Decl_let bindings, t) ->
            make_let (List.map (Pair.map_snd tr.term) bindings) @@ tr.term t
        | BinOp (op, t1, t2) -> make_binop op (tr.term t1) (tr.term t2)
        | Not t -> make_not @@ tr.term t
        | Tuple ts -> make_tuple @@ List.map tr.term ts
        | Proj (i, t) -> make_proj i @@ tr.term t
        | Field (t1, s) -> make_field ~ty:t.typ (tr.term t1) s
        | TryWith (t1, { desc = Fun (x, { desc = Match ({ desc = Var (LId y) }, pats) }) })
          when Id.(x = y) ->
            make_trywith t1 x pats
        | Constr (poly, c, ts) -> make_construct ~poly c (List.map tr.term ts) t.typ
        | _ -> tr.term_rec t
      in
      merge_attrs t.attr t');
  tr.typ <- Fun.id;
  tr.term

let simplify_if_cond : term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun cond desc ->
      match desc with
      | If (t1, t2, t3) ->
          let t1' = reconstruct t1 in
          let ts = decomp_and t1' in
          let t1'' =
            let simplify t =
              if has_no_effect t then
                if implies cond t then true_term
                else if implies cond @@ make_not t then false_term
                else t
              else t
            in
            make_ands @@ List.map simplify ts
          in
          let cond1 = List.filter has_no_effect ts @ cond in
          let cond2 = if has_no_effect t1' then make_not t1' :: cond else cond in
          let t2' = tr.term cond1 t2 in
          let t3' = tr.term (List.map make_not cond2) t3 in
          If (t1'', t2', t3')
      | _ -> tr.desc_rec cond desc);
  tr.term []

let decomp_var_match_tuple : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Match ({ desc = Var x }, [ ({ pat_desc = PTuple pats }, t) ]) -> (
          try
            let aux i pat =
              let y = match pat.pat_desc with PVar y -> y | _ -> raise Not_found in
              (y, make_proj i @@ make_var_lid x)
            in
            (make_lets (List.mapi aux pats) t).desc
          with Not_found -> tr.desc_rec desc)
      | _ -> tr.desc_rec desc);
  tr.term

let tfuns_to_tfun : term -> term =
  let tr = Tr.make () in
  tr.typ <-
    (fun typ ->
      match typ with
      | TFuns (xs, typ) ->
          let xs' = List.map tr.var xs in
          let typ' = tr.typ typ in
          List.fold_right _TFun xs' typ'
      | _ -> tr.typ_rec typ);
  tr.term

let tfun_to_tfuns : term -> term =
  let tr = Tr.make () in
  tr.typ <-
    (fun typ ->
      match typ with
      | TFun (x, typ) ->
          let x' = tr.var x in
          let typ' = tr.typ typ in
          TFuns ([ x' ], typ')
      | _ -> tr.typ_rec typ);
  tr.term

let split_assert_and : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match decomp_assert t with
      | Some (t1, loc) ->
          t1 |> decomp_and |> List.map (make_assert ?loc) |> List.reduce_right make_seq
      | _ -> tr.term_rec t);
  tr.term

let inline_specified : id * id list * term -> term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun (f, xs, t1) t ->
      match t.desc with
      | Var (LId g) when Id.(f = g) ->
          if xs <> [] then invalid_arg "inline_specified?";
          t1
      | App ({ desc = Var (LId g) }, ts) when Id.(f = g) ->
          if List.length xs <> List.length ts then invalid_arg "inline_specified!";
          subst_map (List.combine xs ts) t1
      | _ -> tr.term_rec (f, xs, t1) t);
  tr.term

let add_id_if : (term -> bool) -> term -> int * term =
  let tr = Tr2.make () in
  tr.term <-
    (fun (f, cnt) t ->
      let t' = tr.term_rec (f, cnt) t in
      if f t then
        let id = AId cnt#gen in
        add_attr id t'
      else t');
  fun f t ->
    let cnt = new counter in
    let t' = tr.term (f, cnt) t in
    (cnt#peep, t')

let add_id t = add_id_if (Fun.const true) t
let remove_id t = filter_attr (function AId _ -> false | _ -> true) t
let remove_tid label t = filter_tattr (function TAId (s, _) when s = label -> false | _ -> true) t

let replace_fail : by:desc -> term -> term =
  let f by desc =
    match desc with
    | App ({ desc = Event ("fail", _) }, [ { desc = Const Unit } ]) -> Some by
    | _ -> None
  in
  fun ~by t -> trans_if_desc (f by) t

let replace_fail_with_bot =
  let f ids t =
    match t.desc with
    | App ({ desc = Event ("fail", _) }, [ { desc = Const Unit } ]) ->
        if List.exists (function AId id -> List.mem id ids | _ -> false) t.attr then None
        else Some (make_bottom t.typ)
    | _ -> None
  in
  fun ?(except = []) t -> trans_if (f except) t

(** eta_normal does not see the existence of side-effects *)
let eta_normal : term -> term =
  let tr = Tr.make () in
  let map_arg t =
    match t.desc with
    | Var _ -> t
    | App (t1, ts) ->
        let t1' = tr.term t1 in
        let desc = App (t1', List.map tr.term ts) in
        make desc t.typ
    | _ -> assert false
  in
  tr.term <-
    (fun t ->
      match t.desc with
      | App _ when is_fun_typ t.typ ->
          let t' = map_arg t in
          let xs = t.typ |> decomp_tfun |> fst |> List.map Id.new_var_id in
          make_funs xs (make_app t' @@ List.map make_var xs)
      | App _ -> map_arg t
      | _ -> tr.term_rec t);
  tr.term

let direct_from_CPS : term -> term =
  let tr = Tr.make () in
  tr.typ <- (fun typ -> if typ = typ_result then Ty.unit else tr.typ_rec typ);
  tr.desc <-
    (fun desc ->
      match desc with
      | Const CPS_result -> Const Unit
      | App ({ desc = Event (s, true) }, [ t1; t2 ]) ->
          let t1' = tr.term t1 in
          let t2' = tr.term t2 in
          (make_seq (make_app (make_event s) [ t1' ]) (make_app t2' [ unit_term ])).desc
      | App ({ desc = Const (Rand (typ, true)) }, [ t1; t2 ]) ->
          let t1' = tr.term t1 in
          let t2' = tr.term t2 in
          (make_app t2' [ make_app (make_rand typ) [ t1' ] ]).desc
      | _ -> tr.desc_rec desc);
  tr.term

let reduce_fail_unit : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t = tr.term_rec t in
      match t.desc with
      | Local
          ( Decl_let
              [
                ( _,
                  ({ desc = App ({ desc = Event ("fail", false) }, [ { desc = Const Unit } ]) } as
                   t1) );
              ],
            _ ) ->
          t1
      | _ -> t);
  tr.term

let remove_no_effect_trywith : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t' = tr.term_rec t in
      match t'.desc with TryWith (t, _) when has_no_effect t -> t | _ -> t');
  tr.term

let bool_eta_reduce : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t' = tr.term_rec t in
      match t'.desc with If (t1, { desc = Const True }, { desc = Const False }) -> t1 | _ -> t');
  tr.term

let eta_tuple : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match tr.desc_rec desc with
      | Proj (i, { desc = Tuple ts }) when List.for_alli (fun j t -> i = j || has_no_effect t) ts ->
          (List.nth ts i).desc
      | desc' -> desc');
  tr.term <- set_afv_shallowly -| tr.term_rec;
  tr.term

let eta_reduce : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      let desc' = tr.desc_rec desc in
      match desc' with
      | Fun (x, { desc = App (t1, ts) }) -> (
          let ts', t2 = List.decomp_snoc ts in
          match t2.desc with
          | Var (LId y) when Id.(x = y) ->
              let t1' = make_app t1 ts' in
              if has_no_effect t1' && (not @@ occur_in x t1') then t1'.desc else desc'
          | _ -> desc')
      | _ -> desc');
  tr.term

let name_read_int : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let desc' =
        match t.desc with
        | Local
            ( Decl_let
                ([ (_, { desc = App ({ desc = Const (Rand _) }, [ { desc = Const Unit } ]) }) ] as
                 bindings),
              t ) ->
            Local (Decl_let bindings, tr.term t)
        | App ({ desc = Const (Rand (TBase TInt, false)); attr }, [ { desc = Const Unit } ])
          when List.mem AAbst_under attr ->
            let x = Id.new_var ~name:"r" Ty.int in
            (make_let [ (x, t) ] @@ make_var x).desc
        | _ -> tr.desc_rec t.desc
      in
      make desc' t.typ ~attr:t.attr);
  tr.term

let reduce_size_by_beta : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let desc =
        match t.desc with
        | Local
            ( Decl_let
                ([ (_, { desc = App ({ desc = Const (Rand _) }, [ { desc = Const Unit } ]) }) ] as
                 bindings),
              t ) ->
            Local (Decl_let bindings, tr.term t)
        | App ({ desc = Const (Rand (TBase TInt, false)); attr }, [ { desc = Const Unit } ])
          when List.mem AAbst_under attr ->
            let x = Id.new_var ~name:"r" Ty.int in
            (make_let [ (x, t) ] @@ make_var x).desc
        | _ -> tr.desc_rec t.desc
      in
      make desc t.typ);
  tr.term

exception AllArgumentsRemoved
(* WORKAROUND: we must support the case that all the arguments can be removed *)

let elim_redundant_arg : term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun (vars : id list) desc ->
      match desc with
      | Local (Decl_let [ (f, t1) ], t) when not @@ is_non_rec [ (f, t1) ] -> (
          let xs, t1 = decomp_funs t1 in
          let fixed_args = find_fixed_args (LId f) (List.map Lid._LId xs) t1 in
          let default () =
            Local (Decl_let [ (f, make_funs xs @@ tr.term_rec (xs @ vars) t1) ], tr.term_rec vars t)
          in
          if fixed_args = [] then !!default
          else
            let ixs =
              List.filter_mapi
                (fun i x -> if List.mem ~eq:Lid.eq (LId x) fixed_args then Some (i, x) else None)
                xs
            in
            try
              match col_app_args (LId f) t with
              | [] ->
                  Local
                    ( Decl_let [ (f, make_funs xs @@ tr.term_rec (xs @ vars) t1) ],
                      tr.term_rec vars t )
              | args :: argss ->
                  let args' = List.map Val._Var args in
                  let argss' = List.map (List.map Val._Var) argss in
                  let redundant =
                    ixs
                    |> List.filter (fun (i, _) ->
                           match List.nth args' i with
                           | None -> false
                           | Some (LId x) ->
                               Id.List.mem x vars
                               && List.for_all
                                    (fun args'' ->
                                      Option.exists Lid.(( = ) (LId x)) @@ List.nth args'' i)
                                    argss'
                           | Some _ -> assert false
                           | exception _ -> false)
                  in
                  let pos = List.map fst redundant in
                  let map = List.map (fun (i, x) -> (x, List.nth args i)) redundant in
                  let xs' = List.fold_right List.remove_at pos xs in
                  if xs' = [] then raise AllArgumentsRemoved;
                  let f' = Id.map_typ (List.fold_right remove_arg_at pos) f in
                  let remove_arg =
                    let tr = Tr.make () in
                    tr.desc <-
                      (fun desc ->
                        match desc with
                        | App ({ desc = Var (LId g) }, ts) when Id.(f = g) ->
                            App (make_var f', List.fold_right List.remove_at pos ts)
                        | Fun (g, _) when Id.(f = g) -> desc
                        | Local (Decl_let bindings, _) when List.exists (fst |- Id.( = ) f) bindings
                          ->
                            desc
                        | _ -> tr.desc_rec desc);
                    tr.term
                  in
                  let t1' = t1 |> tr.term (xs @ vars) |> subst_map map |> remove_arg in
                  let t' = t |> tr.term vars |> remove_arg in
                  Local (Decl_let [ (f', make_funs xs' t1') ], t')
            with AllArgumentsRemoved -> !!default)
      | Local (Decl_let bindings, t) ->
          let bindings' = List.map (fun (f, t1) -> (f, tr.term_rec vars t1)) bindings in
          Local (Decl_let bindings', tr.term_rec vars t)
      | _ -> tr.desc_rec vars desc);
  tr.term []

(* TODO: recursively apply the separation to "recs" if need *)
let split_let : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t = tr.term_rec t in
      match t.desc with
      | Local (Decl_let bindings, t2) ->
          let fvs = List.flatten_map (snd |- get_fv ~force:true) bindings in
          let recs, non_recs = List.partition (fst |- Id.List.mem -$- fvs) bindings in
          make_let recs @@ make_lets non_recs t2
      | _ -> t);
  tr.typ <- Fun.id;
  tr.term

let remove_effect_attribute : term -> term =
  let tr = Tr.make () in
  tr.attr <- List.filter (function AEffect _ -> false | _ -> true);
  tr.typ <-
    (fun ty ->
      match ty with
      | TAttr (attrs, ty1) ->
          let attrs' = List.filter (function TAEffect _ -> false | _ -> true) attrs in
          let ty1' = tr.typ ty1 in
          if attrs' = [] then ty1' else TAttr (attrs', ty1')
      | _ -> tr.typ_rec ty);
  tr.term

let assign_id_to_tvar : term -> term =
  let fld = Fold_tr.make () in
  fld.typ <-
    (fun cnt ty ->
      match ty with
      | TVar (b, { contents = None }, _) -> (cnt + 1, TVar (b, { contents = None }, cnt))
      | ty -> fld.typ_rec cnt ty);
  snd -| fld.term 0

let inline_record_type : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Local (Decl_type decls, t) ->
          let cs =
            List.rev_flatten_map
              (snd |- snd |- get_tconstr_typ |- List.filter_map (fst |- Type.Val._LId))
              decls
          in
          let check (c, (params, ty)) =
            if params <> [] then [%unsupported];
            if Type.Is._TRecord ty && Id.List.mem c cs then unsupported "recursive record types"
          in
          List.iter check decls;
          let decls1, decls2 =
            List.partition (function _, (_, TRecord _) -> true | _ -> false) decls
          in
          t
          |> tr.term
          |> Term.type_ decls2
          |> List.fold_right (Fun.uncurry subst_tconstr) decls1
          |> Syntax.desc
      | Module _ -> unsupported "inline_record_type (module)"
      | _ -> tr.desc_rec desc);
  tr.term

let simplify_pattern_term, simplify_pattern =
  let tr = Tr.make () in
  let is_any p = p.pat_desc = PAny in
  let is_all_any ps = List.for_all is_any ps in
  tr.pat <-
    (fun p ->
      match tr.pat_rec p with
      | { pat_desc = POr (p1, p2) } when is_all_any [ p1; p2 ] -> make_pany p.pat_typ
      | { pat_desc = PTuple ps } when is_all_any ps -> make_pany p.pat_typ
      | { pat_desc = PAlias (p, x) } when is_any p -> make_pvar x
      | p' -> p');
  (tr.term, tr.pat)

let remove_pnondet : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match (desc, tr.desc_rec desc) with
      | Match (_, pats), Match (t', pats') ->
          let pats'' =
            let aux (p, _) (p', t') =
              let p'' = if has_pnondet p then Pat.when_ p' Term.randb else p' in
              (p'', t')
            in
            List.map2 aux pats pats'
          in
          Match (t', pats'')
      | _, desc' -> desc');
  tr.pat <-
    (fun p ->
      let p' = tr.pat_rec p in
      match p'.pat_desc with
      | PNondet | POr ({ pat_desc = PAny }, { pat_desc = PAny }) -> Pat.__ p'.pat_typ
      | _ -> p');
  tr.term <- set_afv_shallowly -| tr.term_rec;
  tr.term

let simplify_match : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | Match (t1, ({ pat_desc = PTuple ps }, t2) :: _) when List.for_all Is._PVar ps ->
          let xs = List.map ValE._PVar ps in
          let x = new_var_of_term t1 in
          make_lets ((x, t1) :: List.mapi (fun i y -> (y, [%term x##i])) xs) @@ tr.term t2
      | Match (t1, pats) -> (
          let rec elim_unused = function
            | [] -> []
            | (({ pat_desc = PAny | PVar _ }, _) as pct) :: _ -> [ pct ]
            | pct :: pats -> pct :: elim_unused pats
          in
          let pats' = pats |> List.map (Pair.map simplify_pattern tr.term) |> elim_unused in
          match pats' with
          | [] -> assert false
          | [ ({ pat_desc = PAny }, t) ] ->
              [%term
                `t1;
                `t]
          | [ ({ pat_desc = PConst { desc = Const Unit } }, t) ] ->
              [%term
                `t1;
                `t]
          | [ ({ pat_desc = PVar x }, t) ] -> make_let [ (x, t1) ] t
          | [ ({ pat_desc = PWhen ({ pat_desc = PVar x }, t2) }, t3) ] ->
              [%term
                let x = `t1 in
                if `t2 then `t3 else bot [@ty t.typ]]
          | _ -> make_match (tr.term t1) pats')
      | _ -> tr.term_rec t);
  tr.term

(* must be after encoding lists *)
let remove_match : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t = tr.term_rec t in
      match t.desc with
      | Match (t1, pats) ->
          let x, bind =
            match t1.desc with
            | Var (LId x) -> (x, Fun.id)
            | _ ->
                let x = new_var_of_term t1 in
                (x, Term.let_ [ (x, t1) ])
          in
          let remove (p, t) acc =
            match p.pat_desc with
            | PAny -> t
            | PNondet -> Term.br t acc
            | PVar y ->
                [%term
                  let y = x in
                  `t]
            | PAlias _ -> [%unsupported]
            | PConst c -> [%term if x = `c then `t else `acc]
            | PConstr _ -> [%unsupported]
            | PNil -> [%unsupported]
            | PCons _ -> [%unsupported]
            | PTuple _ -> [%unsupported]
            | PRecord _ -> [%unsupported]
            | PNone -> [%unsupported]
            | PSome _ -> [%unsupported]
            | POr _ -> [%unsupported]
            | PWhen ({ pat_desc = PAny }, cond) -> [%term if `cond then `t else `acc]
            | PWhen ({ pat_desc = PVar y }, cond) ->
                [%term
                  let y = x in
                  if `cond then `t else `acc]
            | PWhen (_, cond) -> [%term if `cond then `t else `acc]
            | PLazy _ -> [%unsupported]
            | PEval _ -> [%unsupported]
          in
          List.fold_right remove pats (Term.bot t.typ) |> bind
      | _ -> t);
  tr.term

let split_type_decls_aux (decls : type_decls) : type_decls list =
  let edges =
    let dummy = Id.make "!dummy!" () in
    let mk_edge (c, (_, ty)) =
      let cs = List.filter_map (fst |- Type.Val._LId) @@ get_tconstr_typ ty in
      let cs = if cs = [] then [ dummy ] else cs in
      List.rev_map (Pair.pair c) cs
    in
    List.rev_flatten_map mk_edge decls
  in
  let edges = List.map (Pair.map_same (Id.set_attr -$- [])) edges (* WORKAROUND *) in
  Graph_wrapper.topological_sort ~eq:Id.eq ~key_of:fst ~edges decls

let split_type_decls : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match tr.desc_rec desc with
      | Local (Decl_type decls, t) ->
          let declss = split_type_decls_aux decls in
          (List.fold_right Term.type_ declss t).desc
      | desc -> desc);
  tr.typ <- Fun.id;
  tr.term

let lift_pwhen_pat : pattern -> pattern =
  let col = Tr_col2.make Term.true_ Term.( && ) in
  col.pat <-
    (fun () p ->
      match p.pat_desc with
      | PWhen (p, c) ->
          let c', p' = col.pat () p in
          (Term.(c' && c), p')
      | POr (p1, p2) ->
          let c1, p1' = col.pat () p1 in
          let c2, p2' = col.pat () p2 in
          assert (c1.desc = Const True && c2.desc = Const True);
          (Term.true_, make_pattern ~attr:p.pat_attr (POr (p1', p2')) p.pat_typ)
      | _ -> col.pat_rec () p);
  fun p ->
    let c, p' = col.pat () p in
    Pat.when_ p' c

let lift_pwhen : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match tr.desc_rec desc with
      | Match (t1, pats) ->
          let pats' = Fmap.(list (lift_pwhen_pat * __)) pats in
          Match (t1, pats')
      | desc -> desc);
  tr.term

let recover_pat_bv ~tr_typ ~before:(p_before, _) ~after:(p_after, t) =
  let make x =
    let ty = tr_typ @@ Id.typ x in
    (Id.set_typ x ty, Term.rand ty)
  in
  let bindings =
    (* WORKAROUND: ~force:true (this must be removed if the attributes are correct) *)
    get_bv_pat ~force:true p_before
    |> Id.List.Set.diff -$- get_bv_pat ~force:true p_after
    |> List.map make
  in
  let p_after =
    let add_bindings =
      let tr = Tr.make () in
      tr.pat <-
        (fun p ->
          match p.pat_desc with
          | PWhen (p1, cond) ->
              let bv = get_bv_pat p1 in
              let bindings' = List.filter (fst |- Id.List.mem -$- bv) bindings in
              Pat.when_ p1 (make_lets_s bindings' cond)
          | _ -> tr.pat_rec p);
      tr.pat
    in
    add_bindings p_after
  in
  (p_after, make_lets_s bindings t)

let trans_match_with_recover_pat_bv_desc ~tr_desc_rec ~tr_typ desc =
  let pats = match desc with Match (_, pats) -> pats | _ -> invalid_arg "%s" __FUNCTION__ in
  let t1, pats' =
    match tr_desc_rec desc with
    | Match (t', pats') -> (t', pats')
    | _ -> invalid_arg "%s" __FUNCTION__
  in
  let pats'' = List.map2 (fun before after -> recover_pat_bv ~tr_typ ~before ~after) pats pats' in
  Match (t1, pats'')

let trans_match_with_recover_pat_bv ~tr_desc_rec ~tr_typ t =
  let desc = trans_match_with_recover_pat_bv_desc ~tr_desc_rec ~tr_typ t.desc in
  let ty = tr_typ t.typ in
  make ~attr:t.attr desc ty

let abst_recdata : string -> (typ -> type_decls list -> bool) -> term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun ((s, check, env) as arg) t ->
      let desc =
        match t.desc with
        | Local (Decl_type decls, t) ->
            let arg' = (s, check, decls :: env) in
            let t' = tr.term arg' t in
            let decls' = Fmap.(list (snd (snd (tr.typ arg')))) decls in
            Local (Decl_type decls', t')
        | Match (_, _) ->
            trans_match_with_recover_pat_bv_desc ~tr_desc_rec:(tr.desc_rec arg) ~tr_typ:(tr.typ arg)
              t.desc
        | Constr (_, _, ts) when check t.typ env ->
            Flag.Abstract.over s;
            let ts' = List.map (tr.term arg) ts in
            Term.(seqs ts' randi).desc
        | _ -> tr.desc_rec arg t.desc
      in
      let typ = tr.typ arg t.typ in
      make desc typ ~attr:t.attr);
  tr.typ <-
    (fun (s, check, env) ty ->
      match ty with
      | (TConstr _ | TVariant _) when check ty env -> Ty.int
      | _ -> tr.typ_rec (s, check, env) ty);
  tr.pat <-
    (fun (s, check, env) p ->
      match p.pat_desc with
      | PConstr _ when check p.pat_typ env ->
          Flag.Abstract.over s;
          make_pnondet Ty.int
      | _ ->
          let p' = tr.pat_rec (s, check, env) p in
          make_pattern p'.pat_desc p'.pat_typ);
  fun s check t ->
    t |> tr.term (s, check, []) |> remove_pnondet |> simplify_pattern_term |> split_type_decls

let replace_list_with_int : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let desc =
        match t.desc with
        | App ({ desc = Var len }, [ t ]) when is_length_var len ->
            let t' = tr.term t in
            Term.(seq t' randi).desc
        | Match (_, pats) ->
            let t1', pats' =
              match tr.desc_rec t.desc with Match (t', pats') -> (t', pats') | _ -> assert false
            in
            let pats'' =
              let aux (p1, _) (p2, t) =
                let make x =
                  let ty = tr.typ @@ Id.typ x in
                  (Id.set_typ x ty, make_rand_unit ty)
                in
                let bindings =
                  get_bv_pat p1
                  |> List.unique ~eq:Id.eq
                  |> List.Set.diff ~eq:Id.eq -$- get_bv_pat p2
                  |> List.map make
                in
                (p2, make_lets_s bindings t)
              in
              List.map2 aux pats pats'
            in
            Match (t1', pats'')
        | Nil -> Term.randi.desc
        | Cons (t1, t2) ->
            Flag.Abstract.over "list-to-int";
            let t1' = tr.term t1 in
            let t2' = tr.term t2 in
            Term.(seqs [ t1'; t2' ] randi).desc
        | _ -> tr.desc_rec t.desc
      in
      let typ = tr.typ t.typ in
      make desc typ ~attr:t.attr);
  tr.typ <-
    (fun ty -> match ty with TConstr (c, _) when c = C.list -> Ty.int | _ -> tr.typ_rec ty);
  tr.pat <-
    (fun p ->
      match p.pat_desc with
      | PNil | PCons _ ->
          Flag.Abstract.over "list-to-int";
          make_pnondet Ty.int
      | _ -> set_afv_abv_pat @@ tr.pat_rec p);
  fun t -> t |> tr.term |> remove_pnondet |> simplify_pattern_term

let abst_ext_recdata : term -> term =
  let typ_not_in_env ty env =
    match elim_tattr ty with
    | TConstr (LId s, _) ->
        (not (List.exists (Id.List.mem_assoc s) env)) && not (is_prim_constr (Type.LId s))
    | TVariant _ -> false
    | _ -> true
  in
  abst_recdata "External rec. data with int" typ_not_in_env

let replace_data_with_int = abst_recdata "Data with int" (fun ty _ -> not (is_prim_tconstr ty))

let replace_data_with_int_but tys : term -> term =
  abst_recdata "Data with int except specific types" (fun ty _ ->
      (not @@ List.mem ty tys) && not (is_prim_tconstr ty))

let replace_poly_variant_with_int : term -> term =
  let check ty env =
    let rec is_poly_variant = function
      | TConstr (LId s, _) ->
          List.find_map_opt (Id.List.assoc_opt s) env |> Option.exists (snd |- is_poly_variant)
      | TVariant (VPoly _, _) -> true
      | _ -> false
    in
    is_poly_variant ty
  in
  abst_recdata "Polymorphic variant with int" check

let replace_abst_with_int : term -> term =
  abst_recdata "Data with int except specific types" (fun ty _ ->
      match ty with TConstr (c, []) -> C.is_abst c | _ -> false)

let replace_exn_with_int t : term =
  match find_exn_typ t with
  | None -> t
  | Some ty_exn ->
      let check ty _ = ty = ty_exn in
      abst_recdata "Exceptions with int" check t

let replace_complex_data_with_int : term -> term =
  let rec get_leaves ty =
    match elim_tattr ty with
    | TTuple xs -> List.flatten_map (Id.typ |- get_leaves) xs
    | TVariant (_, rows) -> List.flatten_map (row_args |- List.flatten_map get_leaves) rows
    | _ -> [ ty ]
  in
  let is_complex ty env =
    match elim_tattr ty with
    | TConstr (LId s, _) -> (
        try
          List.find (Id.List.mem_assoc s) env
          |> List.flatten_map (snd |- snd |- get_leaves)
          |> List.filter (function TConstr (LId s', _) -> not Id.(s = s') | _ -> true)
          |> List.exists (tconstr_occurs s)
        with Not_found -> not (is_prim_constr (Type.LId s)))
    | _ -> false
  in
  abst_recdata "Complex data with int" is_complex

(* ASSUME: there is no recursive types *)
let inline_type_decl : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      let t' = tr.term_rec t in
      match t'.desc with
      | Local (Decl_type decls, t1) -> List.fold_right (Fun.uncurry subst_tconstr) decls t1
      | _ -> t');
  tr.term

let mark_free_as_external : term -> term =
  let tr = Tr2.make () in
  let is_free_id bs x = not (Id.List.mem x bs || Id.is_primitive x) in
  let rec is_free_module bv (path : path) =
    match path with
    | LId c -> is_free_id bv (Id.set_typ c Ty.unknown)
    | LDot (p, _) | LApp (p, _) -> is_free_module bv p
  in
  let is_free (bv, _, _) (lid : lid) =
    match lid with
    | LId c -> is_free_id bv c
    | LDot (p, _) | LApp (p, _) -> is_free_module bv (path_of_lid p)
  in
  let is_free_path (bv, bt, _) (path : path) =
    match path with
    | LId c -> is_free_id bt c && not (List.mem ~eq:Path.eq path C.prims)
    | LDot (p, _) | LApp (p, _) -> is_free_module bv p
  in
  tr.desc <-
    (fun ((bv, bt, cache) as env) desc ->
      match desc with
      | Var lid when is_free env lid -> Var (Lid.map ~f:(Id.add_attr Id.External) lid)
      | Constr (false, c, ts) when is_free_path env c ->
          let c' = Path.map ~f:(Id.add_attr Id.External) c in
          let ts' = List.map (tr.term env) ts in
          Constr (false, c', ts')
      | Local (decl, _) ->
          let bv' = get_bv_decl decl @@@ bv in
          let bt' = get_bt_decl decl @@@ bt in
          tr.desc_rec (bv', bt', cache) desc
      | Fun (x, _) -> tr.desc_rec (x :: bv, bt, cache) desc
      | Match (t1, pats) ->
          let t1' = tr.term_rec env t1 in
          let aux (p, t) =
            let bv' = get_bv_pat p @ bv in
            let env = (bv', bt, cache) in
            (tr.pat env p, tr.term env t)
          in
          Match (t1', List.map aux pats)
      | Module decls -> Module (trans_decls_as_term (tr.term env) decls)
      | _ -> tr.desc_rec env desc);
  tr.pat <-
    (fun env p ->
      match p.pat_desc with
      | PConstr (false, c, ps) when is_free_path env c ->
          let c' = Path.map ~f:(Id.add_attr Id.External) c in
          let ps' = List.map (tr.pat env) ps in
          make_pattern ~attr:p.pat_attr (PConstr (false, c', ps')) p.pat_typ
      | _ -> tr.pat_rec env p);
  tr.lid <-
    (fun env lid -> if is_free env lid then Lid.map ~f:(Id.add_attr Id.External) lid else lid);
  tr.typ <-
    (fun ((_, _, cache) as env) ty ->
      match ty with
      | TConstr (c, tys) when is_free_path env c ->
          let c' = Path.map ~f:(Id.add_attr Id.External) c in
          tr.typ_rec env (TConstr (c', tys))
      | TModSig sgn -> (
          match Hashtbl.find_option cache ty with
          | Some r -> r
          | None ->
              let r =
                sgn
                |> List.map (function
                     | Sig_type decl -> Decl_type decl
                     | Sig_value x -> Decl_let [ (x, Term.dummy (Id.typ x)) ]
                     | Sig_ext ext -> Type_ext (Ext_type ext))
                |> trans_decls_as_term (tr.term env)
                |> List.map (function
                     | Decl_let [ (x, _) ] -> Sig_value x
                     | Decl_type decl -> Sig_type decl
                     | Type_ext (Ext_type ext) -> Sig_ext ext
                     | _ -> assert false)
                |> _TModSig
              in
              Hashtbl.add cache ty r;
              r)
      | _ -> tr.typ_rec env ty);
  tr.attr <- Fun.(const id);
  tr.term <- set_afv_shallowly --| tr.term_rec;
  tr.term ([], [], Hashtbl.create 100)

(** ASSUME: record types are inlined (the first argument is unused) *)
let complete_precord : term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun decls desc ->
      match desc with
      | Local (Decl_type decls', _) -> tr.desc_rec (decls' @ decls) desc
      | _ -> tr.desc_rec decls desc);
  tr.pat <-
    (fun decls p ->
      match p.pat_desc with
      | PRecord [ (label, p) ] when is_ref_typ p.pat_typ ->
          let p' = tr.pat decls p in
          make_pattern (PRecord [ (label, p') ]) p.pat_typ
      | PRecord pats ->
          let pats' =
            p.pat_typ
            |> ValE'._TRecord
            |> List.map (fun (s, (_, ty)) ->
                   match Id.List.assoc_opt s pats with
                   | None -> (s, make_pany ty)
                   | Some p -> (s, tr.pat decls p))
          in
          make_pattern (PRecord pats') p.pat_typ
      | _ -> p);
  tr.term []

let instansiate_weak_poly_types : term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun env t ->
      let uni ty1 ty2 =
        if is_weak_poly_typ ty1 || is_weak_poly_typ ty2 then
          (* WORDAROUND: [unify ~sub] must be used *)
          unify ~env ~only_weak:true ty1 ty2
      in
      match t.desc with
      | Deref t' ->
          uni (Ty.ref t.typ) t'.typ;
          tr.term_rec env t
      | SetRef (t1, t2) ->
          uni (Ty.ref t2.typ) t1.typ;
          tr.term_rec env t
      | Tuple ts ->
          let () =
            match elim_tattr t.typ with
            | TTuple xs ->
                let tys1 = List.map Id.typ xs in
                let tys2 = List.map Syntax.typ ts in
                List.iter2 uni tys1 tys2
            | _ -> ()
          in
          tr.term_rec env t
      | App (({ desc = Var (LId f) } as t1), ts)
        when List.exists (is_weak_poly_typ -| typ) (t1 :: ts) ->
          let rec unify ty ts =
            match (elim_tattr ty, ts) with
            | TFun (x, ty'), t2 :: ts' ->
                uni (Id.typ x) t2.typ;
                unify ty' ts'
            | _, [] -> uni ty t.typ
            | TVar (_, { contents = Some ty }, _), _ -> unify ty ts
            | TVar (_, ({ contents = None } as x), _), _ ->
                let ty1 = new_tvar () in
                let ty2 = new_tvar () in
                let ty = Ty.fun_ ty1 ty2 in
                x := Some ty;
                unify ty ts
            | _ -> assert false
          in
          let ts' = List.map (tr.term env) ts in
          unify t1.typ ts';
          Term.(var f @ ts')
      | Local (Decl_let [ (x, { desc = Var (LId y) }) ], _) ->
          uni (Id.typ x) (Id.typ y);
          tr.term_rec env t
      | Local (Decl_let defs, t1) ->
          (* the order of the transformations matters *)
          let defs' =
            defs
            |> Fmap.(list (pair (tr.var env) (tr.term env)))
            |@> List.iter (fun (x, t) -> uni (Id.typ x) t.typ)
          in
          let t1' = tr.term env t1 in
          make ~attr:t.attr (Local (Decl_let defs', t1')) t1'.typ
      | Local (Decl_type decls, _) ->
          let env' = Tenv.add_typ_decl decls env in
          tr.term_rec env' t
      | Match (t1, pats) ->
          let t1' = tr.term env t1 in
          let pats' =
            pats
            |> List.map (fun (p, t) ->
                   let p' = tr.pat env p in
                   let t' = tr.term env t in
                   let fv = get_fv ~force:true t' in
                   get_bv_pat p
                   |> List.iter (fun x ->
                          fv |> List.filter Id.(eq x) |> List.iter (uni (Id.typ x) -| Id.typ));
                   (p', t'))
          in
          make (Match (t1', pats')) t.typ
      | _ -> tr.term_rec env t);
  tr.term !!Tenv.init

let instansiate_poly_types_with_env : (id * typ) list -> term -> term =
  let it = Iter2.make () in
  let it_var env x = Id.List.assoc_opt x env |> Option.iter (unify (Id.typ x)) in
  it.var <- it_var;
  fun env t ->
    it.term env t;
    t

let inline_types_if : (type_decls -> term decl_item -> bool) -> term -> term decl_item list * term =
  let fld = Fold_tr.make () in
  fld.desc <-
    (fun (f, env, map) desc ->
      match desc with
      | Local (Decl_type decls, t) ->
          let decls1, decls2 = List.partition (f decls) decls in
          let map' = decls1 @ map in
          if decls1 = [] then
            let env' = decls @ env in
            fld.desc_rec (f, env', map') desc
          else
            let env' = decls1 @ env in
            let acc, { desc } =
              make_local (Decl_type decls2) t |> subst_tconstr_map decls1 |> fld.term (f, env', map')
            in
            (acc, desc)
      | _ -> fld.desc_rec (f, env, map) desc);
  fun f t ->
    let (_, _, map), t = fld.term (f, [], []) t in
    (map, t)

(** Inlining non recursive types *)
let inline_simple_types : term -> term decl_item list * term =
  let rec is_simple top decls (d, (_, ty)) =
    let aux ty = is_simple false decls (d, ([], ty)) in
    match ty with
    | TBase _ -> true
    | TFun (x, ty') -> aux (Id.typ x) && aux ty'
    | TTuple xs -> List.for_all (Id.typ |- aux) xs
    | TConstr (LId s, []) -> top || (not @@ List.mem_assoc s decls)
    | TConstr (LId s, tys) -> (not (List.mem_assoc s decls)) && List.for_all aux tys
    | TAttr (_, ty) -> aux ty
    | TVariant (_, rows) -> List.for_all (row_args |- List.for_all aux) rows
    | TModSig _ -> true
    | TModLid _ -> true
    | _ -> false
  in
  inline_types_if (is_simple true)

let inline_exn_type t : term =
  let _, t = inline_types_if (fun _ (s, _) -> C.is_exn (Type.LId s)) t in
  t

let set_length_typ : term -> term =
  let tr = Tr.make () in
  let tr_desc desc =
    match desc with
    | App ({ desc = Var x }, [ t ]) when is_length_var x -> (make_length @@ tr.term t).desc
    | _ -> tr.desc_rec desc
  in
  tr.desc <- tr_desc;
  tr.term

let split_mutual_rec : ?only_top:bool -> term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun only_top desc ->
      match desc with
      | Local (Decl_let (_ :: _ :: _ as bindings), t) ->
          let map =
            let rec aux bindings =
              match bindings with
              | [] -> []
              | (f, _) :: bindings' ->
                  let tys = List.map (fst |- Id.typ) bindings' in
                  let f' = f |> Id.new_var_id |> Id.map_typ (Ty.funs tys) in
                  (f, f') :: aux bindings'
            in
            aux bindings
          in
          let bindings' =
            if only_top then bindings else List.map (Pair.map_snd @@ tr.term only_top) bindings
          in
          let bindings'' =
            let rec aux acc bindings =
              match bindings with
              | [] -> acc
              | (f, t1) :: bindings' ->
                  let args = List.map fst bindings' in
                  let args' = List.map Id.new_var_id args in
                  let arg_map = List.combine args args' in
                  let f' = Id.List.assoc f map in
                  let t_f = Term.(var f' @ vars args) in
                  let t1' = t1 |> subst_map acc |> Term.(f |-> t_f) |> subst_var_map arg_map in
                  let acc' = (f, t_f) :: List.map (Pair.map_snd @@ subst f t_f) acc in
                  (f', make_funs args' t1') :: aux acc' bindings'
            in
            aux [] bindings'
          in
          (make_lets bindings'' @@ tr.term only_top t).desc
      | _ -> tr.desc_rec only_top desc);
  fun ?(only_top = false) t -> tr.term only_top t

let is_big_literal t : (id -> term) option =
  match t.desc with
  | Const (String s) when !Flag.Abstract.literal <= String.length s ->
      Some Term.var (* TODO: String.length ... = ... *)
  | Cons _ -> (
      match decomp_list t with
      | None -> None
      | Some ts ->
          if List.length ts >= !Flag.Abstract.literal && List.for_all has_safe_attr ts then
            let n = List.length ts in
            Some
              (fun r ->
                [%term
                  assume (length r = int n);
                  r])
          else None)
  | _ -> None

let abst_literal : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match is_big_literal t with
      | None -> tr.term_rec t
      | Some add_assume ->
          Flag.Abstract.over "literal";
          let t = make_rand_unit t.typ in
          let r = new_var_of_term t in
          Term.(let_ [ (r, t) ] (add_assume r)));
  fun t -> if !Flag.Abstract.literal < 0 then t else tr.term @@ reconstruct t

let encode_bool_as_int : term -> term =
  let tr = Tr.make () in
  tr.typ <- (fun typ -> if typ = Ty.bool then Ty.int else tr.typ_rec typ);
  let int_of_bool t = Term.(if_ t (int 1) (int 0)) in
  let bool_of_int t =
    match t.desc with
    | If (t1, { desc = Const (Int 1) }, { desc = Const (Int 0) }) -> t1
    | _ -> Term.(t <> int 0)
  in
  tr.desc <-
    (fun desc ->
      match desc with
      | Const True -> Const (Int 1)
      | Const False -> Const (Int 0)
      | Not t ->
          let t' = bool_of_int @@ tr.term t in
          Term.(int_of_bool (not t')).desc
      | BinOp (((And | Or) as op), t1, t2) ->
          let op' = match op with And -> Term.( && ) | Or -> Term.( || ) | _ -> assert false in
          let t1' = bool_of_int @@ tr.term t1 in
          let t2' = bool_of_int @@ tr.term t2 in
          (int_of_bool @@ op' t1' t2').desc
      | BinOp (Eq, t1, t2) when elim_tattr t1.typ = Ty.bool ->
          If
            ( bool_of_int @@ tr.term t1,
              bool_of_int @@ tr.term t2,
              Term.not (bool_of_int @@ tr.term t2) )
      | BinOp ((Eq | Lt | Gt | Leq | Geq), t1, _) ->
          if elim_tattr t1.typ <> Ty.int then [%unsupported];
          let desc' = tr.desc_rec desc in
          let t' = make desc' Ty.bool in
          (int_of_bool t').desc
      | If (t1, t2, t3) ->
          let t1' = tr.term t1 in
          let t2' = tr.term t2 in
          let t3' = tr.term t3 in
          Term.(if_ (bool_of_int t1') t2' t3').desc
      | _ -> tr.desc_rec desc);
  tr.term

(* only for closed terms *)
let remove_unambiguous_id : term -> term =
  let col = Col2.make [] ( @ ) in
  col.term <-
    (fun bv t ->
      match t.desc with
      | Var (LId x) ->
          let xs = List.filter (Id.eq x) bv in
          if List.length xs = 1 then xs else []
      | Var _ -> assert false
      | Fun (x, _) -> col.term_rec (x :: bv) t
      | Local (decl, t) ->
          let bv = get_bv_decl decl @@@ bv in
          col.decl bv decl @@@ col.term bv t
      | Match _ -> unsupported "Trans.remove_unambiguous_id: Match"
      | _ -> col.term_rec bv t);
  fun t ->
    let t = alpha_rename ~whole:true t in
    let xs = col.term [] t in
    map_var (fun x -> if Id.List.mem x xs then Id.set_id x 0 else x) t

let replace_typ_result_with_unit : term -> term =
  let tr = Tr.make () in
  tr.typ <- (fun typ -> if typ = typ_result then Ty.unit else tr.typ_rec typ);
  tr.term

let rename_for_ocaml : term -> term =
  let reserved =
    [
      "and";
      "as";
      "assert";
      "asr";
      "begin";
      "class";
      "constraint";
      "do";
      "done";
      "downto";
      "else";
      "end";
      "exception";
      "external";
      "false";
      "for";
      "fun";
      "function";
      "functor";
      "if";
      "in";
      "include";
      "inherit";
      "initializer";
      "land";
      "lazy";
      "let";
      "lor";
      "lsl";
      "lsr";
      "lxor";
      "match";
      "method";
      "mod";
      "module";
      "mutable";
      "new";
      "nonrec";
      "object";
      "of";
      "open";
      "or";
      "private";
      "rec";
      "sig";
      "struct";
      "then";
      "to";
      "true";
      "try";
      "type";
      "val";
      "virtual";
      "when";
      "while";
      "with";
    ]
  in
  let tr = Tr.make () in
  let tr_var x =
    let s = String.sign_to_letters @@ Id.name x in
    let s' =
      if Char.is_uppercase s.[0] then "_" ^ s
      else if List.mem (Id.to_string x) reserved then s ^ "_"
      else s
    in
    Id.set_name x s'
  in
  tr.var <- tr_var;
  tr.term

let remove_tattr : term -> term = { !!Tr.make with typ = elim_tattr_all }.term

let rec is_rand_unit' t =
  match t.desc with
  | Const Unit -> true
  | App ({ desc = Const (Rand (_, false)) }, [ { desc = Const Unit } ]) -> true
  | Tuple ts -> List.for_all is_rand_unit' ts
  | BinOp ((Eq | Lt | Gt | Leq | Geq), t1, t2) ->
      (is_rand_unit' t1 && has_safe_attr t2) || (is_rand_unit' t2 && has_safe_attr t1)
  | BinOp ((Add | Sub | Mult), t1, t2) ->
      (is_rand_unit' t1 && has_safe_attr t2) || (is_rand_unit' t2 && has_safe_attr t1)
  | BinOp (Div, t1, { desc = Const c }) when c <> Int 0 -> is_rand_unit' t1
  | If (t1, t2, t3) -> has_safe_attr t1 && is_rand_unit' t2 && is_rand_unit' t3
  | _ -> false

(** [reduce_rand t] reduces terms with [rand_unit] into more simple terms in [t].
    E.g., [%term randi + 1] is replaced with [%term randi] *)
let reduce_rand : ?annot:bool -> term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun ((rand_funs, annot) as arg) t ->
      match t.desc with
      | Local (Decl_let bindings, t) ->
          let bindings' = List.map (Pair.map_snd @@ tr.term arg) bindings in
          let rand_funs' =
            List.filter_map
              Option.(some_if (snd |- decomp_funs |- snd |- is_rand_unit') |- map fst)
              bindings'
          in
          let rand_funs'' = List.filter_out (Id.List.mem_assoc -$- bindings) rand_funs in
          let t' = tr.term (rand_funs' @@@ rand_funs'', annot) t in
          make_let bindings' t'
      | Fun (x, _) ->
          let rand_funs' = List.filter_out (Id.( = ) x) rand_funs in
          tr.term_rec (rand_funs', annot) t
      | _ -> (
          let t' = tr.term_rec arg t in
          match t'.desc with
          | _ when is_rand_unit' t' ->
              let t'' = Term.rand t.typ in
              if annot && not (same_term t t'') then add_attr (AInfo (Replaced t')) t'' else t''
          | App ({ desc = Var (LId f) }, ts)
            when Id.List.mem f rand_funs && List.for_all has_safe_attr ts ->
              Term.rand t.typ
          | If (t1, t2, { desc = Bottom }) when is_rand_unit' t1 -> t2
          | If (t1, t2, t3) when is_rand_unit' t1 && same_term t2 t3 -> t2
          | Local (Decl_let _, _) -> assert false
          | _ -> t'));
  fun ?(annot = false) t -> t |> reconstruct |> tr.term ([], annot) |> elim_unused_let ~annot

let reduce_ignore : term -> term =
  let tr = Tr2.make () in
  tr.term <-
    (fun ignore_funs t ->
      match t.desc with
      | Local (Decl_let bindings, t) ->
          let bindings' = List.map (Pair.map_snd @@ tr.term ignore_funs) bindings in
          let ignore_funs' =
            List.L.filter_map bindings' ~f:(fun (f, t) ->
                let xs, t1 = decomp_funs t in
                if t1.desc = Const Unit then Some (f, List.length xs) else None)
          in
          let t' = tr.term (ignore_funs' @ ignore_funs) t in
          make_let bindings' t'
      | _ -> (
          let t' = tr.term_rec ignore_funs t in
          match t'.desc with
          | App ({ desc = Var (LId f) }, ts)
            when Id.List.assoc_opt f ignore_funs |> Option.exists (( = ) (List.length ts)) ->
              List.fold_right make_seq ts unit_term
          | Local (Decl_let _, _) -> assert false
          | _ -> t'));
  tr.term [] |- elim_unused_let

let reduce_branch : term -> term =
  let tr = Tr.make () in
  let rec decomp_branch t =
    match t.desc with
    | If (t1, t2, t3) when is_randbool_unit t1 -> decomp_branch t2 @ decomp_branch t3
    | _ -> [ t ]
  in
  tr.term <-
    (fun t ->
      t
      |> tr.term_rec
      |> set_afv_shallowly
      |> decomp_branch
      |> List.classify ~eq:same_term
      |> List.map List.hd
      |> List.reduce_right make_br);
  tr.term

(* Add unique id to each "fail" *)
let mark_fail : term -> (int * Location.t option) list * term =
  let fld = Fold_tr.make () in
  fld.term <-
    (fun map t ->
      match t.desc with
      | App ({ desc = Event ("fail", false) }, [ { desc = Const Unit } ]) ->
          let loc = List.find_map_opt (function ALoc loc -> Some loc | _ -> None) t.attr in
          let c = List.length map in
          ((c, loc) :: map, add_attr (AId c) t)
      | Event ("fail", _) -> unsupported "mark_fail"
      | _ -> fld.term_rec map t);
  fld.term []

let split_assert t =
  if col_id t <> [] then [%unsupported];
  let t' = split_assert_and t in
  let map, t'' = mark_fail t' in
  List.rev_map (fun (id, loc) -> (replace_fail_with_bot ~except:[ id ] t'', loc)) map

let insert_extra_param t : term =
  t
  |> lift_fst_snd
  |> FpatInterface.insert_extra_param (* THERE IS A BUG in exception handling *)
  |@> Dbg.printf "insert_extra_param (%d added)::@. @[%a@.@."
        (List.length !Fpat.RefTypInfer.params)
        Print.term

(* input must be the whole program *)
let unify_pure_fun_app : term -> term =
  let tr = Tr.make () in
  let rec trans_apps ts =
    match ts with
    | [] -> []
    | t :: ts' ->
        let ts1, ts2 = List.partition (same_term t) ts' in
        (List.length ts1 + 1, t) :: trans_apps ts2
  in
  let collect_app =
    let col = Col.make [] ( @@@ ) in
    let filter bv apps =
      List.filter (get_fv |- List.Set.inter ~eq:Id.eq bv |- List.is_empty) apps
    in
    let col_term t =
      match t.desc with
      | App (_, ts) when has_pure_attr t -> t :: List.flatten_map col.term ts
      | Fun (x, t1) -> filter [ x ] @@ col.term t1
      | Match (t1, pats) ->
          let aux (p, t) = filter (get_bv_pat p) (col.pat p @@@ col.term t) in
          col.term t1 @@@ List.flatten_map aux pats
      | Local (Decl_let defs, t2) -> filter (List.map fst defs) @@ col.term t2
      | _ -> col.term_rec t
    in
    col.term <- col_term;
    col.term |- trans_apps
  in
  let unify t =
    let t' = tr.term t in
    let apps = collect_app t' in
    let aux (n, app) t =
      if n >= 2 then
        let x = new_var_of_term app in
        make_let [ (x, app) ] @@ subst_rev app x t
      else t
    in
    List.fold_right aux apps t'
  in
  tr.desc <-
    (fun desc ->
      match desc with
      | If (t1, t2, t3) -> If (tr.term t1, unify t2, unify t3)
      | Match (t, pats) -> Match (tr.term t, List.map (Pair.map_snd unify) pats)
      | Fun (x, t) -> Fun (x, unify t)
      | Local (Decl_let defs, t) -> Local (Decl_let (List.map (Pair.map_snd unify) defs), unify t)
      | _ -> tr.desc_rec desc);
  tr.term

let lift_assume : term -> term =
  let tr = Tr.make () in
  let collect_assume =
    let union = List.Set.union ~eq:same_term in
    let col = Col.make [] union in
    let col_term t =
      match t.desc with
      | If (t1, t2, { desc = Bottom }) -> union [ t1 ] (union (col.term t1) (col.term t2))
      | If (t1, _, _) | Match (t1, _) -> col.term t1
      | Fun _ -> []
      | Local (Decl_let defs, t') ->
          t' :: List.map snd defs
          |> List.map col.term
          |> List.reduce union
          |> List.filter_out (get_fv |- List.exists (Id.List.mem_assoc -$- defs))
      | _ -> col.term_rec t
    in
    col.term <- col_term;
    col.term
  in
  let remove_assume =
    let tr = Tr.make () in
    let tr_desc desc =
      match desc with If (_, t2, { desc = Bottom }) -> tr.desc t2.desc | _ -> tr.desc_rec desc
    in
    tr.desc <- tr_desc;
    tr.term
  in
  tr.desc <-
    (fun desc ->
      let lift ?fs t =
        let asms = t |> collect_assume |> List.map remove_assume in
        let asms' =
          match fs with
          | None -> asms
          | Some fs -> List.filter (get_fv |- List.exists (List.mem -$- fs)) asms
        in
        t |> tr.term |> List.fold_right Term.assume asms'
      in
      match desc with
      | If (_, t2, { desc = Bottom }) -> tr.desc t2.desc
      | If (t1, t2, t3) -> If (tr.term t1, lift t2, lift t3)
      | Match (t, pats) -> Match (tr.term t, List.map (Pair.map_snd lift) pats)
      | Fun (x, t) -> Fun (x, lift t)
      | Local (Decl_let defs, t) ->
          let fs = List.map fst defs in
          Local (Decl_let (List.map (Pair.map_snd tr.term) defs), lift ~fs t)
      | _ -> tr.desc_rec desc);
  tr.term

let elim_singleton_tuple : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Tuple [ t ] -> tr.desc t.desc
      | Proj (_, t) when tuple_num t.typ = Some 1 -> tr.desc t.desc
      | _ -> tr.desc_rec desc);
  tr.typ <- (fun typ -> match typ with TTuple [ x ] -> tr.typ @@ Id.typ x | _ -> tr.typ_rec typ);
  tr.pat <- (fun p -> match p.pat_desc with PTuple [ p ] -> tr.pat p | _ -> tr.pat_rec p);
  tr.term

(* Output: the direct ancestors of patters for constructors must be PAny or PVar wrapped with PWhen *)
let decompose_match : term -> term =
  let tr = Tr.make () in
  let decomp_var p =
    match p.pat_desc with
    | PVar x -> Some (x, Term.true_)
    | PWhen ({ pat_desc = PVar x }, cond) -> Some (x, cond)
    | _ -> None
  in
  let bind_id (_default, t) = t in
  let ( ++ ) bind1 bind2 (default, t) = bind1 (default, bind2 (default, t)) in
  let rec tr_pat_list ps =
    let aux p =
      match p.pat_desc with
      | PVar _ -> (p, bind_id)
      | _ ->
          let x = new_var_of_pattern p in
          let p', bind = tr_pat p in
          let cond = Term.(match_ (var x) [ (p', true_); (Pat.(__ p'.pat_typ), false_) ]) in
          let bind' (default, t) =
            Term.(match_ (var x) [ (p', bind (bot, t)); (Pat.(__ p'.pat_typ), default t.typ) ])
          in
          (Pat.(when_ (var x) cond), bind')
    in
    let ps', binds = List.split_map aux ps in
    (ps', List.fold_left ( ++ ) bind_id binds)
  and tr_pat p =
    match p.pat_desc with
    | PAny -> (p, bind_id)
    | PNondet -> assert false
    | PVar _ -> (p, bind_id)
    | PAlias (p1, x) ->
        let p1', bind = tr_pat p1 in
        let pat_desc = PAlias (p1', x) in
        (make_pattern pat_desc p.pat_typ, bind)
    | PConst c ->
        let x = new_var_of_term c in
        let c' = tr.term c in
        (Pat.(when_ (var x) Term.(var x = c')), bind_id)
    | PConstr (b, c, ps) ->
        let ps', bind = tr_pat_list ps in
        let pat_desc = PConstr (b, c, ps') in
        (make_pattern pat_desc p.pat_typ, bind)
    | PNil -> (p, bind_id)
    | PCons (p1, p2) ->
        let p1', p2', bind =
          match tr_pat_list [ p1; p2 ] with
          | [ p1'; p2' ], bind -> (p1', p2', bind)
          | _ -> assert false
        in
        let pat_desc = PCons (p1', p2') in
        (make_pattern pat_desc p.pat_typ, bind)
    | PTuple ps ->
        let ps', bind1 = tr_pat_list ps in
        let xs, conds = List.split_map (Option.get -| decomp_var) ps' in
        let x = new_var_of_pattern p in
        let bind2 = List.mapi (fun i y (_, t) -> Term.(let_s [ (y, proj i (var x)) ] t)) xs in
        let bind = List.fold_right ( ++ ) bind2 bind_id in
        let bind' = bind ++ bind1 in
        (Pat.(when_ (var x) Term.(bind ((fun _ -> false_), ands conds))), bind')
    | PRecord sps ->
        let ss, ps = List.split sps in
        let ps', bind = tr_pat_list ps in
        let sps' = List.combine ss ps' in
        let pat_desc = PRecord sps' in
        (make_pattern pat_desc p.pat_typ, bind)
    | PNone -> (p, bind_id)
    | PSome p1 ->
        let p1', bind = tr_pat p1 in
        let pat_desc = PSome p1' in
        (make_pattern pat_desc p.pat_typ, bind)
    | POr (p1, p2) -> (
        let p1', bind1 = tr_pat p1 in
        let p2', bind2 = tr_pat p2 in
        match (decomp_var p1', decomp_var p2') with
        | Some (x1, cond1), Some (x2, cond2) ->
            let bind = (fun (_, t) -> Term.(let_s [ (x2, var x1) ] t)) ++ bind1 ++ bind2 in
            (Pat.(when_ (var x1) (bind Term.((fun _ -> false_), cond1 || cond2))), bind)
        | _ ->
            let pat_desc = POr (p1', p2') in
            (make_pattern pat_desc p.pat_typ, bind1 ++ bind2))
    | PLazy p1 ->
        let p1', bind = tr_pat p1 in
        let pat_desc = PLazy p1' in
        (make_pattern pat_desc p.pat_typ, bind)
    | PWhen (p1, cond) ->
        let p1', bind = tr_pat p1 in
        let cond' = tr.term cond in
        (Pat.(when_ p1' (bind ((fun _ -> Term.false_), cond'))), bind)
    | PEval (_x, _t, _p) -> unsupported "decompose_match"
  in
  tr.desc <-
    (fun desc ->
      match desc with
      | Match (t1, pats) ->
          let x = new_var_of_term t1 in
          let pats' =
            List.L.map pats ~f:(fun (p, t) ->
                let p', bind = tr_pat p in
                (p', bind (Term.bot, tr.term t)))
          in
          let t1' = tr.term t1 in
          let t' = Term.(match_ t1' pats') in
          if Id.List.mem x @@ get_fv t' then Term.(let_ [ (x, t1') ] (match_ (var x) pats')).desc
          else t'.desc
      | _ -> tr.desc_rec desc);
  tr.term

let variant_args_to_tuple : ?do_decomp:bool -> term -> term =
  let fld = Fold_tr.make () in
  fld.desc <-
    (fun _ desc ->
      match desc with
      | Constr (b, s, ts) ->
          let _, ts' = List.split_map (fld.term []) ts in
          ([], Constr (b, s, [ Term.tuple ts' ]))
      | Match (t1, pats) ->
          let _, t1' = fld.term [] t1 in
          let pats' =
            let aux (p, t) =
              let bind, p' = fld.pat [] p in
              let _, t' = fld.term [] t in
              (p', make_lets_s bind t')
            in
            List.map aux pats
          in
          ([], Match (t1', pats'))
      | _ -> fld.desc_rec [] desc);
  fld.pat <-
    (fun bind p ->
      match p.pat_desc with
      | PConstr (b, LId s, ps) ->
          let _, pat_typ = fld.typ [] p.pat_typ in
          let binds, _ = List.split_map (fld.pat []) ps in
          let x =
            match pat_typ with
            | TVariant (_, rows) -> Id.new_var @@ List.get @@ row_args @@ assoc_row s rows
            | _ -> assert false
          in
          let bind =
            let aux i p =
              match p.pat_desc with
              | PVar y -> (y, [%term x##i])
              | _ -> invalid_arg "Trans.variant_args_to_tuple"
            in
            List.mapi aux ps
          in
          let pat_desc = PConstr (b, LId s, Pat.[ var x ]) in
          let pat_attr = [ PABV [ x ]; PAFV [] ] in
          (bind @ List.flatten binds, make_pattern pat_desc pat_typ ~attr:pat_attr)
      | PWhen (p, cond) ->
          let bind, p' = fld.pat [] p in
          let cond' = make_let_s bind cond in
          (bind, Pat.(when_ p' cond'))
      | _ -> fld.pat_rec bind p);
  fld.typ <-
    (fun _ ty ->
      match ty with
      | TVariant (b, rows) ->
          let tr = snd -| fld.typ [] in
          let rows' =
            rows
            |> List.map (fun row -> { row with row_args = [ Ty.tuple (List.map tr row.row_args) ] })
          in
          ([], TVariant (b, rows'))
      | _ -> fld.typ_rec [] ty);
  fun ?(do_decomp = true) t ->
    let t' = if do_decomp then decompose_match t else t in
    snd @@ fld.term [] t'

let remove_obstacle_type_attribute_for_pred_share : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Local (decl, t) ->
          let decl' =
            match decl with
            | Decl_let defs ->
                let aux (f, t) =
                  let f' = if is_fun_var f then f else tr.var f in
                  (f', tr.term t)
                in
                Decl_let (List.map aux defs)
            | _ -> decl
          in
          Local (decl', tr.term t)
      | _ -> tr.desc_rec desc);
  tr.typ <-
    (fun ty ->
      match ty with
      | TAttr (attr, ty') ->
          let attr' =
            List.filter
              (function
                | TAId (s, _) when s = label_pred_share -> false
                | TAPredShare _ -> false
                | _ -> true)
              attr
          in
          _TAttr attr' @@ tr.typ ty'
      | _ -> tr.typ_rec ty);
  tr.term

let alpha_rename_if : (id -> bool) -> term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun check desc ->
      let new_id x = if check x then Id.new_var_id x else x in
      let desc' = tr.desc_rec check desc in
      match desc' with
      | Local (Decl_let bindings, t1) ->
          let map = List.map (fun (f, _) -> (f, new_id f)) bindings in
          let map' = Fmap.(list (snd _LId)) map |> IdMap.of_list in
          let bindings' =
            List.map2 (fun (_, t) (_, f') -> (f', subst_var_map_without_typ map' t)) bindings map
          in
          Local (Decl_let bindings', subst_var_map_without_typ map' t1)
      | Fun (x, t1) ->
          let x' = new_id x in
          Fun (x', subst_var_without_typ x (LId x') t1)
      | Match (t1, pats) ->
          let aux (p, t2) =
            let map = List.map (Pair.add_right new_id) @@ List.unique ~eq:Id.eq @@ get_bv_pat p in
            let map' = Fmap.(list (snd _LId)) map |> IdMap.of_list in
            (rename_pat map p, subst_var_map_without_typ map' t2)
          in
          Match (t1, List.map aux pats)
      | _ -> desc');
  tr.term

(* TODO: refactor *)

(** The input must be in CPS *)
let add_occurence_param : term -> term =
  let fld = Fold_tr.make () in
  let gen x env =
    try Id.List.assoc_map x succ env |> Pair.swap with Not_found -> ((x, 1) :: env, 0)
  in
  fld.term <-
    (fun env t0 ->
      match t0.desc with
      | Fun _ ->
          let xs, t' = decomp_funs t0 in
          let env, xs' = Fold_tr.list ~f:fld.var ~acc:env xs in
          let env, t'' = fld.term env t' in
          let y = Id.new_var Ty.int in
          (env, Term.funs (y :: xs') t'')
      | App ({ desc = Const (Rand (ty, _)) }, [ { desc = Const Unit }; { desc = Var (LId k) } ]) ->
          let env, ty' = fld.typ env ty in
          let env, x = gen k env in
          let env, k' = fld.var env k in
          (env, Term.(make_rand_cps ty' @ [ unit; var k' @ [ int x ] ]))
      | App ({ desc = Const (Rand (ty, _)) }, [ { desc = Const Unit }; { desc = Fun (x, t) } ]) ->
          let env, ty' = fld.typ env ty in
          let env, t' = fld.term env t in
          let env, x' = fld.var env x in
          (env, Term.(make_rand_cps ty' @ [ unit; fun_ x' t' ]))
      | App ({ desc = Const (Rand _) }, _) -> assert false
      | App ({ desc = Event (s, _) }, [ { desc = Const Unit }; { desc = Fun (x, t) } ]) ->
          let env, t' = fld.term env t in
          let env, x' = fld.var env x in
          (env, Term.(make_event_cps s @ [ unit; fun_ x' t' ]))
      | App ({ desc = Event _ }, _) -> assert false
      | App ({ desc = Var (LId f) }, ts) ->
          let env, f' = fld.var env f in
          let env, x = gen f env in
          let env, ts' = Fold_tr.list ~f:fld.term ~acc:env ts in
          (env, Term.(var f' @ (int x :: ts')))
      | App (({ desc = Fun _ } as t1), ts) ->
          let env, t1' = fld.term env t1 in
          let env, ts' = Fold_tr.list ~f:fld.term ~acc:env ts in
          (env, Term.(t1' @ (int 0 :: ts')))
      | _ -> fld.term_rec env t0);
  fld.typ <-
    (fun env ty ->
      match ty with
      | TFun _ ->
          let xs, ty' = decomp_tfun ty in
          let env, xs' = Fold_tr.list ~f:fld.var ~acc:env xs in
          let x = Id.new_var Ty.int in
          let env, ty'' = fld.typ env ty' in
          (env, List.fold_right _TFun (x :: xs') ty'')
      | ty -> fld.typ_rec env ty);
  snd -| fld.term [] -| eta_normal

let map_typ : (typ -> typ) -> term -> term =
  let tr = Tr2.make () in
  tr.typ <- ( @@ );
  tr.term

let split_by_ref_type env t =
  if env = [] then invalid_arg "Trans.split_by_ref_type";
  let make acc_rev t = acc_rev |> List.fold_left (Fun.flip Term.local) t |> copy_tvar |> snd in
  let rec aux env acc_rev t =
    let have defs (f, _) = Id.List.mem_assoc f defs in
    match t.desc with
    | Local ((Decl_let defs as decl), t1) when List.exists (have defs) env -> (
        let f_env, env' = List.partition (have defs) env in
        match f_env with
        | [] -> assert false
        | [ (f, ty) ] ->
            let acc_rev' = decl :: acc_rev in
            (Some (f, ty), make acc_rev' Term.eod) :: aux env' acc_rev t1
        | _ -> unsupported "split_by_ref_type")
    | Local (decl, t1) -> aux env (decl :: acc_rev) t1
    | _ ->
        let t' = make acc_rev t in
        let t'' =
          if !Flag.Method.verify_ref_interface then
            if env <> [] then
              failwith "%a not found (unused functions are removed)" (print_list Print.id ",")
                (List.map fst env)
            else replace_fail_with_bot t'
          else t'
        in
        [ (None, t'') ]
  in
  aux env [] t

let rename_target_ext_funs map =
  let assoc x loc =
    let s_loc = Format.asprintf "%a" Print.location loc in
    List.find_map_opt
      (fun (y, (s, y')) -> if Id.(x = y) && String.exists s_loc s then Some y' else None)
      map
  in
  let f t =
    match t.desc with
    | Var (LId x) ->
        t.attr
        |> List.find_map_opt (function ALoc loc -> Some loc | _ -> None)
        |> Option.bind -$- assoc x
        |> Option.map Term.var
    | _ -> None
  in
  trans_if f

let set_assert_ref_typ ?catch_all x ty t =
  let catch_all = Option.default_delayed (fun () -> make_catch_all t) catch_all in
  let tys, ty' = Ref_type.decomp_funs ty in
  let r = Id.new_var ~name:"r" @@ Ref_type.to_simple ty' in
  let t_check = match ty' with Ref_type.Base (_, y, p) -> subst_var y r p | _ -> Term.true_ in
  let xs =
    let make = Id.new_var ~name:"arg" -| Ref_type.to_simple ~with_pred:true in
    List.map (snd |- make) tys
  in
  let t_check' = List.fold_right2 (subst_var -| fst) tys xs t_check in
  let term =
    let t_app = Term.(catch_all (var x @ vars xs)) in
    let main =
      [%term
        let r = `t_app in
        assert `t_check']
    in
    let rec aux t =
      match t.desc with
      | Local (Decl_let bindings, t2) ->
          let t2' = if Id.List.mem_assoc x bindings then main else aux t2 in
          make_let bindings t2'
      | Local (Decl_type decls, t2) -> make_let_type decls @@ aux t2
      | _ -> assert false
    in
    aux t
  in
  let env =
    let aux x (y, ty) acc = (x, ty) :: List.map (Pair.map_snd @@ Ref_type.subst_var y x) acc in
    List.fold_right2 aux xs tys []
  in
  (env, term)

let update_attr = AInfo (String "ref_update")

let infer_ref_update : term -> term =
  let trc = Tr_col2.make false ( || ) in
  trc.term <-
    (fun () t ->
      let update, desc = trc.desc_rec () t.desc in
      let update, desc =
        match desc with
        | Fun _ -> (false, desc)
        | App _ -> (true, desc)
        | Ref _ -> (true, desc)
        | SetRef _ -> (true, desc)
        | _ -> (update, desc)
      in
      let attr = if update then update_attr :: t.attr else t.attr in
      (update, make desc t.typ ~attr));
  trc.term () |- snd

(** Replace dereference with the previous result.
    E.g. [let n = !r + 1 in !r + n] => [let v_r = !r in let n = v_r + 1 in v_r + n]
    Update is checked by [update_attr].
*)
let merge_deref : term -> term option =
  let has_update t = List.mem update_attr t.attr in
  let rec decomp t =
    match t.desc with
    | Local (Decl_let [ (x, ({ desc = Deref { desc = Var (LId r) } } as t1)) ], t2) ->
        let refs', t2' = decomp t2 in
        ((x, r, t1) :: refs', t2')
    | _ -> ([], t)
  in
  let pp_ref fm (x, r, t) = Format.fprintf fm "(%a, %a, %a)" Print.id x Print.id r Print.term t in
  let _pp_refs = Print.list pp_ref in
  let let_refs refs t = Term.lets (List.map Triple.take13 refs) t in
  let ( ++ ) refs1 refs2 =
    let aux (x, r, t) acc =
      let acc' =
        List.map (fun (x', r', t') -> (x', r', if Id.(r = r') then Term.var x else t')) acc
      in
      (x, r, t) :: acc'
    in
    List.fold_right aux refs1 refs2
  in
  let tr_list_focus focus tr_list xs =
    let ctxs, ts = List.split_map focus xs in
    let defs, ts', rs = tr_list ts in
    (defs, List.map2 ( @@ ) ctxs ts', rs)
  in
  let rec tr_aux update t =
    let t' = tr t in
    if update then ([], t', true)
    else
      let refs, t'' = decomp t' in
      (refs, t'', has_update t)
  and tr_list_left ?(update = false) ts =
    let aux (refs_rev, ts_rev, update) t =
      let refs, t', update' = tr_aux update t in
      (List.rev refs ++ refs_rev, t' :: ts_rev, update')
    in
    let refs_rev, ts_rev, rs = List.fold_left aux ([], [], update) ts in
    (List.rev refs_rev, List.rev ts_rev, rs)
  and tr_list_right ?(update = false) ts =
    let aux t (refs_acc, ts_acc, update) =
      let refs, t', update' = tr_aux update t in
      (refs ++ refs_acc, t' :: ts_acc, update')
    in
    List.fold_right aux ts ([], [], update)
  and tr_list left_to_right = if left_to_right then tr_list_left else tr_list_right
  and tr t =
    let refs, desc =
      match t.desc with
      | End_of_definitions | Const _ | Event _ | Nil | Bottom | TNone | Var _ -> ([], t.desc)
      | Fun (x, t1) ->
          (* can improve *)
          ([], Fun (x, tr t1))
      | App (t1, ts) ->
          let refs, (t1', ts') =
            let refs, ts, _ = tr_list Flag.EvalStrategy.app_left_to_right (t1 :: ts) in
            (refs, List.decomp_cons ts)
          in
          (refs, App (t1', ts'))
      | If (t1, t2, t3) ->
          let refs1, t1', update = tr_aux false t1 in
          let refs2, t2', _ = tr_aux update t2 in
          let refs3, t3', _ = tr_aux update t3 in
          let refs = refs1 ++ refs2 ++ refs3 in
          (refs, If (t1', t2', t3'))
      | Local (Decl_let defs, t2) ->
          let refs1, defs', rs = tr_list_focus Focus.snd (tr_list true) defs in
          let refs2, t2', _ = tr_aux rs t2 in
          let refs = refs1 ++ refs2 in
          (refs, Local (Decl_let defs', t2'))
      | Local (decl, t2) ->
          (* can improve *)
          ([], Local (decl, tr t2))
      | BinOp (op, t1, t2) ->
          let refs, t1', t2' =
            match tr_list Flag.EvalStrategy.binop_left_to_right [ t1; t2 ] with
            | refs, [ t1'; t2' ], _ -> (refs, t1', t2')
            | _ -> assert false
          in
          (refs, BinOp (op, t1', t2'))
      | Not t1 ->
          let refs, t1', _ = tr_aux false t1 in
          (refs, Not t1')
      | Record fields ->
          let refs, fields', _ = tr_list_focus Focus.snd (tr_list true) fields in
          (refs, Record fields')
      | Field (t1, s) ->
          let refs, t1', _ = tr_aux false t1 in
          (refs, Field (t1', s))
      | SetField (t1, s, t2) ->
          let refs, t1', t2' =
            match tr_list Flag.EvalStrategy.setfield_left_to_right [ t1; t2 ] with
            | refs, [ t1'; t2' ], _ -> (refs, t1', t2')
            | _ -> assert false
          in
          (refs, SetField (t1', s, t2'))
      | Cons (t1, t2) ->
          let refs, t1', t2' =
            match tr_list Flag.EvalStrategy.constr_left_to_right [ t1; t2 ] with
            | refs, [ t1'; t2' ], _ -> (refs, t1', t2')
            | _ -> assert false
          in
          (refs, Cons (t1', t2'))
      | Constr (b, s, ts) ->
          let refs, ts', _ = tr_list Flag.EvalStrategy.constr_left_to_right ts in
          (refs, Constr (b, s, ts'))
      | Match (t1, pats) ->
          let refs1, t1', update = tr_aux false t1 in
          let aux (p, t) (refs_acc, pats_acc) =
            (match p.pat_desc with PWhen _ -> unsupported "" | _ -> ());
            let refs, t', _ = tr_aux update t in
            let bv = get_bv_pat p in
            let refs1, refs2 = List.partition (Triple.snd |- Id.List.mem -$- bv) refs in
            let t'' = let_refs refs1 t' in
            (refs2 ++ refs_acc, (p, t'') :: pats_acc)
          in
          let refs, pats' = List.fold_right aux pats ([], []) in
          (refs1 ++ refs, Match (t1', pats'))
      | Raise t1 ->
          let refs, t1', _ = tr_aux false t1 in
          (refs, Raise t1')
      | TryWith (t1, t2) ->
          let refs, t1', t2' =
            match tr_list true [ t1; t2 ] with
            | refs, [ t1'; t2' ], _ -> (refs, t1', t2')
            | _ -> assert false
          in
          (refs, TryWith (t1', t2'))
      | Tuple ts ->
          let refs, ts', _ = tr_list Flag.EvalStrategy.tuple_left_to_right ts in
          (refs, Tuple ts')
      | Proj (i, t1) ->
          let refs, t1', _ = tr_aux false t1 in
          (refs, Proj (i, t1'))
      | Ref t1 ->
          let refs, t1', _ = tr_aux false t1 in
          (refs, Ref t1')
      | Deref { desc = Var (LId r) } ->
          let x =
            let name = "v_" ^ Id.name r in
            Id.new_var ~name t.typ
          in
          ([ (x, r, [%term !r]) ], Var (LId x))
      | Deref t1 ->
          let refs, t1', _ = tr_aux false t1 in
          (refs, Deref t1')
      | SetRef (t1, t2) ->
          let refs, t1', t2' =
            match tr_list Flag.EvalStrategy.setref_left_to_right [ t1; t2 ] with
            | refs, [ t1'; t2' ], _ -> (refs, t1', t2')
            | _ -> assert false
          in
          (refs, SetRef (t1', t2'))
      | TSome t1 ->
          let refs, t1', _ = tr_aux false t1 in
          (refs, TSome t1')
      | Lazy t1 ->
          let refs, t1', _ = tr_aux false t1 in
          (refs, Lazy t1')
      | Module _ -> [%unsupported]
      | MemSet (t1, t2) ->
          let refs, t1', t2' =
            match tr_list true [ t1; t2 ] with
            | refs, [ t1'; t2' ], _ -> (refs, t1', t2')
            | _ -> assert false
          in
          (refs, MemSet (t1', t2'))
      | AddSet (t1, t2) ->
          let refs, t1', t2' =
            match tr_list true [ t1; t2 ] with
            | refs, [ t1'; t2' ], _ -> (refs, t1', t2')
            | _ -> assert false
          in
          (refs, AddSet (t1', t2'))
      | Subset (t1, t2) ->
          let refs, t1', t2' =
            match tr_list true [ t1; t2 ] with
            | refs, [ t1'; t2' ], _ -> (refs, t1', t2')
            | _ -> assert false
          in
          (refs, Subset (t1', t2'))
      | Pack _ -> assert false
      | Unpack _ -> assert false
      | Forall _ -> [%unsupported]
      | Exists _ -> [%unsupported]
    in
    let attr = List.remove t.attr update_attr in
    let_refs refs (make desc t.typ ~attr)
  in
  fun t ->
    try t |> alpha_rename |> infer_ref_update |> tr |> inline_var |> set_afv |> Option.some
    with Unsupported _ -> None

let abstract_exn : term -> term =
  let used = ref [] in
  let tr = Tr2.make () in
  let is_exn_ty (ty_exn, _, _) ty = ty = ty_exn || ty = Ty.exn in
  tr.term <-
    (fun ((_, target, _) as env) t ->
      let t' = tr.term_rec env t in
      match t'.desc with
      | Constr (false, s, ts) when is_exn_ty env t.typ ->
          (* TODO: fix for the terms with side-effects *)
          let name = Path.name s in
          let b = List.mem name target in
          if b then used := name :: !used;
          Term.(seqs ts (bool b))
      | Match (t1, pats) ->
          let pats_old = match t.desc with Match (_, pats) -> pats | _ -> assert false in
          let pats' =
            let aux (p1, _) (p2, t) =
              let make x =
                let ty = tr.typ env @@ Id.typ x in
                (Id.set_typ x ty, make_rand_unit ty)
              in
              let bindings =
                let ( - ) = List.Set.diff ~eq:Id.eq in
                get_bv_pat p1 - get_bv_pat p2 |> List.map make
              in
              (p2, make_lets_s bindings t)
            in
            List.map2 aux pats_old pats
          in
          let desc = Match (t1, pats') in
          make desc t'.typ
      | _ -> t');
  tr.typ <- (fun env ty -> if is_exn_ty env ty then Ty.bool else tr.typ_rec env ty);
  tr.pat <-
    (fun ((_, target, non_target) as env) p ->
      let p' = tr.pat_rec env p in
      if is_exn_ty env p.pat_typ then
        if target = [] then Pat.nondet p'.pat_typ
        else
          let rec match_any p =
            match p.pat_desc with
            | PVar _ -> true
            | PAny -> true
            | PAlias (p, _) -> match_any p
            | _ -> false
          in
          match p.pat_desc with
          | PConstr (_, s, ps) when List.for_all match_any ps ->
              let b = Id.new_var ~name:"b" Ty.bool in
              let name = Path.name s in
              if List.mem name target then
                if [ name ] = target then Pat.(const Term.true_)
                else Pat.(when_ (var b) Term.(if_ (not (var b)) false_ randb))
              else if [ name ] = non_target then Pat.(const Term.false_)
              else Pat.(when_ (var b) Term.(if_ (var b) false_ randb))
          | _ -> Pat.nondet p'.pat_typ
      else p');
  fun t ->
    used := [];
    match find_exn_typ t with
    | None -> t
    | Some ty_exn ->
        let target = !Flag.Method.target_exn in
        let non_target =
          let constrs =
            match ty_exn with
            | TVariant (_, rows) -> List.map (row_constr |- Id.name) rows
            | _ -> assert false
          in
          List.Set.diff constrs target
        in
        let t' = tr.term (ty_exn, target, non_target) t in
        if List.Set.(target - !used <> []) then
          failwith "Unused target: %a@." (print_list Format.pp_print_string ", ") target;
        t'

(* Make top definitions not to have side-effects *)
let top_def_to_funs t : term =
  let t = split_let t in
  let decls, body = decomp_decls t in
  let has_effect decl =
    match decl with
    | Decl_let [ (x, t) ] when not (has_no_effect t) ->
        assert (not (Id.List.mem x (get_fv t)));
        let x' = Id.new_var ~name:(Id.name x) Ty.(fun_ unit (Id.typ x)) in
        Some (decl, (x, x', t))
    | Decl_let defs ->
        if List.exists (not -| has_no_effect -| snd) defs then
          unsupported
            "Trans.top_def_to_funs (there may exist side-effect on some 'let ... and ...' \
             introduced by a prepprocess?)";
        None
    | _ -> None
  in
  let map = List.filter_map has_effect decls in
  if map = [] then t
  else
    let body' =
      let defs =
        List.map (fun (_, (x, x', _)) -> (Id.new_var_id x, Term.(var x' @ [ unit ]))) map
      in
      let main = Id.new_var ~name:"main" body.typ in
      Term.(let_ [ (main, lets defs body) ] (var main))
    in
    let aux decl t =
      match List.assoc_opt decl map with
      | None -> Term.(local decl t)
      | Some (x, x', tx) ->
          let tx' =
            let u = Id.new_var ~name:"u" Ty.unit in
            Term.(fun_ u tx)
          in
          let t' = subst x Term.(var x' @ [ unit ]) t in
          let decl' = Decl_let [ (x', tx') ] in
          Term.(local decl' t')
    in
    List.fold_right aux decls body'

let set_to_primitive : term -> term =
  let tr = Tr2.make () in
  let make_is_set_op sm to_s x =
    List.exists (fun (m, _) -> Id.is_in_module_string ~m (to_s x)) sm
  in
  tr.desc <-
    (fun set_modules desc ->
      let is_set_op = make_is_set_op set_modules Lid.to_string in
      let name = Lid.last in
      match desc with
      | Var x when is_set_op x -> ( match name x with "empty" -> Const Empty | _ -> Var x)
      | App (({ desc = Var x } as tx), [ t1 ]) when is_set_op x -> (
          let t1' = tr.term set_modules t1 in
          match name x with "singleton" -> AddSet (t1', Term.empty t1.typ) | _ -> App (tx, [ t1' ]))
      | App (({ desc = Var x } as tx), [ t1; t2 ]) when is_set_op x -> (
          let t1' = tr.term set_modules t1 in
          let t2' = tr.term set_modules t2 in
          match name x with
          | "mem" -> MemSet (t1', t2')
          | "add" -> AddSet (t1', t2')
          | "subset" -> Subset (t1', t2')
          | _ -> App (tx, [ t1'; t2' ]))
      | Local ((Decl_let [ (m, { desc = App ({ desc = Var make }, [ elt ]) }) ] as decl), t)
        when Lid.name make = "Stdlib.Set.Make" ->
          let set_modules' =
            let _, (_, ty) =
              match elt.typ with
              | TModSig sgn ->
                  sgn |> sig_types |> List.find_map (List.find_opt (fst |- Id.name |- ( = ) "t"))
              | _ -> assert false
            in
            (m, ty) :: set_modules
          in
          let t' = tr.term set_modules' t in
          Local (decl, t')
      | _ -> tr.desc_rec set_modules desc);
  tr.typ <-
    (fun set_modules ty ->
      match ty with
      | TConstr (s, _) when make_is_set_op set_modules Path.to_string s ->
          let _, ty =
            List.find (fun (m, _) -> Id.is_in_module_string ~m @@ Path.to_string s) set_modules
          in
          Ty.set ty
      | _ -> tr.typ_rec set_modules ty);
  tr.term []

let abst_div : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | BinOp (Div, t1, t2) ->
          let x = new_var_of_term t1 in
          let y = new_var_of_term t2 in
          let q = Id.new_var ~name:"q" Ty.int in
          let r = Id.new_var ~name:"r" Ty.int in
          let t_abs =
            let z = Id.new_var ~name:"z" Ty.int in
            let z_ = Term.var z in
            Term.(fun_ z (if_ (z_ >= int 0) z_ ~-z_))
          in
          let abs = Id.new_var ~name:"abs" t_abs.typ in
          let x_ = Term.var x in
          let q_ = Term.var q in
          let y_ = Term.var y in
          let r_ = Term.var r in
          let abs_ = Term.var abs in
          Term.(
            lets
              [ (abs, t_abs); (x, t1); (y, t2); (q, randi); (r, randi) ]
              (assume (x_ = (q_ * y_) + r_ && abs_ @ [ r_ ] < abs_ @ [ y_ ]) (var q)))
      (*
    | BinOp(Div, t1, t2) ->
        let x = new_var_of_term t1 in
        let y = new_var_of_term t2 in
        let r = Id.new_var ~name:"r" Ty.int in
        let div = Id.new_var ~name:"div" Ty.(funs [int; int] int) ~attr:[External] in
        let t = Term.(var div @ [var x; var y]) in
        Term.(lets [x,t1; y,t2; r,t]
              (assume (if_ (var x >= int 0 && var y >= int 0 || var x <= int 0 && var y <= int 0) (var r >= int 0) (var r <= int 0))
               (var r)))
 *)
      | _ -> set_afv_shallowly @@ tr.term_rec t);
  tr.term

let remove_peval : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Match (t, pats) ->
          let t' = tr.term t in
          let pats' =
            let rec tr_pat p =
              let tr_pat_list tr ps =
                let bind, ps' = List.split_map tr ps in
                (List.flatten bind, ps')
              in
              let bind, pat_desc =
                match p.pat_desc with
                | PAny | PNondet | PVar _ | PNil | PNone -> ([], p.pat_desc)
                | PAlias (p, x) ->
                    let bind, p' = tr_pat p in
                    (bind, PAlias (p', x))
                | PConst t -> ([], PConst (tr.term t))
                | PConstr (b, s, ps) ->
                    let bind, ps' = tr_pat_list tr_pat ps in
                    (bind, PConstr (b, s, ps'))
                | PCons (p1, p2) ->
                    let bind1, p1' = tr_pat p1 in
                    let bind2, p2' = tr_pat p2 in
                    (bind1 @ bind2, PCons (p1', p2'))
                | PTuple ps ->
                    let bind, ps' = tr_pat_list tr_pat ps in
                    (bind, PTuple ps')
                | PRecord fields ->
                    let bind, fields' = tr_pat_list Focus.(apply snd tr_pat snd) fields in
                    (bind, PRecord fields')
                | PSome p ->
                    let bind, p' = tr_pat p in
                    (bind, PSome p')
                | POr (p1, p2) ->
                    let bind1, p1' = tr_pat p1 in
                    let bind2, p2' = tr_pat p2 in
                    assert (List.Set.eq ~eq:Id.eq (get_bv_pat p1') (get_bv_pat p2'));
                    (bind1 @ bind2, POr (p1', p2'))
                | PLazy p ->
                    let bind, p' = tr_pat p in
                    (bind, PLazy p')
                | PWhen (p, t) ->
                    let bind, p' = tr_pat p in
                    (bind, PWhen (p', tr.term t))
                | PEval (x, t, p) ->
                    let p' = tr.pat p in
                    let t' = tr.term t in
                    let bind =
                      let bv = get_bv_pat p in
                      if bv = [] then []
                      else
                        let t'' = Term.match_ t' [ (p', Term.(tuple (vars bv))) ] in
                        let y = Id.new_var t''.typ in
                        (y, t'') :: List.mapi (fun i z -> (z, [%term y##i])) bv
                    in
                    let p'' =
                      let cond =
                        Term.(match_ t' [ (p', Term.true_); (Pat.__ p.pat_typ, Term.false_) ])
                      in
                      PWhen (Pat.var x, cond)
                    in
                    (bind, p'')
              in
              (bind, make_pattern pat_desc p.pat_typ)
            in
            pats
            |> List.map (fun (p, t) ->
                   let bind, p' = tr_pat p in
                   (p', Term.lets bind @@ tr.term t))
          in
          Match (t', pats')
      | _ -> tr.desc_rec desc);
  tr.term

let get_tconstr, get_tconstr_typ =
  let col = Col.make [] ( @@@ ) in
  col.typ <-
    (fun ty ->
      match ty with
      | TConstr (s, tys) -> (s, tys) :: List.rev_map_flatten col.typ tys
      | _ -> col.typ_rec ty);
  col.term <-
    (fun t ->
      let r1 = col.typ t.typ in
      let r2 = col.desc t.desc in
      r1 @@@ r2);
  (col.term, col.typ)

(** Assume the input is in the image of [copy_poly_funs].
    TODO: Labels of variants and fields of records could be non-unique *)
let copy_poly_type t =
  (* Decompose t into type declarations and the othe part *)
  let declss, body =
    try split_type_decl_and_body ~force:true t
    with Invalid_argument _ -> invalid_arg "Trans.copy_poly_type"
  in
  let decls = List.concat declss in
  (* [extract [] (s,tys)] returns all [TConstr(s',tys')] used in [TConstr(s,tys)] *)
  let eq = Eq.(id * list can_unify) in
  let rec extract acc ((s : tconstr), tys) =
    let tys = List.map flatten_tvar_typ tys in
    if List.mem ~eq (s, tys) acc then acc
    else
      let acc' = (s, tys) :: acc in
      match Id.List.assoc_opt s decls with
      | None -> acc'
      | Some pty -> (
          try
            apply_tconstr pty tys
            |> get_tconstr_typ
            |> List.map (Pair.map_fst Path.id_of)
            |> extract_list acc'
          with
          | Invalid_argument _
          when List.exists
                 (function TConstr (LId c, []) -> (Id.name c).[0] = '$' | _ -> false)
                 tys
          ->
            assert (List.compare_lengths (fst pty) tys < 0);
            unsupported "Existential types in GADT (%a)" Print.tconstr s)
  and extract_list acc tconstrs = List.fold_left extract acc tconstrs in
  let tconstrs : (tconstr * typ list) list =
    body
    |> make_let_type (List.filter (snd |- fst |- ( = ) []) decls)
    |@> instansiate_tvar Ty.unit
    |> get_tconstr
    |> List.map (Pair.map_fst Path.id_of)
    |> List.unique ~eq
    |> extract_list []
    |> List.filter_out (fst |- Type._LId |- List.mem ~eq:Path.eq -$- C.prims)
  in
  (* Replacing all type variables with unit *)
  let normalize = List.map (fun ty -> if is_tvar ty then Ty.unit else flatten ty) in
  let fresh x tcs = gen_fresh_name_var_int (List.map snd tcs) x in
  let name_map =
    tconstrs
    |> List.filter_map (fun ((s : tconstr), tys) ->
           if tys = [] || is_prim_constr (LId s) then None
           else
             let name = List.map to_id_string tys @ [ string_of_tconstr s ] |> String.join "_" in
             let name =
               if String.length name < Flag.long_name_len then name
               else List.map to_id_string_short tys @ [ string_of_tconstr s ] |> String.join "_"
             in
             let name =
               if String.length name < Flag.long_name_len then name else string_of_tconstr s
             in
             let s' = tconstr_of_string name in
             let tys' = normalize tys in
             Some ((s, tys'), s'))
    |> List.fold_left (fun map_rev (stys, s') -> (stys, fresh s' map_rev) :: map_rev) []
    |> List.rev
  in
  let sbst, sbst_typ =
    let tr = Tr.make () in
    let tr_typ ty =
      match ty with
      | TConstr (LId s, tys) -> (
          match List.assoc_opt ~eq (s, normalize tys) name_map with
          | None -> tr.typ_rec ty
          | Some s' -> TConstr (LId s', []))
      | _ -> tr.typ_rec ty
    in
    tr.typ <- tr_typ;
    (tr.term, tr.typ)
  in
  let decls =
    let aux (s, (params, ty)) =
      let stys =
        if params = [] then [ (s, ty) ]
        else
          name_map
          |> List.filter (fst |- fst |- Id.( = ) s)
          |> List.map (fun ((_, tys), s) -> (s, apply_tconstr (params, ty) tys))
      in
      List.map (fun (s, ty) -> (s, ([], sbst_typ ty))) stys
    in
    List.flatten_map (List.concat_map aux) declss
  in
  make_let_type decls (sbst body) |> split_type_decls

let inline_type_alias : term -> term =
  let tr = Tr2.make () in
  let is_alias (_, (params, ty)) =
    match ty with
    | TConstr (_, params') ->
        assert (
          List.L.for_all params' ~f:(function
            | TVar (_, r, _) ->
                List.L.exists params ~f:(function TVar (_, r', _) -> r == r' | _ -> false)
            | _ -> true));
        true
    | TBase _ -> true
    | _ -> false
  in
  tr.term <-
    (fun env t ->
      match t.desc with
      | Local (Decl_type decls, t1) when List.exists is_alias decls ->
          let aliases, decls' = List.partition is_alias decls in
          tr.term (aliases @@@ env) (make_let_type decls' t1)
      | _ -> tr.term_rec env t);
  tr.typ <-
    (fun env ty ->
      match ty with
      | TConstr (LId s, tys) when Id.List.mem_assoc s env ->
          let params, ty' = Id.List.assoc s env in
          if TConstr (LId s, params) = ty' then (* WORKAROUND: Is this still necessary? *)
            ty
          else
            let tys' = List.map (tr.typ env) tys in
            let ty'' = apply_tconstr (params, ty') tys' in
            tr.typ env ty''
      | TModSig _ | TModLid _ ->
          Flag.Print.signature := true;
          Format.eprintf "ty: %a@." Print.typ ty;
          assert false (* modules and functors must be removed in advance *)
      | _ -> tr.typ_rec env ty);
  tr.term []

let inline_ext_rebind : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | Local (Type_ext (Ext_rebind (s, LId s')), t1) ->
          t1 |> subst_tconstr_label_map [ (s, s') ] |> subst_constr (LId s) (LId s') |> tr.term
      | Local ((Type_ext (Ext_rebind _) as decl), _) ->
          Format.eprintf "t: %a@." Print.decls [ decl ];
          invalid_arg "%s" __FUNCTION__
      | _ -> tr.term_rec t);
  tr.term

(* TODO: detect Obj.magic by using its type 'a -> 'b *)
let abst_magic : term -> term =
  let tr = Tr.make () in
  tr.term <-
    (fun t ->
      match t.desc with
      | App ({ desc = Var x }, ts)
        when List.mem (Lid.name x) [ "Stdlib.Obj.magic"; "Stdlib__Obj.magic" ] ->
          let ts = List.map tr.term ts in
          Term.(seqs ts (rand t.typ))
      | _ -> set_afv_shallowly @@ tr.term_rec t);
  tr.typ <- Fun.id;
  tr.attr <- Fun.id;
  tr.term

let remove_unused_palias : term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun _ desc ->
      match desc with
      | Match (t, pats) ->
          let pats' =
            List.L.map pats ~f:(fun (p, t) ->
                let used = get_fv t in
                (tr.pat used p, tr.term [] t))
          in
          let t' = tr.term [] t in
          Match (t', pats')
      | _ -> tr.desc_rec [] desc);
  tr.pat <-
    (fun used p ->
      match p.pat_desc with
      | PAlias (p, x) when not (Id.List.mem x used) -> tr.pat used p
      | _ -> tr.pat_rec used p);
  tr.typ <- (fun _ ty -> ty);
  tr.attr <- (fun _ attr -> attr);
  tr.term []

let remove_dummy : term -> term =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match desc with
      | Const (Dummy ty) -> (
          match (make_default_term ty).desc with Const (Dummy _) -> [%unsupported] | desc -> desc)
      | _ -> tr.desc_rec desc);
  tr.typ <- Fun.id;
  tr.attr <- Fun.id;
  tr.term

(* TODO: not to copy case bodies *)
let remove_por : term -> term =
  let tr = Tr.make () in
  let rec expand_list ps = ps |> List.map expand |> Combination.take_each
  and expand p : pattern list =
    let open Nondet in
    match p.pat_desc with
    | PAny | PNondet | PVar _ | PConst _ | PNil | PNone -> [ p ]
    | PAlias (p, x) ->
        let* p' = expand p in
        return @@ make_palias p' x
    | PConstr (b, c, ps) ->
        let* ps' = expand_list ps in
        return @@ make_pattern (PConstr (b, c, ps')) p.pat_typ
    | PCons (p1, p2) ->
        let* p1' = expand p1 in
        let* p2' = expand p2 in
        return @@ make_pcons p1' p2'
    | PTuple ps ->
        let* ps' = expand_list ps in
        return @@ make_ptuple ps'
    | PRecord records ->
        let aux (label, p) =
          let* p' = expand p in
          return (label, p')
        in
        let* records' = records |> List.map aux |> Combination.take_each in
        return @@ make_pattern (PRecord records') p.pat_typ
    | PSome p ->
        let* p' = expand p in
        return @@ make_psome p'
    | POr (p1, p2) -> expand p1 @ expand p2
    | PWhen (p, t) ->
        let* p' = expand p in
        return @@ make_pwhen p' t
    | PLazy p ->
        let* p' = expand p in
        return @@ make_plazy p'
    | PEval (x, t, p) ->
        let* p' = expand p in
        return @@ make_peval x t p'
  in
  tr.desc <-
    (fun desc ->
      match desc with
      | Match (t1, pats) ->
          let t1' = tr.term t1 in
          let pats' =
            pats
            |> List.flatten_map (fun (p, t) -> expand p |> List.map (Pair.pair -$- t))
            |> List.map (Pair.map tr.pat tr.term)
          in
          Match (t1', pats')
      | _ -> tr.desc_rec desc);
  tr.term <- set_afv_shallowly -| tr.term_rec;
  tr.typ <- Fun.id;
  tr.attr <- Fun.id;
  tr.term

(* Unused (buggy?) *)
let instansiate_matched_poly : term -> unit =
  let it = Iter.make () in
  it.desc <-
    (fun desc ->
      match desc with
      | Match (t, pats) when is_tvar @@ flatten t.typ ->
          unify t.typ (fst (List.hd pats)).pat_typ;
          it.term t;
          List.iter (Pair.iter it.pat it.term) pats
      | _ -> it.desc_rec desc);
  it.term

let remove_unused_rec_type : term -> term =
  let tr = Tr.make () in
  tr.typ <-
    (fun ty ->
      match ty with
      | TAttr (attrs, ty) when List.exists (function TARec _ -> true | _ -> false) attrs ->
          let attrs', ty' =
            List.L.fold_left attrs
              ~init:([], tr.typ ty)
              ~f:(fun (acc, ty) attr ->
                match attr with
                | TARec (_, r, _) when not (occurs r ty) -> (acc, ty)
                | _ -> (attr :: acc, ty))
          in
          _TAttr attrs' ty'
      | _ -> tr.typ_rec ty);
  tr.term

let abst_poly_variant : term -> term =
  let tr = Tr2.make () in
  tr.desc <-
    (fun env desc ->
      match desc with
      | Constr (true, LId c, ts) ->
          Flag.Abstract.over "polymorphic variant";
          let ts = List.map (tr.term env) ts in
          Id.List.assoc c env |> Term.int |> List.fold_right make_use ts |> Syntax.desc
      | Match _ ->
          trans_match_with_recover_pat_bv_desc ~tr_desc_rec:(tr.desc_rec env) ~tr_typ:(tr.typ env)
            desc
      | _ -> tr.desc_rec env desc);
  tr.term <- set_afv_shallowly --| tr.term_rec;
  tr.pat <-
    (fun env p ->
      match p.pat_desc with
      | PConstr (true, LId c, ps) ->
          let p = Pat.int (Id.List.assoc c env) in
          if ps = [] then p else Pat.when_ p Term.randb
      | _ -> tr.pat_rec env p);
  tr.typ <- (fun env ty -> match ty with TVariant (VPoly _, _) -> Ty.int | _ -> tr.typ_rec env ty);
  fun t ->
    let env = t |> col_poly_constr |> List.mapi Pair.pair_rev in
    tr.term env t |> remove_unused_rec_type

let remove_tpoly : term -> term =
  let tr = Tr.make () in
  tr.typ <- (fun ty -> match ty with TPoly (_, ty) -> tr.typ ty | _ -> tr.typ_rec ty);
  tr.decl <-
    (fun decl ->
      match decl with
      | Decl_let defs ->
          let defs =
            defs
            |> List.map (fun (x, t) ->
                   let x' = tr.var x in
                   let t' = tr.term t in
                   if Is'._TPoly (Id.typ x) then unify (Id.typ x') t'.typ;
                   (x', t'))
          in
          Decl_let defs
      | _ -> tr.decl_rec decl);
  tr.term

exception CannotMakeTerm (* WORKAROUND: we must use type environments *)

let rec col_alias force name_por fv p =
  let col = col_alias force name_por fv in
  let col_list ps =
    let bindss, ps', ts = List.split3 @@ List.map col ps in
    (List.flatten bindss, ps', ts)
  in
  let find ?(fv = fv) x = List.find_default x (Id.eq x) fv in
  let must_bind ?(fv = fv) x =
    match find ~fv x with
    | x' -> not (Type.equal (Id.typ x) (Id.typ x'))
    | exception Not_found -> false
  in
  let binds, pat_desc, t =
    match p.pat_desc with
    | PAny ->
        let x = Id.new_var ~name:"u" p.pat_typ in
        ([], PVar x, Term.var x)
    | PNondet -> [%invalid_arg]
    | PVar x -> ([], PVar x, Term.var x)
    | PAlias (p, x) when force || must_bind x ->
        let binds, p', t = col_alias force true fv p in
        let x' = find x in
        let t' = Syntax.set_typ t (Id.typ x') in
        ((x', t') :: binds, PAlias (p', x), t')
    | PAlias (p, x) -> (
        try
          let binds, p', _ = col p in
          (binds, PAlias (p', x), Term.var x)
        with CannotMakeTerm -> ([], PAlias (p, x), Term.var x))
    | PConst t -> ([], PConst t, t)
    | PConstr (poly, c, ps) ->
        let binds, ps', ts = col_list ps in
        (binds, PConstr (poly, c, ps'), Term.constr ~poly c ts p.pat_typ)
    | PNil -> ([], PNil, Term.nil2 ~list_typ:p.pat_typ)
    | PCons (p1, p2) ->
        let binds1, p1', t1 = col p1 in
        let binds2, p2', t2 = col p2 in
        (binds1 @@@ binds2, PCons (p1', p2'), Term.cons t1 t2)
    | PTuple ps ->
        let binds, ps', ts = col_list ps in
        (binds, PTuple ps', Term.tuple ts)
    | PRecord fields ->
        let fields =
          let rest =
            try
              ValE'._TRecord p.pat_typ
              |> List.filter_map (fun (label, (_, ty)) ->
                     if Id.List.mem_assoc label fields then None
                     else
                       let x = Id.new_var ~name:(Id.name label) ty in
                       Some (label, Pat.var x))
            with Invalid_argument _ -> raise CannotMakeTerm
          in
          fields @ rest
        in
        let bindss, pfields', ts =
          fields
          |> List.map (fun (label, p) ->
                 let binds, p', t = col p in
                 (binds, (label, p'), t))
          |> List.split3
        in
        let binds = List.flatten bindss in
        let fields' = List.map2 (Pair.pair -| fst) fields ts in
        (binds, PRecord pfields', Term.record fields' p.pat_typ)
    | PNone -> ([], PNone, Term.none2 ~opt_typ:p.pat_typ)
    | PSome p ->
        let binds, p', t = col p in
        (binds, PSome p', Term.some t)
    | POr (p1, p2) ->
        let binds1, p1', _ = col p1 in
        let binds2, p2', _ = col p2 in
        let binds = binds1 @@@ binds2 in
        let desc = POr (p1', p2') in
        let p' = set_pat_desc p desc in
        if name_por then
          let x = new_var_of_pattern p in
          (binds, PAlias (p', x), Term.var x)
        else (binds, desc, Term.dummy p.pat_typ (* term must not be used *))
    | PWhen (p, cond) ->
        let p', cond' = make_bind_for_PAlias_aux force name_por (p, cond) in
        let binds, p'', t = col p' in
        (binds, PWhen (p'', cond'), t)
    | PLazy p ->
        let binds, p', t = col p in
        (binds, PLazy p', Term.lazy_ t)
    | PEval _ -> [%invalid_arg]
  in
  (binds, set_pat_desc p pat_desc, t)

and make_bind_for_PAlias_aux force name_por (p, t) =
  try
    let binds, p', _ = col_alias force name_por (get_fv t) p in
    (p', Term.local (Decl_let binds) t)
  with CannotMakeTerm -> (p, t)

let make_bind_for_PAlias =
  let tr = Tr2.make () in
  tr.desc <-
    (fun force t ->
      match t with
      | Match (t, pats) ->
          let t' = tr.term force t in
          let pats' =
            pats
            |> Fmap.(list (snd (tr.term force)))
            |> List.map (make_bind_for_PAlias_aux force false)
          in
          Match (t', pats')
      | desc -> tr.desc_rec force desc);
  tr.term <- set_afv_shallowly --| tr.term_rec;
  tr.typ <- (fun _ ty -> ty);
  tr.attr <- (fun _ attr -> attr);
  fun ?(force = false) ->
    remove_pnondet |- remove_peval |- remove_unused_palias |- tr.term force |- remove_unused_palias

let add_def_of_free_types t =
  let decls : type_decl list =
    get_free_types t
    |> List.map (fun (c, n) ->
           (tconstr_of_string (Path.to_string c), (List.init n (fun _ -> Type.new_tvar ()), Ty.abst)))
  in
  make_lets_type decls t

let inline_tvar =
  let tr = Tr2.make () in
  let is_tvar (_, (params, ty)) =
    match (params, ty) with [], TVar (_, { contents = None }, _) -> true | _ -> false
  in
  tr.term <-
    (fun env t ->
      match t.desc with
      | Local (Decl_type decls, t1) when List.exists is_tvar decls ->
          let tvars, decls' = List.partition is_tvar decls in
          let env' = List.map (fun (c, (_, ty)) -> (c, ty)) tvars @@@ env in
          tr.term env' (make_let_type decls' t1)
      | _ -> tr.term_rec env t);
  tr.typ <-
    (fun env ty ->
      match ty with
      | TConstr (LId s, []) when Id.List.mem_assoc s env -> Id.List.assoc s env
      | TModSig _ | TModLid _ ->
          Flag.Print.signature := true;
          Format.eprintf "ty: %a@." Print.typ ty;
          assert false (* modules and functors must be removed in advance *)
      | _ -> tr.typ_rec env ty);
  tr.term []

let reduce_trivial_branch =
  let tr = Tr2.make () in
  tr.desc <-
    (fun conds desc ->
      match desc with
      | If (t1, t2, _) when List.exists (same_term t1) conds -> tr.desc conds t2.desc
      | If (t1, _, t3) when List.exists (same_term (Term.not t1)) conds -> tr.desc conds t3.desc
      | If (t1, t2, t3) when has_pure_attr t1 ->
          let t1' = tr.term conds t1 in
          let t2' = tr.term (t1 :: conds) t2 in
          let t3' = tr.term (Term.not t1 :: conds) t3 in
          If (t1', t2', t3')
      | _ -> tr.desc_rec conds desc);
  tr.term <- set_afv_shallowly --| tr.term_rec;
  tr.term []

let abst_menhir : term -> term =
  let tr = Tr.make () in
  let is_menhir_fun (f, t) =
    let xs, _ = decomp_funs t in
    String.exists (Id.name f) "_menhir_"
    && List.exists (fun x -> String.exists (Id.name x) "_menhir_stack") xs
  in
  tr.decl <-
    (fun decl ->
      match decl with
      | Decl_let defs ->
          defs
          |> List.map (fun (f, t) ->
                 let t' =
                   if is_menhir_fun (f, t) then
                     let () = Flag.Abstract.over "polymorphic variant" in
                     if has_fail t then
                       let xs, t' = decomp_funs t in
                       Term.funs xs Term.(seq fail (bot t'.typ))
                     else Term.rand ~use:false t.typ
                   else tr.term t
                 in
                 (f, t'))
          |> _Decl_let
      | _ -> tr.decl_rec decl);
  tr.term <- set_afv_shallowly -| tr.term_rec;
  tr.term |- elim_unused_let ~leave_last:true

let add_ref_check =
  let tr = Tr2.make () in
  tr.term <-
    (fun env t ->
      match t.desc with
      | Var (LId x) when List.mem ATarget t.attr ->
          let rty = Id.List.assoc x env in
          let s = Format.asprintf "%a : %a@." Print.id x Ref_type.print rty in
          let annot = add_attr (AInfo (Inserted s)) in
          let t' = map_attr (List.remove_all -$- ATarget) t in
          Ref_type_gen.add_assert_assume ~annot true t' rty
      | Var _ -> t
      | _ -> tr.term_rec env t);
  tr.term

(* Module not supported *)
let remove_unused_exception =
  let tr = Tr2.make () in
  tr.desc <-
    (fun used desc ->
      match desc with
      | Local (Type_ext (Ext_type (_, (_, { ext_row_path }))), t)
        when not (List.mem ~eq:Path.eq ext_row_path used) ->
          (tr.term used t).desc
      | _ -> tr.desc_rec used desc);
  fun t ->
    let used = col_constr_path_in_term t in
    tr.term used t

(* Module not supported *)
let remove_unused_type_decl =
  let ( ++ ) = Path.Set.union in
  let tc = Tr_col2.make Path.Set.empty ( ++ ) in
  tc.term <-
    (fun () t ->
      let used1, _ = tc.typ () t.typ in
      match t.desc with
      | Local (Decl_type decls, t) ->
          let used2, t' = tc.term () t in
          let used12 = used1 ++ used2 in
          let decls' =
            let update (used, xs) =
              let used', xs' =
                List.L.fold_left_map xs ~init:used ~f:(fun used ((b, cs, ((c, _) as decl)) as x) ->
                    if b then (cs ++ used, x) else (used, (Path.Set.mem (Type.LId c) used, cs, decl)))
              in
              (not (Path.Set.equal used used'), (used', xs'))
            in
            let init ((c, (_, ty)) as decl) =
              (Path.Set.mem (Type.LId c) used12, col_used_path ty, decl)
            in
            fixed_point_update update (used12, List.map init decls)
            |> snd
            |> List.filter_map (fun (b, _, decl) -> if b then Some decl else None)
          in
          let used3, _ = tc.decl () (Decl_type decls') in
          (used3 ++ used12, Term.type_ decls' t')
      | _ ->
          let used, desc = tc.desc () t.desc in
          (used, make desc t.typ ~attr:t.attr));
  tc.typ <-
    (fun () ty ->
      match ty with
      | TConstr (s, tys) ->
          let useds, tys' = List.split_map (tc.typ ()) tys in
          (Path.Set.add s @@ List.fold_left Path.Set.union Path.Set.empty useds, TConstr (s, tys'))
      | _ -> tc.typ_rec () ty);
  tc.term () |- snd

let rec has_fun_neg visited tenv ty =
  let neg = has_fun_neg visited tenv in
  let pos = has_fun_pos visited tenv in
  match ty with
  | TBase _ -> false
  | TVar (_, { contents = None }, _) -> false
  | TVar (_, { contents = Some ty }, _) -> neg ty
  | TFun (x, ty') -> pos (Id.typ x) || neg ty'
  | TFuns _ -> assert false
  | TTuple xs -> List.exists (Id.typ |- neg) xs
  | TVariant (_, rows) -> List.exists (fun { row_args } -> List.exists neg row_args) rows
  | TRecord fields -> List.exists (snd |- snd |- neg) fields
  | TConstr (c, tys) ->
      if List.mem ~eq:Path.eq c visited then false
      else if is_prim_constr c then
        (* Assuming that primitive types have only covariant arguments *)
        List.exists neg tys
      else has_fun_pos (c :: visited) tenv (apply_tconstr (Tenv.assoc_type c tenv) tys)
  | TAttr (_, ty) -> neg ty
  | TModSig _ -> assert false
  | TModLid _ -> assert false
  | TPackage _ -> assert false
  | TPoly (_, _) -> assert false
  | TConstraint (_, _) -> assert false
  | TOpen -> assert false

and has_fun_pos visited tenv ty =
  let pos = has_fun_pos visited tenv in
  match ty with
  | TBase _ -> false
  | TVar (_, { contents = None }, _) -> false
  | TVar (_, { contents = Some ty }, _) -> pos ty
  | TFun _ -> true
  | TFuns _ -> assert false
  | TTuple xs -> List.exists (Id.typ |- pos) xs
  | TVariant (_, rows) -> List.exists (fun { row_args } -> List.exists pos row_args) rows
  | TRecord fields -> List.exists (snd |- snd |- pos) fields
  | TConstr (c, tys) -> (
      if List.mem ~eq:Path.eq c visited then false
      else if is_prim_constr c then
        (* Assuming that primitive types have only covariant arguments *)
        List.exists pos tys
      else
        try has_fun_pos (c :: visited) tenv (apply_tconstr (Tenv.assoc_type c tenv) tys)
        with Not_found ->
          Format.eprintf "c: %a@." Path.print c;
          assert false)
  | TAttr (_, ty) -> pos ty
  | TModSig _ -> assert false
  | TModLid _ -> assert false
  | TPackage _ -> assert false
  | TPoly (_, _) -> assert false
  | TConstraint (_, _) -> assert false
  | TOpen -> assert false

let has_fun_pos = has_fun_pos []
let has_fun_neg = has_fun_neg []

(** [reduce_external fs t] reduces "f x y z" to "rand ty"
    if [f] is a fail-free external function and not in [fs] *)
let reduce_external =
  let tr = Tr2.make () in
  tr.desc <-
    (fun ((fs, tenv) as env) desc ->
      match desc with
      | App ({ desc = Var (LId f) }, ts)
        when Id.is_external f
             && arg_num (Id.typ f) = List.length ts
             && (not (Id.List.mem f fs))
             && not (has_fun_neg tenv (Id.typ f)) ->
          let map = if Flag.EvalStrategy.app_left_to_right then List.map else List.rev_map in
          let defs = map (tr.term env |- Pair.add_left new_var_of_term) ts in
          let t = Term.rand ~expand:false (snd @@ decomp_tfun @@ Id.typ f) in
          (Term.lets_s defs t).desc
      | Local (Decl_type decls, t) ->
          let tenv' = Tenv.add_typ_decl decls tenv in
          let t' = tr.term (fs, tenv') t in
          Local (Decl_type decls, t')
      | _ -> tr.desc_rec env desc);
  fun fs t -> inline_var t |> tr.term (fs, !!Tenv.init) |> reconstruct

let merge_branch =
  let tr = Tr.make () in
  tr.desc <-
    (fun desc ->
      match tr.desc_rec desc with
      | If (t1, t2, { desc = If (t31, t32, t33) }) when same_term t2 t32 ->
          If (Term.(t1 || t31), t2, t33)
      | If (t1, { desc = If (t21, t22, t23) }, t3) when same_term t23 t3 ->
          If (Term.(t1 && t21), t22, t3)
      | desc -> desc);
  tr.typ <- Fun.id;
  tr.term
