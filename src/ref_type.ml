open Util
module S = Syntax
module SU = Term_util
module T = Type
module TU = Type_util

module Debug = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

type t =
  | Var of S.term T.tvar
  | Base of T.base * S.id * S.term
  | Fun of S.id * t * t
  | Tuple of (S.id * t) list
  | Inter of S.typ * t list
  | Union of S.typ * t list
  | ExtArg of S.id * t * t
  | List of S.id * S.term * S.id * S.term * t (* List(len,p_len,i,p_i,typ) *)
  | Constr of T.path * t list * S.id * S.term
  | Variant of (T.constr * t list) list
  | Record of (T.label * (T.mutable_flag * t)) list
  | Exn of t * t
    (* [Exn(ty1,ty2)] is a type of terms that return the values of type [ty1]
       or raise an exception of type [ty2] *)
[@@deriving show]

let typ_module = Constr (T.prim_path "sig", [], Id.new_var TU.Ty.unit, SU.true_term)
let typ_result = Constr (T.prim_path "X", [], Id.new_var TU.Ty.unit, SU.true_term)
let _Inter styp typs = Inter (styp, typs)
let _Union styp typs = Union (styp, typs)
let _ExtArg x typ1 typ2 = ExtArg (x, typ1, typ2)
let top styp = Inter (styp, [])
let bottom styp = Union (styp, [])

let make_trans ?(tr = S.Tr.id) f =
  let tr_term = tr.term in
  let tr_var = tr.var in
  let rec trans ty =
    match f trans ty with
    | None -> (
        match ty with
        | Var s -> Var s
        | Base (base, y, p) -> Base (base, tr_var y, tr_term p)
        | Constr (c, tys, y, p) -> Constr (c, List.map trans tys, tr_var y, tr_term p)
        | Fun (y, typ1, typ2) -> Fun (tr_var y, trans typ1, trans typ2)
        | Tuple xtyps -> Tuple (List.map (Pair.map_snd @@ trans) xtyps)
        | Inter (typ, typs) -> Inter (typ, List.map trans typs)
        | Union (typ, typs) -> Union (typ, List.map trans typs)
        | ExtArg (y, typ1, typ2) -> ExtArg (y, trans typ1, trans typ2)
        | List (y, p_len, z, p_i, typ) ->
            List (tr_var y, tr.term p_len, tr_var z, tr.term p_i, trans typ)
        | Variant labels -> Variant (List.map (Pair.map_snd @@ List.map trans) labels)
        | Record fields -> Record (List.map (Pair.map_snd @@ Pair.map_snd trans) fields)
        | Exn (typ1, typ2) -> Exn (trans typ1, trans typ2))
    | Some ty -> ty
  in
  trans

let make_col f empty ( ++ ) =
  let col_list cl xs = List.fold_left (fun acc x -> cl x ++ acc) empty xs in
  let rec col ty =
    match f col ty with
    | None -> (
        match ty with
        | Var _ -> empty
        | Base _ -> empty
        | Fun (_, ty1, ty2) -> col ty1 ++ col ty2
        | Tuple xtys -> col_list (snd |- col) xtys
        | Inter (_, tys) -> col_list col tys
        | Union (_, tys) -> col_list col tys
        | ExtArg (_, ty1, ty2) -> col ty1 ++ col ty2
        | List (_, _, _, _, ty1) -> col ty1
        | Constr (_, tys, _, _) -> col_list col tys
        | Variant labels -> col_list (snd |- col_list col) labels
        | Record fields -> col_list (snd |- snd |- col) fields
        | Exn (ty1, ty2) -> col ty1 ++ col ty2)
    | Some acc -> acc
  in
  col

let decomp_base typ = match typ with Base (base, x, t) -> Some (base, x, t) | _ -> None
let decomp_fun typ = match typ with Fun (x, typ1, typ2) -> Some (x, typ1, typ2) | _ -> None

let decomp_list typ =
  match typ with List (x, p_len, y, p_i, typ2) -> Some (x, p_len, y, p_i, typ2) | _ -> None

let rec decomp_inter typ =
  match typ with Inter (_, typs) -> List.flatten_map decomp_inter typs | _ -> [ typ ]

let rec decomp_union typ =
  match typ with Inter (_, typs) -> List.flatten_map decomp_union typs | _ -> [ typ ]

let is_base = Option.is_some -| decomp_base
let is_fun = Option.is_some -| decomp_fun
let is_list = Option.is_some -| decomp_list

let is_bottom typ =
  match typ with
  | Union (_, []) -> true
  | Base (_, _, { S.desc = Const False }) -> true
  | _ -> false

let is_top typ = match typ with Inter (_, []) -> true | _ -> false

let rec is_bottom' typ =
  match typ with
  | Union (_, []) -> true
  | Base (_, _, { S.desc = Const False }) -> true
  | Fun (_, typ1, typ2) -> is_top typ1 && is_bottom' typ2
  | Tuple xtyps -> List.exists (snd |- is_bottom') xtyps
  | _ -> false

and is_top' typ =
  match typ with
  | Inter (_, []) -> true
  | Base (_, _, { S.desc = S.Const S.True }) -> true
  | Fun (_, typ1, _) -> is_bottom typ1
  | _ -> false

let rec occur x ty =
  let f = occur x in
  match ty with
  | Var _ -> false
  | Base (_, _, p) -> List.exists (Id.same x) @@ S.get_fv p
  | Fun (y, typ1, typ2) -> (Id.(x <> y) && f typ1) || f typ2
  | Tuple xtyps -> List.exists (fun (y, ty) -> Id.(x <> y) && f ty) xtyps
  | Inter (_, typs) | Union (_, typs) -> List.exists f typs
  | ExtArg (_, typ1, typ2) -> f typ1 || f typ2
  | List (_, p_len, _, p_i, typ) ->
      let aux = Id.List.mem x -| S.get_fv in
      aux p_len || aux p_i || f typ
  | Variant labels -> List.exists (snd |- List.exists f) labels
  | Record fields -> List.exists (snd |- snd |- f) fields
  | Constr (_, tys, _, p) -> List.exists f tys || (List.exists (Id.same x) @@ S.get_fv p)
  | Exn (typ1, typ2) -> f typ1 || f typ2

let rec decomp_funs typ =
  match typ with
  | Fun (_, _, Exn _) -> ([], typ)
  | Fun (x, typ1, typ2) ->
      let xtys, typ' = decomp_funs typ2 in
      ((x, typ1) :: xtys, typ')
  | _ -> ([], typ)

let rec print is_arg fm ty =
  let pr = print is_arg in
  match ty with
  | Var s -> Format.fprintf fm "%a" Print.typ (T.TVar s)
  | Base (base, _, p) when p = SU.true_term -> Format.fprintf fm "%a" Print_typ.base base
  | Base (T.TBool, x, p) when SU.make_var x = p -> Format.fprintf fm "{true}"
  | Base (T.TBool, x, p) when SU.make_not (SU.make_var x) = p -> Format.fprintf fm "{false}"
  | Base (_, x, { desc = BinOp (Eq, { desc = Var y }, t) }) when S.LId x = y ->
      Format.fprintf fm "{%a}" Print.term t
  | Base (_, x, { desc = BinOp (Eq, t, { desc = Var y }) }) when S.LId x = y ->
      Format.fprintf fm "{%a}" Print.term t
  | Base (_, _, p) when p.desc = Const False -> Format.fprintf fm "Bot"
  | Base (base, x, p) ->
      Format.fprintf fm "@[{%a:%a |@ %a}@]" Id.print x Print_typ.base base Print.term p
  | Constr (s, [], _, p) when p.desc = Const True -> Format.fprintf fm "%a" Print_typ.path s
  | Constr (s, [], x, p) ->
      Format.fprintf fm "@[{%a:%a |@ %a}@]" Id.print x Print_typ.path s Print.term p
  | Constr (constr, tys, _, p) when p.desc = Const True ->
      let s1, s2 = if is_arg then ("", "") else ("(", ")") in
      Format.fprintf fm "%s@[%a %s@]%s" s1
        (print_list (print true) ",")
        tys (TU.string_of_path constr) s2
  | Constr (constr, tys, x, p) ->
      Format.fprintf fm "@[{%a:%a %s |@ %a}@]" Id.print x
        (print_list (print true) ",")
        tys (TU.string_of_path constr) Print.term p
  | Fun (x, typ1, Exn (typ2, typ3)) when is_bottom typ3 -> pr fm (Fun (x, typ1, typ2))
  | Fun (x, typ1, Exn (typ2, typ3)) ->
      let arg = if occur x typ2 || occur x typ3 then Format.asprintf "%a:" Id.print x else "" in
      Format.fprintf fm "(@[<hov 2>%s%a ->^[%a]@ %a@])" arg pr typ1 pr typ3 pr typ2
  | Fun _ as typ ->
      let rec aux fm (xtyps, typ) =
        match xtyps with
        | [] -> pr fm typ
        | (x, typ1) :: xtyps' ->
            if List.exists (occur x) @@ (typ :: List.map snd xtyps') then
              Format.fprintf fm "@[<hov 2>%a:%a ->@ %a@]" Id.print x pr typ1 aux (xtyps', typ)
            else Format.fprintf fm "@[<hov 2>%a ->@ %a@]" pr typ1 aux (xtyps', typ)
      in
      Format.fprintf fm "(%a)" aux @@ decomp_funs typ
  | Tuple xtys ->
      let rec aux xtys =
        match xtys with
        | [] -> ()
        | [ (_, ty) ] -> pr fm ty
        | (x, ty) :: xtys' ->
            if occur x @@ Tuple xtys' then Format.fprintf fm "%a:" Id.print x;
            Format.fprintf fm "%a *@ " pr ty;
            aux xtys'
      in
      Format.fprintf fm "(@[";
      aux xtys;
      Format.fprintf fm "@])"
  | Inter (styp, []) when !!Debug.check -> Format.fprintf fm "Top(%a)" Print.typ styp
  | Inter (_, []) -> Format.fprintf fm "Top"
  | Inter (_, [ typ ]) -> pr fm typ
  | Inter (_, typs) -> Format.fprintf fm "(@[%a@])" (print_list pr " /\\@ ") typs
  | Union (styp, []) when !!Debug.check -> Format.fprintf fm "Bot(%a)" Print.typ styp
  | Union (_, []) -> Format.fprintf fm "Bot"
  | Union (_, [ typ ]) -> pr fm typ
  | Union (_, typs) -> Format.fprintf fm "(@[%a@])" (print_list pr " \\/@ ") typs
  | ExtArg (x, typ1, typ2) -> Format.fprintf fm "(@[%a where %a:%a@])" pr typ2 Id.print x pr typ1
  | List (x, p_len, y, p_i, typ2) ->
      let s1, s2 = if is_arg then ("", "") else ("(", ")") in
      Format.fprintf fm "%s@[" s1;
      if p_i = SU.true_term then
        if occur y typ2 then Format.fprintf fm "[%a]%a " Id.print y pr typ2
        else Format.fprintf fm "%a " (print true) typ2
      else Format.fprintf fm "[%a: %a]%a " Id.print y Print.term p_i pr typ2;
      if p_len <> SU.true_term then Format.fprintf fm "|%a: %a|" Id.print x Print.term p_len
      else if List.exists (Id.same x) (S.get_fv p_i) || occur x typ2 then
        Format.fprintf fm "|%a|" Id.print x;
      Format.fprintf fm "list@]%s" s2
  | Variant labels ->
      let pr fm (s, typs) =
        if typs = [] then Format.fprintf fm "%a" Print_typ.constr s
        else Format.fprintf fm "@[%a of %a@]" Print_typ.constr s (print_list pr "@ *@ ") typs
      in
      Format.fprintf fm "(@[%a@])" (print_list pr "@ | ") labels
  | Record fields ->
      let pr' fm (s, (f, typ)) =
        let sf = if f = T.Mutable then "mutable " else "" in
        Format.fprintf fm "@[%s%a: %a@]" sf Print_typ.label s pr typ
      in
      Format.fprintf fm "{@[%a@]}" (print_list pr' ";@ ") fields
  | Exn (typ1, typ2) ->
      if is_bottom typ2 then pr fm typ1
      else Format.fprintf fm "(@[<hov 2>%a@ |^[%a]@])" pr typ1 pr typ2

let print = print false

let rec decomp_funs_n n typ =
  match typ with
  | Fun _ when n <= 0 -> ([], [], typ)
  | Fun (x, typ1, typ2) ->
      let exts, typs, typ' = decomp_funs_n (n - 1) typ2 in
      (exts, (x, typ1) :: typs, typ')
  | ExtArg (x, typ1, typ2) ->
      let exts, typs, typ' = decomp_funs_n n typ2 in
      ((x, typ1) :: exts, typs, typ')
  | _ when n = 0 -> ([], [], typ)
  | _ ->
      Debug.printf "%a@." print typ;
      assert false

let rec arg_num = function
  | Var _ -> 0
  | Base _ -> 0
  | Tuple _ -> 0
  | Inter (typ, []) -> List.length @@ fst @@ TU.decomp_tfun typ
  | Inter (_, typ :: _) -> arg_num typ
  | Union (typ, []) -> List.length @@ fst @@ TU.decomp_tfun typ
  | Union (_, typ :: _) -> arg_num typ
  | Fun (_, _, typ2) -> 1 + arg_num typ2
  | ExtArg (_, _, typ2) -> arg_num typ2
  | Constr _ -> 0
  | List _ -> 0
  | Variant _ -> 0
  | Record _ -> 0
  | Exn (typ, _) -> arg_num typ

let map_pred f =
  let tr = !!S.Tr.make in
  tr.term <- f;
  make_trans ~tr (fun _ _ -> None)

let rec subst_map map typ =
  let f = subst_map map in
  match typ with
  | Var s -> Var s
  | Base (base, y, p) ->
      let map' = List.filter_out (fst |- Id.eq y) map in
      Base (base, y, SU.subst_map map' p)
  | Constr (s, tys, y, p) ->
      let map' = List.filter_out (fst |- Id.eq y) map in
      Constr (s, List.map f tys, y, SU.subst_map map' p)
  | Fun (y, typ1, typ2) ->
      let map' = List.filter_out (fst |- Id.eq y) map in
      let y', typ2' =
        if Id.List.mem y @@ List.flatten_map (snd |- S.get_fv) map then
          let y' = Id.new_var_id y in
          (y', subst_map [ (y, SU.make_var y') ] typ2)
        else (y, typ2)
      in
      Fun (y', f typ1, subst_map map' typ2')
  | Tuple xtyps -> Tuple (List.map (Pair.map_snd @@ f) xtyps)
  | Inter (typ, typs) -> Inter (typ, List.map f typs)
  | Union (typ, typs) -> Union (typ, List.map f typs)
  | ExtArg (y, typ1, typ2) ->
      let map' = List.filter_out (fst |- Id.eq y) map in
      ExtArg (y, f typ1, subst_map map' typ2)
  | List (y, p_len, z, p_i, typ) ->
      let map1 = List.filter_out (fst |- Id.eq y) map in
      let map2 = List.filter_out (fst |- Id.eq z) map1 in
      List (y, SU.subst_map map p_len, z, SU.subst_map map1 p_i, subst_map map2 typ)
  | Variant labels -> Variant (List.map (Pair.map_snd @@ List.map f) labels)
  | Record fields -> Record (List.map (Pair.map_snd @@ Pair.map_snd f) fields)
  | Exn (typ1, typ2) -> Exn (f typ1, f typ2)

let subst x t typ = subst_map [ (x, t) ] typ
let subst_var x y typ = subst x (SU.make_var y) typ
let subst_rev t x typ = map_pred (SU.subst_rev t x) typ

let replace_term t1 t2 t3 =
  let x = Id.new_var t1.S.typ in
  subst x t2 @@ subst_rev t1 x t3

let subst_constr ?(force = false) s ty1 =
  let aux _ ty2 =
    match ty2 with
    | Constr (s', _, _, t) when s = s' ->
        if not force then assert (S.(t.desc = Const True));
        Some ty1
    | _ -> None
  in
  make_trans aux

let rec rename full var ty =
  let f = rename full in
  let new_var x = if full then Id.new_var ~name:"x" @@ Id.typ x else Id.new_var_id x in
  match ty with
  | Var s -> Var s
  | Base (base, x, p) ->
      let x' = Option.default (new_var x) var in
      Base (base, x', SU.subst_var x x' p)
  | Constr (s, tys, x, p) ->
      let x' = Option.default (new_var x) var in
      Constr (s, List.map (f var) tys, x', SU.subst_var x x' p)
  | Fun (x, typ1, typ2) ->
      let x' = new_var x in
      let typ2' = subst_var x x' typ2 in
      Fun (x', f (Some x') typ1, f None typ2')
  | Tuple xtyps ->
      let aux (x, typ) xtyps =
        let x' = new_var x in
        let sbst = subst_var x x' in
        let xtyps' = List.map (Pair.map_snd sbst) xtyps in
        (x', f (Some x') @@ sbst typ) :: xtyps'
      in
      Tuple (List.fold_right aux xtyps [])
  | Inter (typ, typs) -> Inter (typ, List.map (f var) typs)
  | Union (typ, typs) -> Union (typ, List.map (f var) typs)
  | ExtArg (x, typ1, typ2) ->
      let x' = new_var x in
      let typ2' = subst_var x x' typ2 in
      ExtArg (x', f (Some x') typ1, f None typ2')
  | List (x, p_len, y, p_i, typ) ->
      let x' = new_var x in
      let y' = new_var y in
      let p_len' = SU.subst_var x x' p_len in
      let p_i' = SU.subst_var y y' p_i in
      let typ' = subst_var x x' typ in
      let typ'' = subst_var y y' typ' in
      List (x', p_len', y', p_i', f None typ'')
  | Variant labels -> Variant (List.map (Pair.map_snd @@ List.map @@ f None) labels)
  | Record fields -> Record (List.map (Pair.map_snd @@ Pair.map_snd @@ f None) fields)
  | Exn (typ1, typ2) -> Exn (f var typ1, f var typ2)

let rename ?(full = false) typ = rename full None typ

let rec of_simple typ =
  match T.elim_tattr typ with
  | TBase TUnit -> Base (TUnit, Id.new_var typ, SU.true_term)
  | TBase TBool -> Base (TBool, Id.new_var typ, SU.true_term)
  | TBase TInt -> Base (TInt, Id.new_var typ, SU.true_term)
  | TConstr (c, [ typ ]) when c = T.C.list ->
      List (Id.new_var TU.Ty.int, SU.true_term, Id.new_var TU.Ty.int, SU.true_term, of_simple typ)
  | TConstr (constr, tys) -> Constr (constr, List.map of_simple tys, Id.new_var typ, SU.true_term)
  | TFun (x, typ) -> Fun (x, of_simple @@ Id.typ x, of_simple typ)
  | TTuple xs -> Tuple (List.map (Pair.add_right @@ (of_simple -| Id.typ)) xs)
  | TVar (_, { contents = Some ty }, _) -> of_simple ty
  | TVar x -> Var x
  | TVariant (_, rows) ->
      let rows =
        rows
        |> List.map (fun { Type.row_constr; row_args; row_ret } ->
               if row_ret <> None then unsupported "%s" __FUNCTION__;
               (row_constr, List.map of_simple row_args))
      in
      Variant rows
  | TRecord fields -> Record (List.map (Pair.map_snd @@ Pair.map_snd of_simple) fields)
  | TModSig _ | TModLid _ -> typ_module
  | _ ->
      Format.fprintf !Flag.Print.target "%a@." Print.typ typ;
      unsupported "Ref_type.of_simple"

let rec to_abst_typ ?(decomp_pred = false) ?(with_pred = false) typ =
  let f = to_abst_typ ~decomp_pred ~with_pred in
  match typ with
  | Var x -> T.TVar x
  | Base (base, x, ({ S.desc = S.Const _ } as p)) ->
      let sty = T.TBase base in
      if with_pred then TU.add_tattr (T.TARefPred (x, p)) sty
      else
        let ps = if decomp_pred then SU.decomp_and p else [ p ] in
        TU.add_tattr (T.TAPred (x, ps)) sty
  | Base (base, x, t) ->
      let x' = Id.new_var_id x in
      let typ' = T.TBase base in
      let ps =
        if !Flag.PredAbst.decomp_pred then SU.decomp_bexp @@ SU.subst_var x x' t
        else [ SU.subst_var x x' t ]
      in
      SU.add_tapred x' ps typ'
  | Constr (s, tys, _, _) ->
      if not with_pred then warning "Abstraction type of ADT cannot have predicates";
      T.TConstr (s, List.map f tys)
  | Fun (x, typ1, typ2) ->
      let x' = Id.new_var ~name:(Id.name x) @@ f typ1 in
      let typ2' = f @@ subst_var x x' typ2 in
      T.TFun (x', typ2')
  | Tuple xtyps ->
      let aux (x, typ) xs =
        let x' = Id.new_var ~name:(Id.name x) @@ f typ in
        List.map (Id.map_typ @@ SU.subst_type_var x x') (x' :: xs)
      in
      T.TTuple (List.fold_right aux xtyps [])
  | Inter (styp, typs) | Union (styp, typs) -> List.fold_right (SU.merge_typ -| f) typs styp
  | ExtArg _ -> unsupported "Ref_type.to_abst_typ"
  | List (x, p_len, y, p_i, typ1) ->
      if p_i.S.desc <> S.Const S.True || occur y typ1 then unsupported "Ref_type.to_abst_typ"
      else
        let x' = Id.new_var ~name:"xs" @@ TU.make_tlist @@ f typ1 in
        if p_len = SU.true_term then Id.typ x'
        else SU.(add_tapred x' Term.[ (x |-> length (var x')) p_len ] @@ Id.typ x')
  | Variant _labels -> unsupported "to_abst_typa"
  | Record _fields -> unsupported "to_abst_typa"
  | Exn (typ1, _) -> f typ1

let rec to_simple ?(with_pred = false) typ =
  let f = to_simple ~with_pred in
  match typ with
  | Var x -> T.TVar x
  | Base (b, x, p) -> T.TBase b |> with_pred ^> TU.add_tattr (T.TARefPred (x, p))
  | Constr (s, tys, x, p) ->
      T._TConstr s @@ List.map f tys |> with_pred ^> TU.add_tattr (T.TARefPred (x, p))
  | Fun (x, typ1, typ2) ->
      let x' = Id.set_typ x @@ f typ1 in
      T.TFun (x', f typ2)
  | Tuple xtyps -> TU.make_ttuple (List.map (f -| snd) xtyps)
  | Inter (sty, _) | Union (sty, _) -> if with_pred then to_abst_typ typ else sty
  | ExtArg _ -> assert false
  | List (_, _, _, _, typ) -> TU.make_tlist @@ f typ
  | Variant labels ->
      T.TVariant
        ( VNonPoly,
          List.map
            (fun (row_constr, row_args) ->
              { Type.row_constr; row_args = List.map f row_args; row_ret = None })
            labels )
  | Record fields -> T.TRecord (List.map (Pair.map_snd @@ Pair.map_snd f) fields)
  | Exn (typ1, _) -> f typ1

let make_base ?(pred = SU.true_term) base = Base (base, Id.new_var (Type.TBase base), pred)
let make_fun ty1 ty2 = Fun (Id.new_var @@ to_simple ty1, ty1, ty2)
let make_tuple tys = Tuple (List.map (fun ty -> (Id.new_var (to_simple ty), ty)) tys)

let make_ref ty =
  Constr (TU.lid_of_string "ref", [ ty ], Id.new_var (TU.Ty.ref @@ to_simple ty), SU.true_term)

let rec set_base_var x = function
  | Base (base, y, p) -> Base (base, x, SU.subst_var y x p)
  | Inter (typ, typs) -> Inter (typ, List.map (set_base_var x) typs)
  | Union (typ, typs) -> Union (typ, List.map (set_base_var x) typs)
  | typ -> typ

let copy_fun_arg_to_base =
  let aux f ty =
    match ty with
    | Fun (x, typ1, typ2) -> Some (Fun (x, set_base_var x @@ f typ1, f typ2))
    | _ -> None
  in
  make_trans aux

let rec same typ1 typ2 =
  match (typ1, typ2) with
  | Base (base1, x1, p1), Base (base2, x2, p2) ->
      base1 = base2 && (SU.same_term p1 @@ SU.subst_var x2 x1 p2)
  | Fun (x1, typ11, typ12), Fun (x2, typ21, typ22) ->
      same typ11 typ21 && (same typ12 @@ subst_var x2 x1 typ22)
  | Tuple xtyps1, Tuple xtyps2 ->
      let typs1 = List.map snd xtyps1 in
      let typs2 =
        List.map
          (fun (_, typ) ->
            List.fold_left2 (fun typ (x1, _) (x2, _) -> subst_var x2 x1 typ) typ xtyps1 xtyps2)
          xtyps2
      in
      List.eq ~eq:same typs1 typs2
  | Inter (_, typs1), Inter (_, typs2) -> List.eq ~eq:same typs1 typs2
  | Union (_, typs1), Union (_, typs2) -> List.eq ~eq:same typs1 typs2
  | ExtArg (x1, typ11, typ12), ExtArg (x2, typ21, typ22) ->
      same typ11 typ21 && (same typ12 @@ subst_var x2 x1 typ22)
  | List (x1, p1_len, y1, p1_i, typ1'), List (x2, p2_len, y2, p2_i, typ2') ->
      (SU.same_term p1_len @@ SU.subst_var x2 x1 p2_len)
      && (SU.same_term p1_i @@ SU.subst_var x2 x1 @@ SU.subst_var y2 y1 p2_i)
      && (same typ1' @@ subst_var x2 x1 @@ subst_var y2 y1 typ2')
  | _ -> false

let rec has_no_predicate typ =
  let f = has_no_predicate in
  match typ with
  | Var _ -> true
  | Base (_, _, t) -> t = SU.true_term
  | Constr (_, tys, _, t) -> List.for_all f tys && t = SU.true_term
  | Fun (_, typ1, typ2) -> f typ1 && f typ2
  | Tuple xtyps -> List.for_all (f -| snd) xtyps
  | Inter (_, typs) | Union (_, typs) -> List.for_all f typs
  | ExtArg _ -> [%unsupported]
  | List (_, p_len, _, p_i, typ1) -> p_len = SU.true_term && p_i = SU.true_term && f typ1
  | Variant labels -> List.for_all (snd |- List.exists f) labels
  | Record fields -> List.for_all (snd |- snd |- f) fields
  | Exn (typ1, typ2) -> f typ1 && f typ2

let conv = Fpat.Formula.of_term -| FpatInterface.of_term
let is_sat = FpatInterface.is_sat -| conv
let is_valid = FpatInterface.is_valid -| conv
let implies ts t = FpatInterface.implies (List.map conv ts) [ conv t ]

let rec simplify_pred t =
  try
    if not @@ is_sat t then SU.false_term
    else if is_valid t then SU.true_term
    else
      match S.desc t with
      | S.BinOp (S.And, t1, t2) ->
          let t1' = simplify_pred t1 in
          let t2' = simplify_pred t2 in
          if implies [ t1' ] t2' then t1'
          else if implies [ t2' ] t1' then t2'
          else SU.make_and t1' t2'
      | S.BinOp (S.Or, t1, t2) ->
          let t1' = simplify_pred t1 in
          let t2' = simplify_pred t2 in
          if implies [ t1' ] t2' then t2'
          else if implies [ t2' ] t1' then t1'
          else SU.make_or t1' t2'
      | _ -> t
  with Unsupported _ -> t

let rec flatten typ =
  match typ with
  | Inter (styp, typs) ->
      let typs' = List.map flatten typs in
      let typs'' = List.flatten_map decomp_inter typs' in
      Inter (styp, typs'')
  | Union (styp, typs) ->
      let typs' = List.map flatten typs in
      let typs'' = List.flatten_map decomp_union typs' in
      Union (styp, typs'')
  | _ -> typ

let make_env x typ = match typ with Base (_, y, t) -> SU.subst_var y x t | _ -> SU.true_term

let rec subtype env typ1 typ2 =
  let r =
    match (typ1, typ2) with
    | Base (base1, x, t1), Base (base2, y, t2) ->
        base1 = base2 && implies (t1 :: env) (SU.subst_var y x t2)
    | Fun (x, typ11, typ12), Fun (y, typ21, typ22) ->
        let env' = make_env x typ11 :: env in
        subtype env typ21 typ11 && subtype env' typ12 (subst_var y x typ22)
    | _, Inter (_, typs) -> List.for_all (subtype env typ1) typs
    | Union (_, typs), _ -> List.for_all (subtype env -$- typ2) typs
    | Inter (_, typs), _ -> List.exists (subtype env -$- typ2) typs || is_top' typ2
    | _, Union (_, typs) -> List.exists (subtype env typ1) typs || is_bottom typ1
    | Tuple xtyps1, Tuple xtyps2 ->
        let aux (env, acc) (x1, typ1) (_x2, typ2) =
          (* TODO: Fix to use x2 *)
          (make_env x1 typ1 :: env, acc && subtype env typ1 typ2)
        in
        List.length xtyps1 = List.length xtyps2
        && (snd @@ List.fold_left2 aux (env, true) xtyps1 xtyps2)
    | Exn (typ11, typ12), Exn (typ21, typ22) -> subtype env typ11 typ21 && subtype env typ12 typ22
    | Exn (typ11, typ12), _ when is_bottom typ12 -> subtype env typ11 typ2
    | _, Exn (typ21, _) -> subtype env typ1 typ21
    | Exn _, _ -> false
    | List (x1, p_len1, y1, p_i1, typ1'), List (x2, p_len2, y2, p_i2, typ2') ->
        let typ1'' =
          Tuple
            [
              (x1, Base (T.TInt, x1, p_len1));
              (Id.new_var TU.Ty.int, Fun (y1, Base (T.TInt, y1, p_i1), typ1'));
            ]
        in
        let typ2'' =
          Tuple
            [
              (x2, Base (T.TInt, x2, p_len2));
              (Id.new_var TU.Ty.int, Fun (y2, Base (T.TInt, y2, p_i2), typ2'));
            ]
        in
        subtype env typ1'' typ2''
    | Constr (s1, [], x, t1), Constr (s2, [], y, t2) ->
        s1 = s2 && implies (t1 :: env) (SU.subst_var y x t2)
    | _ ->
        Format.eprintf "typ1: %a@." print typ1;
        Format.eprintf "typ2: %a@." print typ2;
        unsupported "Ref_type.subtype"
  in
  if 0 = 0 then (
    Debug.printf "  sub typ1: %a@." print typ1;
    Debug.printf "  sub typ2: %a@." print typ2;
    Debug.printf "  sub r: %b@." r);
  r

let subtype typ1 typ2 = subtype [] typ1 typ2
let suptype typ1 typ2 = subtype typ2 typ1
let equiv typ1 typ2 = subtype typ1 typ2 && subtype typ2 typ1

let remove_if f typs =
  let rec aux acc typs =
    match typs with
    | [] -> acc
    | typ :: typs' ->
        let acc' = if List.exists (f -$- typ) (acc @ typs') then acc else typ :: acc in
        aux acc' typs'
  in
  aux [] typs

let remove_subtype ?(sub = subtype) typs = remove_if sub typs
let remove_equiv typs = remove_if equiv typs

let rec simplify_typs constr sub styp is_zero make_zero and_or typs =
  let decomp typ =
    match typ with Inter (_, typs) -> typs | Union (_, typs) -> typs | typ -> [ typ ]
  in
  Debug.printf "ST@.";
  let typs' =
    typs
    |@> Debug.printf "ST1: @[%a@." (List.print print)
    |> List.map simplify
    |@> Debug.printf "ST2: @[%a@." (List.print print)
    |> remove_subtype ~sub
    |@> Debug.printf "ST3: @[%a@." (List.print print)
    |*> List.unique ~eq:same
    |> constr styp
    |> flatten
    |> decomp
  in
  let typs'' =
    let remove_exn = function Exn (typ, _) | typ -> typ in
    if List.length typs' >= 2 && List.exists (function Exn _ -> false | _ -> true) typs' then
      List.map remove_exn typs'
    else typs'
  in
  Debug.printf "ST: @[%a ==>@ %a@." (List.print print) typs (List.print print) typs'';
  if List.exists is_zero typs'' then make_zero styp
  else
    match typs'' with
    | [] -> constr styp []
    | [ typ ] -> typ
    | _ ->
        if List.for_all is_base typs'' then (
          let bs, xs, ts = List.split3 @@ List.map (Option.get -| decomp_base) typs'' in
          let base = List.hd bs in
          assert (List.for_all (( = ) base) bs);
          let x = List.hd xs in
          let ts' = List.map2 (SU.subst_var -$- x) xs ts in
          Base (base, x, and_or ts'))
        else if List.for_all is_fun typs'' then
          let xs, typs1, typs2 = List.split3 @@ List.map (Option.get -| decomp_fun) typs'' in
          if List.for_all (same @@ List.hd typs1) @@ List.tl typs1 then
            let x = List.hd xs in
            let typs2' = List.map2 (subst_var -$- x) xs typs2 in
            let styp' = to_simple @@ List.hd typs2 in
            Fun (x, List.hd typs1, simplify_typs constr sub styp' is_zero make_zero and_or typs2')
          else flatten @@ constr styp typs''
          (*
    else if List.for_all is_list typs' then
      let xs,p_lens,ys,p_is,typs'' = List.split3 @@ List.map (Option.get -| decomp_fun) typs' in
*)
        else flatten @@ constr styp typs''

and simplify typ =
  let f = simplify in
  match flatten typ with
  | Var s -> Var s
  | Base (base, x, p) ->
      let p' = simplify_pred p in
      if p' = SU.false_term then Union (to_simple typ, []) else Base (base, x, p')
  | Constr (s, tys, x, p) ->
      let p' = simplify_pred p in
      if p' = SU.false_term then Union (to_simple typ, []) else Constr (s, List.map f tys, x, p')
  | Fun (x, typ1, typ2) -> Fun (x, f typ1, f typ2)
  | Tuple xtyps ->
      let xtyps' = List.map (Pair.map_snd f) xtyps in
      if List.exists (snd |- is_bottom) xtyps' then Union (to_simple typ, []) else Tuple xtyps'
  | Inter (styp, []) -> Inter (styp, [])
  | Inter (styp, typs) ->
      let _Inter' styp typs =
        if typs <> [] && List.for_all (function Tuple _ -> true | _ -> false) typs then
          let xtypss = List.map (function Tuple xs -> xs | _ -> assert false) typs in
          let xs, typss =
            match xtypss with
            | [] -> assert false
            | xtyps :: ytypss ->
                let xs = List.map fst xtyps in
                let rename ytyps =
                  List.fold_right2
                    (fun x (y, typ) acc ->
                      let sbst = subst_var x y in
                      sbst typ :: List.map sbst acc)
                    xs ytyps []
                in
                (xs, List.map snd xtyps :: List.map rename ytypss)
          in
          let typss' = List.transpose typss in
          Tuple
            (List.map2 (fun x typs -> (x, f @@ _Inter (to_simple @@ List.hd typs) typs)) xs typss')
        else _Inter styp typs
      in
      simplify_typs _Inter' subtype styp is_bottom (_Union -$- []) SU.make_ands typs
  | Union (styp, []) -> Union (styp, [])
  | Union (styp, typs) -> simplify_typs _Union suptype styp is_top (_Inter -$- []) SU.make_ors typs
  | ExtArg (x, typ1, typ2) -> ExtArg (x, f typ1, f typ2)
  | List (x, p_len, y, p_i, typ) ->
      let p_len' = simplify_pred p_len in
      if p_len' = SU.false_term then Union (to_simple typ, [])
      else List (x, p_len', y, simplify_pred p_i, f typ)
  | Variant labels -> Variant (List.map (Pair.map_snd @@ List.map f) labels)
  | Record fields -> Record (List.map (Pair.map_snd @@ Pair.map_snd f) fields)
  | Exn (typ1, typ2) ->
      let typ1' = f typ1 in
      let typ2' = f typ2 in
      if is_bottom typ2' then typ1' else Exn (typ1', typ2')

let rec make_strongest typ =
  match T.elim_tattr typ with
  | TBase TUnit -> Base (TUnit, Id.new_var typ, SU.false_term)
  | TBase TBool -> Base (TBool, Id.new_var typ, SU.false_term)
  | TBase TInt -> Base (TInt, Id.new_var typ, SU.false_term)
  | TFun (x, typ) -> Fun (x, make_weakest @@ Id.typ x, make_strongest typ)
  | TTuple xs -> Tuple (List.map (Pair.add_right (make_strongest -| Id.typ)) xs)
  | TConstr (c, _) when c = T.C.list -> unsupported "Ref_type.make_strongest TList"
  | _ when typ = TU.Ty.result -> Base (T.TUnit, Id.new_var typ, SU.false_term)
  | _ ->
      Format.eprintf "make_strongest: %a@." Print.typ typ;
      unsupported "Ref_type.make_strongest"

and make_weakest typ =
  match T.elim_tattr typ with
  | TBase TUnit -> Base (TUnit, Id.new_var typ, SU.true_term)
  | TBase TBool -> Base (TBool, Id.new_var typ, SU.true_term)
  | TBase TInt -> Base (TInt, Id.new_var typ, SU.true_term)
  | TConstr _ -> unsupported "Ref_type.make_weakest List"
  | TAttr ([ T.TAPureFun ], T.TFun (x, typ)) -> Fun (x, make_weakest @@ Id.typ x, make_weakest typ)
  | TFun (x, typ) -> Fun (x, make_strongest @@ Id.typ x, make_weakest typ)
  | TTuple xs -> Tuple (List.map (Pair.add_right (make_weakest -| Id.typ)) xs)
  | _ when typ = TU.Ty.result -> Base (T.TUnit, Id.new_var typ, SU.true_term)
  | _ ->
      Format.eprintf "make_weakest: %a@." Print.typ typ;
      unsupported "Ref_type.make_weakest"

let inter styp typs = simplify @@ Inter (styp, typs)
let union styp typs = simplify @@ Union (styp, typs)

let decomp_funs_and_classify typs =
  let typs' = List.map (Option.get -| decomp_fun) typs in
  List.classify ~eq:(fun (_, typ1, _) (_, typ2, _) -> same typ1 typ2) typs'

let merge constr typs =
  let x, typ1, _ = List.hd typs in
  let typs' = List.map (fun (y, _, typ2) -> subst_var y x typ2) typs in
  Fun (x, typ1, constr typs')

let rec push_inter_union_into typ =
  match typ with
  | Inter (styp, (Fun _ :: _ as typs)) ->
      let typss = decomp_funs_and_classify @@ List.map push_inter_union_into typs in
      inter styp @@ List.map (merge @@ inter styp) typss
  | Union (styp, (Fun _ :: _ as typs)) ->
      let typss = decomp_funs_and_classify @@ List.map push_inter_union_into typs in
      union styp @@ List.map (merge @@ union styp) typss
  | _ -> typ

module Value = struct
  type t' = t
  type t = t'

  let print = print
  let merge typ1 typ2 = [ inter (to_simple typ1) [ typ1; typ2 ] ]
  let eq = equiv
end

module Env = Menv.Make (Syntax.ID) (Value)

type env = Env.t

module NegValue = struct
  type t' = t
  type t = t'

  let print = print
  let merge typ1 typ2 = [ union (to_simple typ1) [ typ1; typ2 ] ]
  let eq = equiv
end

module NegEnv = Menv.Make (Syntax.ID) (NegValue)

type neg_env = NegEnv.t

let rec contract typ =
  let f = contract in
  match flatten typ with
  | Var _ -> typ
  | Base _ -> typ
  | Fun (x, typ1, typ2) -> Fun (x, contract typ1, contract typ2)
  | Tuple xtyps -> Tuple (List.map (Pair.map_snd contract) xtyps)
  | Inter (typ, typs) -> (
      let typs = List.map contract typs in
      let typs' =
        List.fold_right
          (fun typ acc -> if List.exists (equiv typ) acc then acc else typ :: acc)
          typs []
      in
      match typs' with [ typ' ] -> typ' | _ -> Inter (typ, typs'))
  | Union (typ, typs) -> (
      let typs = List.map contract typs in
      let typs' =
        List.fold_right
          (fun typ acc -> if List.exists (equiv typ) acc then acc else typ :: acc)
          typs []
      in
      match typs' with [ typ' ] -> typ' | _ -> Union (typ, typs'))
  | ExtArg (x, typ1, typ2) -> ExtArg (x, contract typ1, contract typ2)
  | List (x, p_len, y, p_i, typ) -> List (x, p_len, y, p_i, contract typ)
  | Constr (constr, tys, x, p) -> Constr (constr, List.map contract tys, x, p)
  | Variant labels -> Variant (List.map (Pair.map_snd @@ List.map f) labels)
  | Record fields -> Record (List.map (Pair.map_snd @@ Pair.map_snd f) fields)
  | Exn (typ1, typ2) -> Exn (contract typ1, contract typ2)

let rec split_inter typ =
  match typ with
  | Base (base, x, p) ->
      let rec decomp t =
        match t.Syntax.desc with
        | Syntax.BinOp (Syntax.And, t1, t2) -> decomp t1 @ decomp t2
        | _ -> [ t ]
      in
      let ps = decomp p in
      List.map (fun p' -> Base (base, x, p')) ps
  | Fun (x, typ1, typ2) ->
      let typs2 = split_inter typ2 in
      List.map (fun typ2' -> Fun (x, typ1, typ2')) typs2
  | Tuple xtyps ->
      let make i typ =
        let xtyps' =
          List.mapi (fun j (x, typ') -> (x, if i = j then typ else top @@ to_simple typ')) xtyps
        in
        Tuple xtyps'
      in
      List.flatten_mapi (fun i (_, typ) -> List.map (make i) @@ split_inter typ) xtyps
  | Inter (styp, typs) -> [ Inter (styp, List.flatten_map split_inter typs) ]
  | _ -> [ typ ]

let rec has_inter_union ty =
  let f = has_inter_union in
  match ty with
  | Var _ -> false
  | Base _ -> false
  | Constr (_, tys, _, _) -> List.exists f tys
  | Fun (_, ty1, ty2) -> f ty1 || f ty2
  | Tuple xts -> List.exists (snd |- f) xts
  | Inter (_, tys) -> tys <> []
  | Union (_, tys) -> tys <> []
  | ExtArg (_, ty1, ty2) -> f ty1 || f ty2
  | List (_, _, _, _, ty') -> f ty'
  | Variant labels -> List.exists (snd |- List.exists f) labels
  | Record fields -> List.exists (snd |- snd |- f) fields
  | Exn (ty1, ty2) -> f ty1 || f ty2

let replace_base_with_int =
  let aux _ ty =
    match ty with
    | Base (T.TUnit, _, _) -> None
    | Base (_, y, p) -> Some (Base (T.TInt, y, p))
    | _ -> None
  in
  make_trans aux

let replace_constr_with_int =
  let new_base p = Base (T.TInt, Id.new_var TU.Ty.int, p) in
  let aux _ ty =
    match ty with
    | Constr (_, _, _, p) ->
        if p <> SU.true_term then unsupported "-data-to-int";
        Some (new_base p)
    | Variant _ -> Some (new_base SU.Term.true_)
    | _ -> None
  in
  make_trans aux

let replace_list_with_int =
  let aux _ ty =
    match ty with List _ -> Some (Base (T.TInt, Id.new_var TU.Ty.int, SU.Term.true_)) | _ -> None
  in
  make_trans aux

let replace_abst_with_int =
  let abst = of_simple Type_util.Ty.abst in
  make_trans (fun _ ty -> if ty = abst then Some (make_base TInt) else None)

let replace_constr_with_int_but_exn exn_constrs =
  let new_base p = Base (T.TInt, Id.new_var TU.Ty.int, p) in
  let aux _ ty =
    match ty with
    | Constr (s, _, _, _) when List.mem s exn_constrs -> None
    | Constr (_, _, _, p) ->
        if p <> SU.true_term then unsupported "-data-to-int-but-exn";
        Some (new_base p)
    | Variant _ -> Some (new_base SU.Term.true_)
    | _ -> None
  in
  make_trans aux

let rec is_safe_fun ty =
  match ty with
  | Var _ -> true
  | Base (_, _, _) -> true
  | Constr (_, [], _, _) -> true
  | Constr (_, _, _, _) -> unsupported "is_safe_fun App"
  | Fun (_, ty1, ty2) -> not_restricted ty1 && is_safe_fun ty2
  | Tuple xts -> List.for_all (is_safe_fun -| snd) xts
  | Inter (_, tys) -> List.exists is_safe_fun tys
  | Union (_, tys) -> List.for_all is_safe_fun tys
  | ExtArg (_, _ty1, _ty2) -> unsupported "is_safe_fun ExtArg"
  | List (_, _, _, p_i, ty) -> p_i.desc = Const True && is_safe_fun ty
  | Variant _labels -> unsupported "is_safe_fun Variant"
  | Record _fields -> unsupported "is_safe_fun Record"
  | Exn (_ty1, _ty2) -> unsupported "is_safe_fun Exn"

and not_restricted ty =
  match ty with
  | Var _ -> true
  | Base (_, _, p) -> p.desc = Const True
  | Constr (_, tys, _, p) -> p.desc = Const True && List.for_all not_restricted tys
  | Fun (_, ty1, ty2) -> is_safe_fun ty1 && not_restricted ty2
  | Tuple xts -> List.exists (is_safe_fun -| snd) xts
  | Inter (_, tys) -> List.for_all not_restricted tys
  | Union (_, tys) -> List.exists not_restricted tys
  | ExtArg (_, _ty1, _ty2) -> unsupported "is_safe_fun ExtArg"
  | List (_, p_len, _, _, ty) -> p_len.desc = Const True && not_restricted ty
  | Variant _labels -> unsupported "is_safe_fun Variant"
  | Record _fields -> unsupported "is_safe_fun Record"
  | Exn (_ty1, _ty2) -> unsupported "is_safe_fun Exn"

let col_constr =
  let f _ ty = match ty with Constr (s, _, _, _) -> Some [ s ] | _ -> None in
  make_col f [] ( @@@ )

let has_precondition ty =
  let rec has_pre ty =
    match ty with
    | Var _ -> false
    | Base _ -> false
    | Fun (_, ty1, ty2) -> has_pre ty2 || has_post ty1
    | Tuple _ -> false
    | Inter (_, tys) -> List.exists has_post tys
    | Union (_, tys) -> List.exists has_post tys
    | ExtArg _ -> [%unsupported]
    | List _ -> false
    | Constr _ -> false
    | Variant _ -> false
    | Record _ -> false
    | Exn (ty, _) -> has_pre ty
  and has_post ty =
    match ty with
    | Var _ -> false
    | Base (_, _, p) -> p.desc <> Const True
    | Fun (_, ty1, ty2) -> has_post ty2 || has_pre ty1
    | Tuple xtys -> List.exists (snd |- has_post) xtys
    | Inter (_, tys) -> List.exists has_post tys
    | Union (_, tys) -> List.exists has_post tys
    | ExtArg _ -> [%unsupported]
    | List (_, p_len, _, p_i, ty) ->
        p_len.desc <> Const True || p_i.desc <> Const True || has_post ty
    | Constr (_, tys, _, p) -> p.desc <> Const True || List.exists has_post tys
    | Variant labels -> List.exists (snd |- List.exists has_post) labels
    | Record fields -> List.exists (snd |- snd |- has_post) fields
    | Exn (ty, _) -> has_post ty
  in
  has_pre ty

let subst_tvar ?stenv env =
  let stenv = Option.default_delayed (fun () -> List.map (Pair.map_snd to_simple) env) stenv in
  let sbst = Id.map_typ (TU.subst_tvar stenv) in
  make_trans (fun tr ty ->
      match ty with
      | Var (_, r, _) -> List.assq_opt r env
      | Base (b, x, p) -> Some (Base (b, sbst x, p))
      | Fun (x, ty1, ty2) ->
          let x' = sbst x in
          let ty2' = subst_var x x' @@ tr ty2 in
          Some (Fun (x', tr ty1, ty2'))
      | Tuple xtys -> Some (Tuple (Fmap.(list (sbst * tr)) xtys))
      | Inter (sty, tys) -> Some (Inter (TU.subst_tvar stenv sty, List.map tr tys))
      | Union (sty, tys) -> Some (Union (TU.subst_tvar stenv sty, List.map tr tys))
      | ExtArg (x, ty1, ty2) -> Some (ExtArg (sbst x, tr ty1, tr ty2))
      | List (len, p_len, i, p_i, ty) -> Some (List (sbst len, p_len, sbst i, p_i, tr ty))
      | Constr (c, tys, x, p) -> Some (Constr (c, List.map tr tys, sbst x, p))
      | _ -> None)

module Ty = struct
  let result = typ_result
  let base = make_base
  let unit ?pred () = base ?pred Type.TUnit
  let bool ?pred () = base ?pred Type.TBool
  let int ?pred () = base ?pred Type.TInt
  let fun_ = make_fun
  let tuple = make_tuple
  let ( * ) t1 t2 = tuple [ t1; t2 ]
  let ref = make_ref
end
