open Util

module Debug_attr = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__ ^ ".attr") end)
module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type base =
  | TUnit
  | TBool
  | TInt
  | TPrim of string

and 'a id = 'a t Id.t

and 'a t =
  | TBase of base
  | TVar of 'a t option ref * int
  | TFun of 'a id * 'a t
  | TFuns of 'a id list * 'a t (* Just for fair-termination. TODO: Refactor *)
  | TTuple of 'a id list
  | TData of string
  | TVariant of bool * (string * 'a t list) list (** true means polymorphic variant *)
  | TRecord of (string * (mutable_flag * 'a t)) list
  | TApp of string * 'a t list
  | TAttr of 'a attr list * 'a t
  | TModule of 'a signature

and mutable_flag = Immutable | Mutable

and 'a attr =
  | TAPred of 'a id * 'a list (* TAPred occur at most ones *)
  | TAPredShare of int
  | TARefPred of 'a id * 'a (* TARefPred occur at most ones *)
  | TAPureFun
  | TAEffect of effect list
  | TAId of string * int
  | TARaise of 'a t

and effect = EVar of int | EEvent | ENonDet | EDiv | EExcep

and 'a signature =
  {sig_types: 'a declaration;
   sig_values: 'a id list}

and 'a declaration = (string * 'a t) list
  [@@deriving show]

exception CannotUnify

let counter = ref 0
let new_tvar () =
  let ty = TVar(ref None, !counter) in
  incr counter;
  ty

let label_pred_share = "pred_share" (* for TAId *)

let print_as_ocaml = ref false
let set_print_as_ocaml () = print_as_ocaml := true
let tmp_set_print_as_ocaml f = Ref.tmp_set print_as_ocaml true f

let _TFun x ty = TFun(x, ty)
let _TAttr attr ty =
  if attr = [] then
    ty
  else
    match ty with
    | TAttr(attr', ty') -> TAttr(List.Set.(attr + attr'), ty')
    | _ -> TAttr(attr, ty)

let typ_unknown = TData "???"

let rec var_name_of typ =
  match typ with
  | TBase TUnit -> "u"
  | TBase TBool -> "b"
  | TBase TInt -> "n"
  | TFun _ -> "f"
  | TTuple _ -> "p"
  | TApp("list",_) -> "xs"
  | TAttr(_,ty) -> var_name_of ty
  | _ -> "x"

let new_var ?name typ =
  let name =
    match name with
    | None -> (var_name_of typ)
    | Some name -> name
  in
  Id.new_var ~name typ

let pureTFun(x,typ) = TAttr([TAPureFun], TFun(x,typ))
let raiseTFun(exn,x,typ) = TAttr([TARaise exn], TFun(x,typ))

let make_tfun ?name typ1 typ2 = TFun(new_var ?name typ1, typ2)
let make_ptfun ?name typ1 typ2 = TAttr([TAPureFun], make_tfun ?name typ1 typ2)
let make_tfun_raise ?name typ1 ~typ_exn typ2 = TAttr([TARaise typ_exn], make_tfun ?name typ1 typ2)
let make_ttuple typs = TTuple (List.map new_var typs)
let make_tpair typ1 typ2 = make_ttuple [typ1; typ2]
let make_tlist typ = TApp("list", [typ])
let make_tset typ = TApp("set", [typ])
let make_tref typ = TApp("ref", [typ])
let make_toption typ = TApp("option", [typ])
let make_tarray typ = TApp("array", [typ])
let make_tconstr s typ = TApp(s, [typ])

let make_trans f =
  let rec trans ty =
    match f trans ty with
    | None ->
        begin match ty with
        | TBase b -> TBase b
        | TVar({contents=Some ty},_) -> trans ty
        | TVar(r,id) -> TVar(r,id)
        | TFun(x,ty) -> TFun(Id.map_typ trans x, trans ty)
        | TApp(c,tys) -> TApp(c, List.map trans tys)
        | TTuple xs -> TTuple (List.map (Id.map_typ trans) xs)
        | TData s -> TData s
        | TAttr(attr,ty) -> TAttr(attr, trans ty)
        | TFuns(xs,ty) -> TFuns(List.map (Id.map_typ trans) xs, trans ty)
        | TVariant(poly,labels) -> TVariant(poly, List.map (Pair.map_snd (List.map trans)) labels)
        | TRecord fields -> TRecord (List.map (Pair.map_snd (Pair.map_snd trans)) fields)
        | TModule {sig_types; sig_values} ->
            let sig_types = List.map (Pair.map_snd trans) sig_types in
            TModule {sig_types; sig_values}
        end
    | Some ty -> ty
  in
  trans

let rec elim_tattr = function
  | TAttr(_,typ) -> elim_tattr typ
  | typ -> typ

let is_fun_typ typ =
  match elim_tattr typ with
  | TFun(_,_) -> true
  | TFuns(_,_) -> true
  | _ -> false

let rec is_base_typ = function
  | TBase _
  | TData "string" -> true
  | TAttr(_,typ) -> is_base_typ typ
  | _ -> false

let is_tuple_typ ty =
  match elim_tattr ty with
  | TTuple _ -> true
  | _ -> false

let tfuns_to_tfun = function
  | TFuns(xs,typ) -> List.fold_right _TFun xs typ
  | typ -> typ

let elim_tattr_all =
  let aux tr ty =
    match ty with
    | TAttr(_,typ) -> Some (tr typ)
    | _ -> None
  in
  fun ty -> make_trans aux ty

let decomp_base ty =
  match elim_tattr ty with
  | TBase b -> Some b
  | _ -> None

let rec decomp_tfun typ =
  match elim_tattr typ with
  | TFun(x,typ) ->
      let xs,typ = decomp_tfun typ in
      x :: xs, typ
  | _ -> [], typ

let decomp_tfuns = function
  | TFuns(xs, typ) -> xs, typ
  | _ -> invalid_arg "decomp_tfuns"

let arity typ = List.length @@ fst @@ decomp_tfun typ

let decomp_effect = function
  | TAttr(attrs, typ) ->
      let attrs1,attrs2 = List.partition (function TAEffect _ -> true | _ -> false) attrs in
      let typ' =
        if attrs2 = [] then
          typ
        else
          TAttr(attrs2, typ)
      in
      begin
        match attrs1 with
        | [] -> None
        | [TAEffect e] -> Some (e, typ')
        | _ -> invalid_arg "decomp_effect"
      end
  | _ -> None

let decomp_raise_tfun ty =
  match ty with
  | TAttr(attrs, TFun(x, ty2)) ->
      List.find_map_opt (function TARaise exn -> Some exn | _ -> None) attrs
      |> Option.map (fun exn -> exn, x, ty2)
  | _ -> None
let is_raise_tfun ty = Option.is_some (decomp_raise_tfun ty)

let print_effect fm e =
  match e with
  | EVar n -> Format.fprintf fm "'e%d" n
  | EEvent -> Format.fprintf fm "event"
  | EDiv -> Format.fprintf fm "div"
  | ENonDet -> Format.fprintf fm "nondet"
  | EExcep -> Format.fprintf fm "excep"

let rec print_attr fm a =
  match a with
  | TAPred _ -> Format.fprintf fm "TAPred"
  | TARefPred _ -> Format.fprintf fm "TARefPred"
  | TAPureFun -> Format.fprintf fm "TAPureFun"
  | TAEffect e -> Format.fprintf fm "TAEffect %a" (List.print print_effect) e
  | TAPredShare x -> Format.fprintf fm "TAPredShare %d" x
  | TAId(s,x) -> Format.fprintf fm "TAId(%s,%d)" s x
  | TARaise ty -> Format.fprintf fm "TARaise %a" (print (fun _ _ -> true) (fun _ ->  assert false)) ty

and print_tvar fm n =
  if n < 0 then
    Format.fprintf fm "'_for_debug"
  else
    let c = char_of_int @@ int_of_char 'a' + n mod 26 in
    let d = if n < 26 then "" else string_of_int (n/26) in
    Format.fprintf fm "'%c%s" c d

and print_base fm b =
  match b with
  | TUnit -> Format.fprintf fm "unit"
  | TBool -> Format.fprintf fm "bool"
  | TInt -> Format.fprintf fm "int"
  | TPrim s -> Format.fprintf fm "TPrim %s" s

and print_signature occur print_pred fm {sig_types; sig_values} =
  if !Flag.Print.signature then
    let pr = print occur print_pred in
    let pr_tys last =
      let pr_ty fm (s,ty) = Format.fprintf fm "@[<hov 2>type %s = %a@]" s pr ty in
      print_list pr_ty ~last "@\n"
    in
    let pr_vals =
      let pr_val fm x = Format.fprintf fm "@[<hov 2>val %a : %a@]" Id.print x pr (Id.typ x) in
      print_list pr_val "@\n"
    in
    let last = sig_types <> [] && sig_values <> [] in
    Format.fprintf fm "(@[sig@[<hv -1>@ %a%a@]@ end@])" (pr_tys last) sig_types pr_vals sig_values
  else
    Format.fprintf fm "sig ... end"

and print occur print_pred fm typ =
  let print' = print occur print_pred in
  let print_preds ps = print_list print_pred "; " ps in
  match typ with
  | TBase TUnit -> Format.fprintf fm "unit"
  | TBase TBool -> Format.fprintf fm "bool"
  | TBase TInt -> Format.fprintf fm "int"
  | TBase (TPrim s) -> Format.fprintf fm "%s" s
  | TVar({contents=Some typ},_) -> print' fm typ
  | TVar({contents=None}, n) -> print_tvar fm n
  | TFun _ ->
      let rec aux fm (xs, typ) =
        match xs with
        | [] ->
            print' fm typ
        | x::xs' ->
            if List.exists (occur x) (typ :: List.map Id.typ xs)
            then Format.fprintf fm "@[<hov 2>%a:%a ->@ %a@]" Id.print x print' (Id.typ x) aux (xs',typ)
            else Format.fprintf fm "@[<hov 2>%a ->@ %a@]" print' (Id.typ x) aux (xs',typ)
      in
      Format.fprintf fm "(%a)" aux @@ decomp_tfun typ
  | TFuns(xs,typ) ->
      let rec aux fm (xs, typ) =
        match xs with
        | [] -> Format.fprintf fm "[%a]" print' typ
        | x::xs' ->
            if List.exists (occur x) (typ :: List.map Id.typ xs)
            then Format.fprintf fm "@[<hov 2>%a:%a ->@ %a@]" Id.print x print' (Id.typ x) aux (xs',typ)
            else Format.fprintf fm "@[<hov 2>%a ->@ %a@]" print' (Id.typ x) aux (xs',typ)
      in
      Format.fprintf fm "(%a)" aux (xs, typ)
  | TTuple [] -> (* TODO: fix *)
      Format.fprintf fm "unit"
  | TTuple xs ->
      let pr fm x =
        if occur x typ then Format.fprintf fm "%a:" Id.print x;
        print' fm @@ Id.typ x
      in
      Format.fprintf fm "(@[<hov 2>%a@])" (print_list pr "@ *@ ") xs
  | TData s when !Flag.Print.tdata -> Format.fprintf fm "TData %s" s
  | TData s -> Format.fprintf fm "%s" s
  | TAttr(_, ty) when !print_as_ocaml -> print' fm ty
  | TAttr([], typ) -> print' fm typ
  | TAttr(TAPred(x,ps)::preds, typ) when not !!Debug_attr.check ->
      Format.fprintf fm "@[%a@[<hov 3>[\\%a. %a]@]@]" print' (TAttr(preds,typ)) Id.print x print_preds ps
  | TAttr([TAPureFun], (TFun(x,typ))) when not !!Debug_attr.check ->
      let pr_arg fm x = if occur x typ then Format.fprintf fm "%a:" Id.print x in
      Format.fprintf fm "(@[<hov 2>%a%a -*>@ %a@])" pr_arg x print' (Id.typ x) print' typ
  | TAttr(TAPureFun::attrs, ty) when not !!Debug_attr.check ->
      print' fm (TAttr(attrs@[TAPureFun],ty))
  | TAttr(TAEffect e::attrs, typ) when not !!Debug_attr.check ->
      let ty = TAttr(attrs,typ) in
      Format.fprintf fm "(@[%a # %a@])" print' ty (List.print print_effect) e
  | TAttr(TARefPred(x,p)::attrs, ty) ->
      let ty' = TAttr(attrs,ty) in
      Format.fprintf fm "@[{%a:%a|%a}@]" Id.print x print' ty' print_pred p
  | TAttr(TAId(_,x)::attrs, ty) when not !!Debug_attr.check ->
      let ty' = TAttr(attrs,ty) in
      let s1,s2 =
        match ty with
        | TFun _ -> "(", ")"
        | _ -> "", ""
      in
      Format.fprintf fm "@[%s%a%s^%d@]" s1 print' ty' s2 x
  | TAttr(attrs, ty) -> Format.fprintf fm "(%a @@ %a)" print' ty (List.print print_attr) attrs
  | TVariant(poly,labels) ->
      let pr fm (s, typs) =
        let s' = if poly then "`" ^ s else s in
        if typs = [] then
          Format.fprintf fm "%s" s'
        else
          Format.fprintf fm "@[%s of %a@]" s' (print_list print' "@ *@ ") typs
      in
      Format.fprintf fm "(@[%a@])" (print_list pr "@ | ") labels
  | TRecord fields ->
      let pr fm (s, (f, typ)) =
        let sf = if f = Mutable then "mutable " else "" in
        Format.fprintf fm "@[%s%s: %a@]" sf s print' typ
      in
      Format.fprintf fm "{@[%a@]}" (print_list pr ";@ ") fields
  | TModule sgn -> Format.fprintf fm "@[%a@]" (print_signature occur print_pred) sgn
  | TApp("ref", [typ]) -> Format.fprintf fm "@[%a ref@]" print' typ
  | TApp("list", [typ]) -> Format.fprintf fm "@[%a list@]" print' typ
  | TApp("option", [typ]) -> Format.fprintf fm "@[%a option@]" print' typ
  | TApp("array", [typ]) -> Format.fprintf fm "@[%a array@]" print' typ
  | TApp("lazy", [typ]) -> Format.fprintf fm "@[%a Lazy.t@]" print' typ
  | TApp("set", [typ]) -> Format.fprintf fm "@[%a set@]" print' typ
  | TApp _ -> assert false

let print ?(occur=fun _ _ -> false) print_pred fm typ =
  Format.fprintf fm "@[%a@]" (print occur print_pred) typ
let print_init typ = print (fun _ -> assert false) typ

let decomp_module s =
  List.decomp_snoc @@ String.split_on_char '.' s

let base = snd -| decomp_module

let rec flatten typ =
  match typ with
      TVar({contents = Some typ'},_) -> flatten typ'
    | _ -> typ

(* just for "unify"? *)
let rec occurs r typ =
  match flatten typ with
  | TBase _ -> false
  | TVar({contents=None} as r',_) -> r == r'
  | TVar({contents=Some _},_) -> assert false
  | TFun(x,typ) -> occurs r (Id.typ x) || occurs r typ
  | TApp(_, typs) -> List.exists (occurs r) typs
  | TTuple xs -> List.exists (occurs r -| Id.typ) xs
  | TData _ -> false
  | TAttr(_,typ) -> occurs r typ
  | TFuns _ -> unsupported ""
  | TVariant(_,labels) -> List.exists (snd |- List.exists @@ occurs r) labels
  | TRecord fields -> List.exists (snd |- snd |- occurs r) fields
  | TModule {sig_types} ->
      List.exists (snd |- occurs r) sig_types

let rec data_occurs s typ =
  match flatten typ with
  | TBase _ -> false
  | TVar(r,_) -> Option.exists (data_occurs s) !r
  | TFun(x,typ) -> data_occurs s (Id.typ x) || data_occurs s typ
  | TApp(_, typs) -> List.exists (data_occurs s) typs
  | TTuple xs -> List.exists (data_occurs s -| Id.typ) xs
  | TData s' -> s = s'
  | TAttr(_,typ) -> data_occurs s typ
  | TFuns _ -> unsupported ""
  | TVariant(_,labels) -> List.exists (snd |- List.exists @@ data_occurs s) labels
  | TRecord fields -> List.exists (snd |- snd |- data_occurs s) fields
  | TModule {sig_types} ->
      List.exists (snd |- data_occurs s) sig_types


let rec unify ?(for_check=false) ?tenv typ1 typ2 =
  let print_error =
    if not for_check then
      Format.eprintf
    else
      Format.ifprintf Format.std_formatter
  in
  let check_eq x y = if x <> y then raise CannotUnify in
  match flatten @@ elim_tattr typ1, flatten @@ elim_tattr typ2 with
  | TBase b1, TBase b2 -> check_eq b1 b2
  | TFun(x1, typ1), TFun(x2, typ2) ->
      unify ~for_check ?tenv (Id.typ x1) (Id.typ x2);
      unify ~for_check ?tenv typ1 typ2
  | TApp(c1,typs1), TApp(c2,typs2) ->
      check_eq c1 c2;
      List.iter2 (unify ~for_check ?tenv) typs1 typs2
  | TTuple xs1, TTuple xs2 ->
      check_eq (List.length xs1) (List.length xs2);
      List.iter2 (fun x1 x2 -> unify ~for_check ?tenv (Id.typ x1) (Id.typ x2)) xs1 xs2
  | TVar(r1,_), TVar(r2,_) when r1 == r2 -> ()
  | TVar({contents = None} as r, n), typ
  | typ, TVar({contents = None} as r, n) ->
      if occurs r typ then
        (print_error "occur-check failure: %a, %a@." print_init (flatten typ1) print_init (flatten typ2);
         raise CannotUnify);
      Debug.printf "UNIFY %a := %a@." print_tvar n print_init typ;
      r := Some typ
  | TVariant(true,_), TVariant(true,_) -> ()
  | TVariant(false,labels1), TVariant(false,labels2) ->
      check_eq (List.length labels1) (List.length labels2);
      let check (s1,typs1) (s2,typs2) =
          check_eq s1 s2;
          check_eq (List.length typs1) (List.length typs2);
          List.iter2 (unify ~for_check ?tenv) typs1 typs2
      in
      List.iter2 check labels1 labels2
  | TRecord fields1, TRecord fields2 ->
      check_eq (List.length fields1) (List.length fields2);
      let check (s1,(f1,typ1)) (s2,(f2,typ2)) =
          check_eq s1 s2;
          check_eq f1 f2;
          unify ~for_check ?tenv typ1 typ2
      in
      List.iter2 check fields1 fields2
  | TModule sgn1, TModule sgn2 ->
      check_eq (List.length sgn1.sig_types) (List.length sgn2.sig_types);
      let check (s1,ty1) (s2,ty2) =
        check_eq s1 s2;
        unify ~for_check ?tenv ty1 ty2
      in
      List.iter2 check sgn1.sig_types sgn2.sig_types;
      check_eq (List.length sgn1.sig_values) (List.length sgn2.sig_values);
      let check x y = unify ~for_check ?tenv (Id.typ x) (Id.typ y) in
      List.iter2 check sgn1.sig_values sgn2.sig_values
  | _, TData _
  | TData _, _ when tenv = None -> ()
  | TData s1, TData s2 when s1 = s2 -> ()
  | TData s, _ when Option.exists (List.mem_assoc s) tenv ->
      unify ~for_check ?tenv (List.assoc s @@ Option.get tenv) typ2
  | _, TData s when Option.exists (List.mem_assoc s) tenv ->
      unify ~for_check ?tenv typ1 (List.assoc s @@ Option.get tenv)
  | ty1, ty2 ->
      print_error "unification error: %a, %a@." print_init ty1 print_init ty2;
      raise CannotUnify

let rec eq ty1 ty2 =
  let eq_id = Compare.eq_on Id.typ ~eq in
  match ty1, ty2 with
  | TBase b1, TBase b2 -> b1 = b2
  | TVar(x,_), TVar(y,_) -> x == y
  | TFun(x,ty1), TFun(y,ty2) -> eq_id x y && eq ty1 ty2
  | TFuns _, TFuns _ -> assert false
  | TTuple tys1, TTuple tys2 -> List.eq ~eq:eq_id tys1 tys2
  | TData s1, TData s2 -> s1 = s2
  | TVariant(b1,labels1), TVariant(b2,labels2) -> b1 = b2 && List.eq ~eq:(Pair.eq (=) (List.eq ~eq)) labels1 labels2
  | TRecord fields1, TRecord fields2 -> List.eq ~eq:(Pair.eq (=) (Pair.eq (=) eq)) fields1 fields2
  | TApp(c1,typs1), TApp(c2,typs2) -> c1 = c2 && List.eq ~eq typs1 typs2
  | TAttr(attr1, ty1),  TAttr(attr2, ty2) -> attr1 = attr2 && ty1 = ty2
  | TModule sgn1, TModule sgn2 ->
      List.eq ~eq:(Pair.eq (=) eq) sgn1.sig_types sgn2.sig_types &&
      List.eq ~eq:eq_id sgn1.sig_values sgn2.sig_values
  | _ -> false


let rec is_instance_of ?(strict=false) ty1 ty2 =
  let eq = is_instance_of ~strict in
  let eq_id = Compare.eq_on Id.typ ~eq in
  match elim_tattr ty1, elim_tattr ty2 with
  | TVar({contents=None},_), TVar({contents=None},_) -> not strict
  | TVar({contents=Some ty1},_), TVar({contents=None},_) -> eq ty1 ty2
  | TBase b1, TBase b2 -> b1 = b2
  | TVar(x,_), TVar(y,_) -> x == y
  | TFun(x,ty1), TFun(y,ty2) -> eq_id x y && eq ty1 ty2
  | TFuns _, TFuns _ -> assert false
  | TTuple xs1, TTuple xs2 -> List.eq ~eq:eq_id xs1 xs2
  | TData s1, TData s2 -> s1 = s2
  | TVariant(b1,labels1), TVariant(b2,labels2) -> b1 = b2 && List.eq ~eq:(Pair.eq (=) (List.eq ~eq:is_instance_of)) labels1 labels2
  | TRecord fields1, TRecord fields2 -> List.eq ~eq:(Pair.eq (=) (Pair.eq (=) eq)) fields1 fields2
  | TApp(c1,typs1), TApp(c2,typs2) -> c1 = c2 && List.eq ~eq typs1 typs2
  | TModule sgn1, TModule sgn2 ->
      List.eq ~eq:(Pair.eq (=) eq) sgn1.sig_types sgn2.sig_types &&
      List.eq ~eq:(Compare.eq_on Id.typ ~eq) sgn1.sig_values sgn2.sig_values
  | _ -> false


let rec same_shape typ1 typ2 =
  let eq_id = Compare.eq_on Id.typ ~eq:same_shape in
  match elim_tattr typ1, elim_tattr typ2 with
  | TBase b1, TBase b2 -> b1 = b2
  | TVar({contents=None},_), TVar({contents=None},_) -> true
  | TVar({contents=Some typ1},_),TVar({contents=Some typ2},_) -> same_shape typ1 typ2
  | TFun(x1,typ1),TFun(x2,typ2) -> eq_id x1 x2 && same_shape typ1 typ2
  | TApp(c1,typs1), TApp(c2,typs2) -> c1=c2 && List.for_all2 same_shape typs1 typs2
  | TTuple xs1, TTuple xs2 -> List.eq ~eq:eq_id xs1 xs2
  | TData s1, TData s2 -> s1 = s2
  | TVariant(poly1,labels1), TVariant(poly2,labels2) ->
      poly1 = poly2 &&
      List.eq ~eq:(Pair.eq (=) (List.eq ~eq:same_shape)) labels1 labels2
  | TRecord fields1, TRecord fields2 -> List.eq ~eq:(Pair.eq (=) (Pair.eq (=) same_shape)) fields1 fields2
  | TModule sgn1, TModule sgn2 ->
      List.eq ~eq:(Pair.eq (=) same_shape) sgn1.sig_types sgn2.sig_types &&
      List.eq ~eq:eq_id sgn1.sig_values sgn2.sig_values
  | _ -> false





let rec app_typ typ typs =
  match typ,typs with
    | TFun(_,typ2), _::typs' -> app_typ typ2 typs'
    | _, [] -> typ
    | _ -> assert false

let tuple_num typ =
  match elim_tattr typ with
  | TTuple xs -> Some (List.length xs)
  | _ -> None

let proj_typ i typ =
  match elim_tattr typ with
  | TTuple xs -> Id.typ @@ List.nth xs i
  | typ when typ = typ_unknown -> typ_unknown
  | typ' -> invalid_arg @@ Format.asprintf "proj_typ %d (%a)" i print_init typ'

let fst_typ typ = proj_typ 0 typ
let snd_typ typ = proj_typ 1 typ

let ref_typ typ =
  match elim_tattr typ with
  | TApp("ref", [typ]) -> typ
  | typ when typ = typ_unknown -> typ_unknown
  | _ -> invalid_arg "ref_typ"

let list_typ typ =
  match elim_tattr typ with
  | TApp("list", [typ]) -> typ
  | typ when typ = typ_unknown -> typ_unknown
  | _ -> invalid_arg "list_typ"

let option_typ typ =
  match elim_tattr typ with
  | TApp("option", [typ]) -> typ
  | typ when typ = typ_unknown -> typ_unknown
  | _ -> invalid_arg "option_typ"

let array_typ typ =
  match elim_tattr typ with
  | TApp("array", [typ]) -> typ
  | typ when typ = typ_unknown -> typ_unknown
  | _ -> invalid_arg "array_typ"

let set_typ typ =
  match elim_tattr typ with
  | TApp("set", [typ]) -> typ
  | typ when typ = typ_unknown -> typ_unknown
  | _ -> invalid_arg "set_typ"

let rec has_pred = function
  | TBase _ -> false
  | TVar({contents=None},_) -> false
  | TVar({contents=Some typ},_) -> has_pred typ
  | TFun(x,typ) -> has_pred (Id.typ x) || has_pred typ
  | TApp(_,typs) -> List.exists has_pred typs
  | TTuple xs -> List.exists (has_pred -| Id.typ) xs
  | TData _ -> false
  | TAttr(attr,typ) ->
      has_pred typ || List.exists (function TAPred(_, _::_) -> true | _ -> false) attr
  | TFuns _ -> unsupported ""
  | TVariant(_,labels) -> List.exists (snd |- List.exists has_pred) labels
  | TRecord fields -> List.exists (snd |- snd |- has_pred) fields
  | TModule {sig_types} ->
      List.exists (snd |- has_pred) sig_types

let rec to_id_string = function
  | TBase TUnit -> "unit"
  | TBase TBool -> "bool"
  | TBase TInt -> "int"
  | TBase (TPrim s) -> s
  | TVar({contents=None},_) -> "abst"
  | TVar({contents=Some typ},_) -> to_id_string typ
  | TFun(x,typ) -> to_id_string (Id.typ x) ^ "__" ^ to_id_string typ
  | TApp(s, [typ]) -> to_id_string typ ^ s
  | TTuple xs ->
      let xs',x = List.decomp_snoc xs in
      let aux x s = to_id_string (Id.typ x) ^ "_x_" ^ s in
      List.fold_right aux xs' @@ to_id_string @@ Id.typ x
  | TData s -> s
  | TAttr(_,typ) -> to_id_string typ
  | TApp _ -> assert false
  | TFuns _ -> unsupported ""
  | TVariant(_,labels) ->
      labels
      |> List.take 2
      |> List.map fst
      |> String.join "_"
  | TRecord fields -> String.join "_" @@ List.map fst fields
  | TModule _ -> "module"


(* order of simpl types *)
let rec order typ =
  match typ with
  | TBase _ -> 0
  | TData _ -> 0
  | TVar({contents=None},_) -> assert false
  | TVar({contents=Some typ},_) -> order typ
  | TFun(x,typ) -> max (order (Id.typ x) + 1) (order typ)
  | TTuple xs -> List.fold_left (fun m x -> max m (order @@ Id.typ x)) 0 xs
  | TAttr(_,typ) -> order typ
  | _ -> assert false

let arg_var typ =
  match elim_tattr typ with
  | TFun(x,_) -> x
  | _ -> invalid_arg "arg_var"

let result_typ typ =
  match elim_tattr typ with
  | TFun(_,typ') -> typ'
  | _ -> invalid_arg "result_typ"

let decomp_ttuple typ =
  match elim_tattr typ with
  | TTuple xs -> List.map Id.typ xs
  | _ -> invalid_arg "decomp_ttuple"

let decomp_trecord typ =
  match elim_tattr typ with
  | TRecord fields -> fields
  | _ -> invalid_arg "decomp_trecord"

let decomp_tvariant ty =
  match elim_tattr ty with
  | TVariant(poly,labels) ->
      poly, labels
  | _ -> invalid_arg "decomp_tvariant"

let decomp_tmodule ty =
  match ty with
  | TModule sgn -> sgn
  | _ -> invalid_arg "decomp_tmodule"

let is_mutable_record typ =
  match typ with
  | TRecord fields ->
      List.exists (fun (_,(f,_)) -> f = Mutable) fields
  | _ -> invalid_arg "is_mutable_record"

let prim_base_types =
  ["char";
   "string";
   "float";
   "int32";
   "int64";
   "nativeint";
   "format4";
   "format6";
   "Format.format";
   "Format.formatter"]

let rec remove_arg_at i ty =
  match ty with
  | TFun(_, typ) when i = 0 -> typ
  | TFun(x, typ) -> TFun(x, remove_arg_at (i-1) typ)
  | _ -> assert false

let decomp_tattr ty =
  match ty with
  | TAttr(attrs, ty') -> attrs, ty'
  | _ -> [], ty

let decomp_tdata ty =
  match ty with
  | TData s -> s
  | _ -> invalid_arg "Type.decomp_tdata"

let is_tvar ty =
  match ty with
  | TVar({contents=None},_) -> true
  | _ -> false

let add_tattr attr ty =
  match ty with
  | TAttr(attrs, ty') when not (List.mem attr attrs) -> TAttr(attr::attrs, ty')
  | _ -> TAttr([attr], ty)

let filter_map_attr f =
  let aux tr ty =
    match ty with
    | TAttr(attr,typ) ->
        let attr' = List.filter_map f attr in
        Some (TAttr(attr', tr typ))
    | _ -> None
  in
  fun ty -> make_trans aux ty

let map_attr f ty = filter_map_attr (Option.some -| f) ty

let elim_tid l ty =
  filter_map_attr (function TAId(l',_) when l = l' -> None | a -> Some a) ty

let rec types_in_signature {sig_types; sig_values} =
  let types =
    let aux x =
      try
        types_in_module ~add_prefix:true x
      with Invalid_argument _ -> []
    in
    List.flatten_map aux sig_values
  in
  sig_types @ types

and types_in_module ?(add_prefix=false) m =
  try
    Id.typ m
    |> decomp_tmodule
    |> types_in_signature
    |&add_prefix&> List.map (Pair.map_fst @@ Id.add_module_prefix_string ~m)
  with Invalid_argument _ -> invalid_arg "constrs_defined_in_module"

let fields_in_declaration decls =
  let aux (_,ty) =
    match ty with
    | TRecord fields -> List.map fst fields
    | _ -> []
  in
  List.flatten_map aux decls

let rec fields_in_signature sgn =
  let constrs =
    let aux x =
      try
        fields_in_module ~add_prefix:true x
      with Invalid_argument _ -> []
    in
    List.flatten_map aux sgn.sig_values
  in
  constrs @ fields_in_declaration sgn.sig_types

and fields_in_module ?(add_prefix=false) m =
  try
    Id.typ m
    |> decomp_tmodule
    |> fields_in_signature
    |&add_prefix&> List.map (Id.add_module_prefix_string ~m)
  with Invalid_argument _ -> invalid_arg "constrs_defined_in_module"

let constrs_in_declaration decls =
  let aux (_,ty) =
    match ty with
    | TVariant(false, labels) -> List.map fst labels
    | _ -> []
  in
  List.flatten_map aux decls

let rec constrs_in_signature sgn =
  let constrs =
    let aux x =
      try
        constrs_in_module ~add_prefix:true x
      with Invalid_argument _ -> []
    in
    List.flatten_map aux sgn.sig_values
  in
  constrs @ constrs_in_declaration sgn.sig_types

and constrs_in_module ?(add_prefix=false) m =
  try
    Id.typ m
    |> decomp_tmodule
    |> constrs_in_signature
    |&add_prefix&> List.map (Id.add_module_prefix_string ~m)
  with Invalid_argument _ -> invalid_arg "constrs_defined_in_module"

let rec values_in_signature ?(extract_module=true) {sig_values} =
  let values =
    if extract_module then
      let aux x =
        try
          values_in_module ~add_prefix:true ~extract_module x
        with Invalid_argument _ -> []
      in
      List.flatten_map aux sig_values
    else []
  in
  values @ sig_values

and values_in_module ?(add_prefix=false) ?(extract_module=true) m =
  try
    Id.typ m
    |> decomp_tmodule
    |> values_in_signature ~extract_module
    |&add_prefix&> List.map (Id.add_module_prefix ~m)
  with Invalid_argument _ -> invalid_arg "values_in_module"


module Ty = struct
  let unit = TBase TUnit
  let bool = TBase TBool
  let int = TBase TInt
  let prim s = TBase (TPrim s)
  let fun_ = make_tfun
  let funs tys ty = List.fold_right make_tfun tys ty
  let pfun = make_ptfun
  let tuple = make_ttuple
  let pair = make_tpair
  let ( * ) = pair
  let list = make_tlist
  let ref = make_tref
  let option = make_toption
  let array = make_tarray
  let set = make_tset
end
