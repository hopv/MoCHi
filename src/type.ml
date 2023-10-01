open Util

type base =
  | TUnit
  | TBool
  | TInt

and 'a tid = 'a t Id.t
and tconstr = unit Id.t (* for type constructors *)
and label = unit Id.t (* for record types *)
and constr = unit Id.t (* for variant types *)
and path =
  | LId of unit Id.t
  | LDot of path * string (* string must be normalized by [Id.normalize_name] *)
  | LApp of path * path

and 'a t =
  | TBase of base
  | TVar of bool * 'a t option ref * int (* Boolean denotes weakness, The third argument (counter) is used just for printing *)
  | TFun of 'a tid * 'a t
  | TFuns of 'a tid list * 'a t (* Just for fair-termination. TODO: Refactor *)
  | TTuple of 'a tid list
  | TVariant of variant_kind * 'a row list (** true means polymorphic variant *)
  | TRecord of (label * (mutable_flag * 'a t)) list
  | TConstr of path * 'a t list
  | TAttr of 'a attr list * 'a t
  | TModSig of 'a signature
  | TModLid of path (* Only for external modules/functors; see #2 of memo.md *)
  | TPackage of 'a t
  | TPoly of 'a t option ref list * 'a t
  | TConstraint of 'a t * ('a t * 'a t) list (* the left in an list element must be TVar *)
  | TOpen (* extensible variant type *)

and variant_kind =
  | VNonPoly
  | VPoly of
      {closed : bool;
       tvar : unit option; (* TODO *)
       lower : constr list option } (* TODO *)

and 'a row =
  {row_constr : constr;
   row_args : 'a t list;
   row_ret : 'a t option}
and mutable_flag = Immutable | Mutable

and 'a attr =
  | TAPred of 'a tid * 'a list (* TAPred occur at most ones *)
  | TAPredShare of int
  | TARefPred of 'a tid * 'a (* TARefPred occur at most ones *)
  | TAPureFun
  | TAEffect of effect list
  | TAId of string * int
  | TARaise of 'a t

and effect = EVar of int | EEvent | ENonDet | EDiv | EExcep

and 'a signature =
  {sig_types: 'a declaration list;
   sig_ext: 'a ext list;
   sig_values: 'a tid list}

and 'a declaration = 'a decl_item list
and 'a decl_item = (tconstr * ('a params * 'a t))

and 'a ext = path * ('a params * 'a ext_row)
and 'a ext_row =
  {ext_row_path : path; (* I have forgotten why we use path here instead of tconstr *)
   ext_row_args : 'a t list;
   ext_row_ret : 'a t option}

and 'a params = 'a t list

and 'a extension =
  | Ext_type of 'a ext          (** [type t += ...] *)
  | Ext_rebind of constr * path (** [exception A = B] *) (* TODO: type t += A = B *)
[@@deriving show {with_path = false}]

let _LId c = LId (Id.set_typ c ())
let _LDot path s = LDot(path, s)
let _LApp path1 path2 = LApp(path1, path2)

let _TBase b = TBase b
let _TVar b r n = TVar(b, r, n)
let _TFun x ty = TFun(x, ty)
let _TFuns xs ty = TFuns(xs, ty)
let _TTuple xs = TTuple xs
let _TVariant b labels = TVariant(b, labels)
let _TRecord fields = TRecord fields
let _TConstr c tys = TConstr(c, tys)
let _TConstraint ty cs =
  if cs = [] then
    ty
  else
    TConstraint(ty, cs)
let _TAttr attr ty =
  if attr = [] then
    ty
  else
    match ty with
    | TAttr(attr', ty') -> TAttr(List.Set.(attr + attr'), ty')
    | _ -> TAttr(attr, ty)
let _TModSig sgn = TModSig sgn
let _TModLid sgn = TModLid sgn
let _TPackage ty = TPackage ty
let _TPoly vars ty = TPoly(vars, ty)

let _Ext_type ext = Ext_type ext
let _Ext_rebind c p = Ext_rebind(c, p)

let row_constr {row_constr;_} = row_constr
let row_args {row_args;_} = row_args
let row_ret {row_ret;_} = row_ret

let rec elim_tattr = function
  | TAttr(_,typ) -> elim_tattr typ
  | typ -> typ

let types_of_format = ["CamlinternalFormatBasics.format6"; "Stdlib.format4"; "Stdlib.format6"]

module Val = struct
  let _LId        = function LId x             -> Some x          | _ -> None
  let _TBase      = function TBase b           -> Some b          | _ -> None
  let _TVar       = function TVar(b, r, n)     -> Some (b, r, n)  | _ -> None
  let _TFun       = function TFun(x,ty)        -> Some (x, ty)    | _ -> None
  let _TFuns      = function TFuns(xs,ty)      -> Some (xs, ty)   | _ -> None
  let _TTuple     = function TTuple xs         -> Some xs         | _ -> None
  let _TVariant   = function TVariant(b, rows) -> Some (b, rows)  | _ -> None
  let _TRecord    = function TRecord fields    -> Some fields     | _ -> None
  let _TConstr    = function TConstr(c, tys)   -> Some (c, tys)   | _ -> None
  let _TAttr      = function TAttr(attr, ty)   -> Some (attr, ty) | _ -> None
  let _TModSig    = function TModSig sgn       -> Some sgn        | _ -> None
  let _TModLid    = function TModLid m         -> Some m          | _ -> None
  let _TPackage   = function TPackage ty       -> Some ty         | _ -> None
  let _TPoly      = function TPoly(r,ty)       -> Some (r, ty)    | _ -> None
  let _Ext_type   = function Ext_type ext      -> Some ext        | _ -> None
  let _Ext_rebind = function Ext_rebind(c,p)   -> Some (c, p)     | _ -> None
end

module ValE = struct
  let _LId        = function LId x             -> x        | _ -> [%invalid_arg]
  let _TBase      = function TBase b           -> b        | _ -> [%invalid_arg]
  let _TVar       = function TVar(b, r, n)     -> b, r, n  | _ -> [%invalid_arg]
  let _TFun       = function TFun(x,ty)        -> x, ty    | _ -> [%invalid_arg]
  let _TFuns      = function TFuns(xs,ty)      -> xs, ty   | _ -> [%invalid_arg]
  let _TTuple     = function TTuple xs         -> xs       | _ -> [%invalid_arg]
  let _TVariant   = function TVariant(b, rows) -> b, rows  | _ -> [%invalid_arg]
  let _TRecord    = function TRecord fields    -> fields   | _ -> [%invalid_arg]
  let _TConstr    = function TConstr(c, tys)   -> c, tys   | _ -> [%invalid_arg]
  let _TAttr      = function TAttr(attr, ty)   -> attr, ty | _ -> [%invalid_arg]
  let _TModSig    = function TModSig sgn       -> sgn      | _ -> [%invalid_arg]
  let _TModLid    = function TModLid m         -> m        | _ -> [%invalid_arg]
  let _TPackage   = function TPackage ty       -> ty       | _ -> [%invalid_arg]
  let _TPoly      = function TPoly(r,ty)       -> r, ty    | _ -> [%invalid_arg]
  let _Ext_type   = function Ext_type ext      -> ext      | _ -> [%invalid_arg]
  let _Ext_rebind = function Ext_rebind(c,p)   -> c, p     | _ -> [%invalid_arg]
end

module Is = struct
  let _LId        = function LId _        -> true | _ -> false
  let _TBase      = function TBase _      -> true | _ -> false
  let _TVar       = function TVar _       -> true | _ -> false
  let _TFun       = function TFun _       -> true | _ -> false
  let _TFuns      = function TFuns _      -> true | _ -> false
  let _TTuple     = function TTuple _     -> true | _ -> false
  let _TVariant   = function TVariant _   -> true | _ -> false
  let _TRecord    = function TRecord _    -> true | _ -> false
  let _TConstr    = function TConstr _    -> true | _ -> false
  let _TAttr      = function TAttr _      -> true | _ -> false
  let _TModSig    = function TModSig _    -> true | _ -> false
  let _TModLid    = function TModLid _    -> true | _ -> false
  let _TPackage   = function TPackage _   -> true | _ -> false
  let _TPoly      = function TPoly _      -> true | _ -> false
  let _Ext_type   = function Ext_type _   -> true | _ -> false
  let _Ext_rebind = function Ext_rebind _ -> true | _ -> false

  let poly_variant = function TVariant(VPoly _, _) -> true | _ -> false
end

module Val' = struct
  let _TBase x    = elim_tattr x |> Val._TBase
  let _TVar x     = elim_tattr x |> Val._TVar
  let _TFun x     = elim_tattr x |> Val._TFun
  let _TFuns x    = elim_tattr x |> Val._TFuns
  let _TTuple x   = elim_tattr x |> Val._TTuple
  let _TVariant x = elim_tattr x |> Val._TVariant
  let _TRecord x  = elim_tattr x |> Val._TRecord
  let _TConstr x  = elim_tattr x |> Val._TConstr
  let _TAttr x    = elim_tattr x |> Val._TAttr
  let _TModSig x  = elim_tattr x |> Val._TModSig
  let _TModLid x  = elim_tattr x |> Val._TModLid
  let _TPackage x = elim_tattr x |> Val._TPackage
  let _TPoly x    = elim_tattr x |> Val._TPoly
end

module ValE' = struct
  let _TBase x    = elim_tattr x |> ValE._TBase
  let _TVar x     = elim_tattr x |> ValE._TVar
  let _TFun x     = elim_tattr x |> ValE._TFun
  let _TFuns x    = elim_tattr x |> ValE._TFuns
  let _TTuple x   = elim_tattr x |> ValE._TTuple
  let _TVariant x = elim_tattr x |> ValE._TVariant
  let _TRecord x  = elim_tattr x |> ValE._TRecord
  let _TConstr x  = elim_tattr x |> ValE._TConstr
  let _TAttr x    = elim_tattr x |> ValE._TAttr
  let _TModSig x  = elim_tattr x |> ValE._TModSig
  let _TModLid x  = elim_tattr x |> ValE._TModLid
  let _TPackage x = elim_tattr x |> ValE._TPackage
  let _TPoly x    = elim_tattr x |> ValE._TPoly
end

module Is' = struct
  let _TBase x    = elim_tattr x |> Is._TBase
  let _TVar x     = elim_tattr x |> Is._TVar
  let _TFun x     = elim_tattr x |> Is._TFun
  let _TFuns x    = elim_tattr x |> Is._TFuns
  let _TTuple x   = elim_tattr x |> Is._TTuple
  let _TVariant x = elim_tattr x |> Is._TVariant
  let _TRecord x  = elim_tattr x |> Is._TRecord
  let _TConstr x  = elim_tattr x |> Is._TConstr
  let _TAttr x    = elim_tattr x |> Is._TAttr
  let _TModSig x  = elim_tattr x |> Is._TModSig
  let _TModLid x  = elim_tattr x |> Is._TModLid
  let _TPackage x = elim_tattr x |> Is._TPackage
  let _TPoly x    = elim_tattr x |> Is._TPoly

  let poly_variant x = elim_tattr x |> Is.poly_variant
end

let empty_signature = {sig_types=[]; sig_ext=[]; sig_values=[]}

let counter = ref 0
let new_tvar_aux b =
  let ty = TVar(b, ref None, !counter) in
  incr counter;
  ty
let new_tvar () = new_tvar_aux false
let new_tvar_weak () = new_tvar_aux true

let copy_tvar ty =
  match ty with
  | TVar(true, {contents=None}, _) -> ty
  | TVar(false, {contents=None}, n) -> TVar(false, ref None, n)
  | _ -> invalid_arg "Type.copy_tvar"

let make_trans f =
  let rec trans ty =
    match f trans ty with
    | None ->
        let tr_row {row_constr; row_args; row_ret} =
          let row_args = List.map trans row_args in
          let row_ret = Option.map trans row_ret in
          {row_constr; row_args; row_ret}
        in
        let tr_ext_row {ext_row_path; ext_row_args; ext_row_ret} =
          let ext_row_args = List.map trans ext_row_args in
          let ext_row_ret = Option.map trans ext_row_ret in
          {ext_row_path; ext_row_args; ext_row_ret}
        in
        begin match ty with
        | TBase b -> TBase b
        | TVar(_,{contents=Some ty},_) -> trans ty
        | TVar(b,r,id) -> TVar(b,r,id)
        | TFun(x,ty) -> TFun(Id.map_typ trans x, trans ty)
        | TConstr(c,tys) -> TConstr(c, List.map trans tys)
        | TTuple xs -> TTuple (List.map (Id.map_typ trans) xs)
        | TAttr(attr,ty) -> TAttr(attr, trans ty)
        | TFuns(xs,ty) -> TFuns(List.map (Id.map_typ trans) xs, trans ty)
        | TVariant(poly,rows) -> TVariant(poly, List.map tr_row rows)
        | TRecord fields -> TRecord (Fmap.(list (snd (snd trans))) fields)
        | TModSig {sig_types; sig_values; sig_ext} ->
            let sig_values = List.map (Id.map_typ trans) sig_values in
            let sig_types = Fmap.(list (list (snd (snd trans)))) sig_types in
            let sig_ext = Fmap.(list (snd (snd tr_ext_row))) sig_ext in
            TModSig {sig_types; sig_values; sig_ext}
        | TModLid m -> TModLid m
        | TPackage ty -> TPackage (trans ty)
        | TPoly(vars,ty) -> TPoly(vars, trans ty)
        | TConstraint(ty,cs) -> TConstraint(trans ty, Fmap.(list (trans * trans)) cs)
        | TOpen -> TOpen
        end
    | Some ty -> ty
  in
  trans

let make_reduce ~f ~app:(++) ~default =
  let rec reduce ty =
    let reduce_var x = reduce @@ Id.typ x in
    let reduce_list red xs = List.fold_left (fun acc x -> acc ++ red x) default xs in
    match f reduce ty with
    | None ->
        begin match ty with
        | TBase _ -> default
        | TVar(_,{contents=Some ty},_) -> reduce ty
        | TVar _ -> default
        | TFun(x,ty) -> reduce_var x ++ reduce ty
        | TConstr(_,tys) -> reduce_list reduce tys
        | TTuple xs -> reduce_list reduce_var xs
        | TAttr(_,ty) -> reduce ty
        | TFuns(xs,ty) -> reduce_list reduce_var xs ++ reduce ty
        | TVariant(_, rows) ->
            let rd_row {row_constr=_; row_args; row_ret} =
              reduce_list reduce row_args ++ Option.fold ~none:default ~some:reduce row_ret
            in
            reduce_list rd_row rows
        | TRecord fields -> reduce_list (snd |- snd |- reduce) fields
        | TModSig {sig_types; sig_values} ->
            reduce_list (reduce_list (reduce -| snd -| snd)) sig_types
            ++ reduce_list reduce_var sig_values
        | TModLid _ -> default
        | TPackage ty -> reduce ty
        | TPoly(_, ty) -> reduce ty
        | TConstraint(ty,cs) -> reduce ty ++ reduce_list (fun (p,ty) -> reduce p ++ reduce ty) cs
        | TOpen -> default
        end
    | Some x -> x
  in
  reduce

let make_find (type a) (f : (a t -> unit) -> a t -> bool) =
  let exception Found of a t in
  let rec find ty =
    let find_var x = find @@ Id.typ x in
    if f find ty then
      raise (Found ty)
    else
      match ty with
      | TBase _ -> ()
      | TVar(_,{contents=Some ty},_) -> find ty
      | TVar _ -> ()
      | TFun(x,ty) -> find_var x; find ty
      | TConstr(_,tys) -> List.iter find tys
      | TTuple xs -> List.iter find_var xs
      | TAttr(_,ty) -> find ty
      | TFuns(xs,ty) -> List.iter find_var xs; find ty
      | TVariant(_, rows) ->
          let rd_row {row_constr=_; row_args; row_ret} =
            List.iter find row_args;
            Option.iter find row_ret
          in
          List.iter rd_row rows
      | TRecord fields -> List.iter (snd |- snd |- find) fields
      | TModSig {sig_types; sig_values} ->
          List.iter (List.iter (find -| snd -| snd)) sig_types;
          List.iter find_var sig_values
      | TModLid _ -> ()
      | TPackage ty -> find ty
      | TPoly(_, ty) -> find ty
      | TConstraint(ty, cs) ->
          find ty;
          List.iter (fun (p,ty) -> find p; find ty) cs
      | TOpen -> ()
  in
  fun ty -> match find ty with () -> None | exception Found ty -> Some ty

let make_fold f =
  let rec fold acc ty =
    let wrap c ~fld ~acc ty = Pair.map_snd c @@ fld ~acc ty in
    let wrap_list c ~fld ~acc tys =
      List.fold_right (fun ty (acc,tys) -> let acc,ty' = fld ~acc ty in acc,ty'::tys) tys (acc,[])
      |> Pair.map_snd c
    in
    let wrap_pair c ~fld1 ~fld2 ~acc x y =
      let acc,x' = fld1 ~acc x in
      let acc,y' = fld2 ~acc y in
      acc, c x' y'
    in
    let fld ~acc ty = fold acc ty in
    let fld_option ~fld ~acc x =
      match x with
      | None -> acc, None
      | Some y ->
          let acc,y' = fld ~acc y in
          acc, Some y'
    in
    let fld_var ~acc x = wrap (Id.set_typ x) ~fld ~acc @@ Id.typ x in
    let fld_list ~fld ~acc xs = wrap_list Fun.id ~fld ~acc xs in
    match f fold acc ty with
    | None ->
        begin match ty with
        | TBase _ -> acc, ty
        | TVar(_,{contents=Some ty},_) -> fold acc ty
        | TVar(b,r,id) -> acc, TVar(b,r,id)
        | TFun(x,ty) -> wrap_pair _TFun ~fld1:fld_var ~fld2:fld ~acc x ty
        | TConstr(c,tys) -> wrap (_TConstr c) ~fld:(fld_list ~fld:fld) ~acc tys
        | TTuple xs -> wrap _TTuple ~fld:(fld_list ~fld:fld_var) ~acc xs
        | TAttr(attr,ty) -> wrap (_TAttr attr) ~fld ~acc ty
        | TFuns(xs,ty) -> wrap_pair _TFuns ~fld1:(fld_list ~fld:fld_var) ~fld2:fld ~acc xs ty
        | TVariant(poly,rows) ->
            let fld_row ~acc {row_constr; row_args; row_ret} =
              let acc,row_args = fld_list ~fld ~acc row_args in
              let acc,row_ret = fld_option ~fld ~acc row_ret in
              acc, {row_constr; row_args; row_ret}
            in
            let acc,rows = fld_list ~fld:fld_row ~acc rows in
            acc, TVariant(poly, rows)
        | TRecord fields ->
            let fld_label ~acc (s,(flag,ty)) = wrap (Pair.pair s -| Pair.pair flag) ~fld ~acc ty in
            wrap_list _TRecord ~fld:fld_label ~acc fields
        | TModSig {sig_types; sig_values; sig_ext} ->
            let acc,sig_types =
              let fld_ty ~acc (s,(params,ty)) = wrap (Pair.pair s -| Pair.pair params) ~fld ~acc ty in
              fld_list ~fld:(fld_list ~fld:fld_ty) ~acc sig_types
            in
            let acc,sig_ext =
              fld_list ~acc sig_ext
                ~fld:(fun ~acc (s, (params, {ext_row_path; ext_row_args; ext_row_ret})) ->
                  let acc,ext_row_args = fld_list ~fld ~acc ext_row_args in
                  let acc,ext_row_ret = fld_option ~fld ~acc ext_row_ret in
                  acc, (s, (params, {ext_row_path; ext_row_args; ext_row_ret})))
            in
            let acc,sig_values = fld_list ~fld:fld_var ~acc sig_values in
            acc, TModSig {sig_types; sig_values; sig_ext}
        | TModLid _ -> acc, ty
        | TPackage ty -> wrap _TPackage ~fld ~acc ty
        | TPoly(vars, ty) -> wrap (_TPoly vars) ~fld ~acc ty
        | TConstraint(ty, cs) ->
            let acc,ty' = fld ~acc ty in
            let acc,cs' =
              fld_list ~acc cs
                ~fld:(fun ~acc (p,ty) ->
                  let acc,p' = fld ~acc p in
                  let acc,ty' = fld ~acc ty in
                  acc, (p', ty'))
            in
            acc, TConstraint(ty', cs')
        | TOpen -> acc, ty
        end
    | Some (acc,ty) -> acc, ty
  in
  fold

(** Checks syntactic equality not semantical equality (e.g., [int List.t] differs from [int list]) *)
let rec equal ?(env=[]) ty1 ty2 =
  let eq = equal ~env in
  match ty1, ty2 with
  | TBase b1, TBase b2 -> b1 = b2
  | TVar(_, {contents = Some ty1}, _), _ -> eq ty1 ty2
  | _, TVar(_, {contents = Some ty2}, _) -> eq ty1 ty2
  | TVar(b1, r1, _), TVar(b2, r2, _) ->
      b1 = b2 && (* TODO: need? *)
      (r1 == r2 || List.exists (fun (r3,r4) -> r1 == r3 && r2 == r4 || r1 == r4 && r2 == r3) env)
  | TFun(x1, ty1), TFun(x2, ty2) -> eq (Id.typ x1) (Id.typ x2) && eq ty1 ty2
  | TFuns _, _
  | _, TFuns _ -> [%unsupported]
  | TTuple xs1, TTuple xs2 -> List.equal (Compare.eq_on ~eq Id.typ) xs1 xs2
  | TVariant(vk1, rows1), TVariant(vk2, rows2) ->
      let b1 =
        match vk1, vk2 with
        | VNonPoly, VNonPoly -> true
        | VPoly {closed=b1}, VPoly {closed=b2} -> b1 = b2 (* TODO *)
        | _ -> false
      in
      b1 && List.equal equal_row rows1 rows2
  | TRecord fields1, TRecord fields2 -> List.equal (fun (l1,(f1,ty1)) (l2,(f2,ty2)) -> l1 = l2 && f1 = f2 && eq ty1 ty2) fields1 fields2
  | TConstr(p1,tys1), TConstr(p2,tys2) -> equal_path p1 p2 && List.equal eq tys1 tys2
  | TAttr(attrs1, ty1), TAttr(attrs2, ty2) -> attrs1 = attrs2 && eq ty1 ty2
  | TModSig sgn1, TModSig sgn2 -> equal_signature ~env sgn1 sgn2
  | TModLid m1, TModLid m2 -> equal_path m1 m2
  | TPackage ty1, TPackage ty2 -> eq ty1 ty2
  | TPoly(ps1, ty1), TPoly(ps2, ty2) -> equal ~env:(List.combine ps1 ps2 @@@ env) ty1 ty2
  | _ -> false

and equal_row ?(env=[]) row1 row2 =
  Id.eq row1.row_constr row2.row_constr &&
  List.equal (equal ~env) row1.row_args row2.row_args &&
  Option.equal (equal ~env) row1.row_ret row2.row_ret

and equal_signature ?(env=[]) sgn1 sgn2 =
  let eq = equal ~env in
  let eq_decl_item (c1,(ps1,ty1)) (c2,(ps2,ty2)) =
    Id.eq c1 c2 && List.equal eq ps1 ps2 && eq ty1 ty2
  in
  List.equal (List.equal eq_decl_item) sgn1.sig_types sgn2.sig_types &&
  List.equal (fun x y -> Id.eq x y && eq (Id.typ x) (Id.typ y)) sgn1.sig_values sgn2.sig_values &&
  List.equal (=) sgn1.sig_ext sgn1.sig_ext (* TODO *)

and equal_path ?(eq=Id.eq) lid1 lid2 =
  match lid1, lid2 with
  | LId id1, LId id2 -> eq id1 id2
  | LDot(p1,s1), LDot(p2,s2) -> equal_path ~eq p1 p2 && s1 = s2
  | LApp(p11,p12), LApp(p21,p22) -> equal_path ~eq p11 p21 && equal_path ~eq p12 p22
  | _ -> false

let eq x y = equal ~env:[] x y




let copy_tvar_typ =
  let fold fld env ty =
    match ty with
    | TVar(false, ({contents=None} as r), _) ->
        let env, ty =
          match List.assq_opt r env with
          | None ->
              let ty = !!new_tvar in
              (r, ty)::env, ty
          | Some ty -> env, ty
        in
        Some (env, ty)
    | TPoly(params, ty1) ->
        let env,ty1' = fld env ty1 in
        let params' =
          params
          |> List.map (fun r ->
                 match List.assq r env with
                 | TVar (_, r',_ ) -> r'
                 | _
                 | exception Not_found ->
                     Format.eprintf "ty: %a@." (pp Fun.ignore2)  ty;
                     assert false)
        in
        Some (env, TPoly(params', ty1'))
    | _ -> None
  in
  fun ?(env=[]) ty -> make_fold fold env ty

let ref_of_tvar typ =
  match typ with
  | TVar(_, r, _) -> r
  | _ -> invalid_arg "Type.ref_of_tvar"

let copy_tconstr_params (params,ty) =
  let env = List.map (Pair.make ref_of_tvar copy_tvar) params in
  let params' = List.map snd env in
  let env',ty' = copy_tvar_typ ~env ty in (* (params,ty) is assumed to be closed??? *)
  env', (params', ty')

let copy_tconstr_params_list params tys =
  let dummy = TBase TUnit in
  let env,(params',_) = copy_tconstr_params (params, dummy) in
  let env',tys' =
    List.L.fold_right ~init:(env,[]) tys ~f:(fun ty (env,acc) ->
        let env,ty' = copy_tvar_typ ~env ty in
        env, ty'::acc)
  in
  env', params', tys'

let tconstr ?id ?(attr=[]) name =
  match id with
  | None -> Id.new_var ~name ~attr ()
  | Some id -> Id.make ~id name ~attr ()
let path ?id ?attr name : path = LId (tconstr ?id ?attr name)
let prim_path name = path ~id:0 ~attr:[Id.Primitive] name

module Path = struct
  type t = path

  let _LId x = LId (Id.set_typ x ())
  let _LDot lid s = LDot(lid, s)
  let _LApp lid1 lid2 = LApp(lid1, lid2)

  let id_of lid =
    match lid with
    | LId x -> x
    | _ -> [%invalid_arg]

  let id_opt lid =
    match lid with
    | LId x -> Some x
    | _ -> None

  let rec cons m lid =
    match lid with
    | LId x -> LDot(LId (Id.set_typ m ()), Id.name x)
    | LDot(p,s) -> LDot(cons m p, s)
    | _ -> [%invalid_arg]

  let rec append path1 path2 =
    match path2 with
    | LId x -> LDot(path1, Id.name x)
    | LDot(path2',s) -> LDot(append path1 path2', s)
    | LApp _ -> [%invalid_arg]

  let append_opt path1 path2 =
    match path1 with
    | None -> path2
    | Some path1' -> append path1' path2

  let rec head lid =
    match lid with
    | LId x -> x
    | LDot(p, _) -> head p
    | LApp _ -> [%invalid_arg]

  let rec last lid =
    match lid with
    | LId x -> Id.name x
    | LDot(_, s) -> s
    | LApp(_, lid2) -> last lid2

  let rec print fm lid =
    match lid with
    | LId x ->
        let s =
          if !Flag.Print.var_id then
            Id.to_string x
          else
            Id.name x
        in
        Format.fprintf fm "%s" s
    | LDot(p,s) -> Format.fprintf fm "%a.%s" print p s
    | LApp(p1,p2) -> Format.fprintf fm "%a(%a)" print p1 print p2
  let pp = pp_path

  let to_string lid = Format.asprintf "%a" print lid
  let name = to_string

  let rec of_string s =
    if s = "" then [%invalid_arg];
    if String.last s = ')' then
      unsupported "%s" __FUNCTION__
    else
      match String.rsplit s ~by:"." with
      | exception Not_found -> LId (Id.make s ())
      | s1, s2 -> LDot(of_string s1, s2)

  let rec flatten acc = function
    | LId s -> s, acc
    | LDot(lid, s) -> flatten (s :: acc) lid
    | LApp(_, _) -> [%invalid_arg]
  let flatten lid = flatten [] lid

  let rec head lid =
    match lid with
    | LId id -> id
    | LDot(p, _) -> head p
    | LApp _ -> [%invalid_arg]

  let equal = equal_path
  let eq = equal

  let rec compare lid1 lid2 =
    match lid1, lid2 with
    | LId _, (LDot _ | LApp _) -> -1
    | LDot _, LApp _ -> -1
    | LApp _, (LDot _ | LId _) -> 1
    | LDot _, LId _ -> 1
    | LId id1, LId id2 -> Id.compare id1 id2
    | LDot(p1,s1), LDot(p2,s2) -> Compare.dict compare p1 p2 Stdlib.compare s1 s2
    | LApp(p11,p12), LApp(p21,p22) -> Compare.dict compare p11 p21 compare p12 p22

  let rec map ~f ?(g=Fun.id) lid =
    match lid with
    | LId id -> LId (f id)
    | LDot(lid', s) -> LDot(map ~f ~g lid', g s)
    | LApp(lid1, lid2) -> LApp(map ~f ~g lid1, map ~f ~g lid2)

  let map_name g lid = map ~f:(Id.map_name g) ~g lid

  let rec is_external lid =
    match lid with
    | LId id -> Id.is_external id
    | LDot(p, _)
    | LApp(p, _) -> is_external p

  let rec is_primitive lid =
    match lid with
    | LId id -> Id.is_primitive id
    | LDot(p, _)
    | LApp(p, _) -> is_primitive p

  let rec decomp_lapp lid =
    match lid with
    | LId _
    | LDot _ -> lid, []
    | LApp(lid1,lid2) ->
        let lid1',lids = decomp_lapp lid1 in
        lid1', lids@[lid2]

  let rec has_app path =
    match path with
    | LId _ -> false
    | LDot(path', _) -> has_app path'
    | LApp _ -> true

  let rec is_prefix path1 path2 =
    if path1 = path2 then
      true
    else
      match path2 with
      | LDot(path2', _) -> is_prefix path1 path2'
      | _ -> false

  let rec subst_head_map map path =
    let sbst = subst_head_map map in
    match path with
    | LId x -> Id.List.assoc_default path x map
    | LDot(path1,s) -> LDot(sbst path1,s)
    | LApp(path1,path2) -> LApp(sbst path1, sbst path2)

  let subst_head x lid path = subst_head_map [x,lid] path

  let rec subst_prefix_map map path =
    let sbst = subst_prefix_map map in
    match path with
    | LId _ -> path
    | LDot(path1,s) ->
        let path1' = List.assoc_default ~eq:(eq ~eq:(Compare.eq_on Id.name)) path1 path1 map in
        LDot(path1', s)
    | LApp(path1,path2) -> LApp(sbst path1, sbst path2)

  let (=) = eq
end

module C = struct
  let obj = prim_path "obj"
  let class_ = prim_path "class"
  let list = prim_path "list"
  let set = prim_path "set"
  let ref = prim_path "ref"
  let option = prim_path "option"
  let array = prim_path "array"
  let lazy_ = prim_path "lazy"
  let unknown = prim_path "???"
  let abst = prim_path "abst"
  let exn = prim_path "exn"
  let char = prim_path "char"
  let float = prim_path "float"
  let string = prim_path "string"
  let result = prim_path "X"

  let is_obj = Path.eq obj
  let is_class_ = Path.eq class_
  let is_list = Path.eq list
  let is_set = Path.eq set
  let is_ref = Path.eq ref
  let is_option = Path.eq option
  let is_array = Path.eq array
  let is_lazy_ = Path.eq lazy_
  let is_unknown = Path.eq unknown
  let is_abst = Path.eq abst
  let is_exn = Path.eq exn
  let is_char = Path.eq char
  let is_float = Path.eq float
  let is_string = Path.eq string
  let is_result = Path.eq result

  let base_prims =
    [char;
     float;
     string]

  let prims =
    [obj;
     class_;
     list;
     set;
     ref;
     option;
     array;
     lazy_;
     unknown;
     abst;
     exn;
     result] @ base_prims
end

(** [instantiate p1 p2] instantiates [p1] by [p2] ([p1] must be a type variable) *)
let instantiate p1 p2 =
  match p1 with
  | TVar(_, ({contents=None} as r), _) -> r := Some p2
  | _ -> [%invalid_arg]

exception Sig_of_Lid of path
type 'a mod_env = 'a mod_typ list
and 'a mod_typ = unit Id.t * 'a t
[@@deriving show]

(* TODO: Support TConstr _ *)
let rec sig_of_mod_typ ~(env : 'a mod_env) ty =
  match elim_tattr ty with
  | TModSig sgn -> sgn
  | TModLid (LId m) ->
      (try
         let ty = Id.List.assoc m env in
         if ty = TModLid (LId m) then [%invalid_arg];
         sig_of_mod_typ ~env ty
       with Not_found -> [%invalid_arg])
  | TModLid (LDot _ as m) -> raise (Sig_of_Lid m)
  | TModLid (LApp _) -> [%invalid_arg]
  | TConstr(_, []) -> [%unsupported]
  | _ -> [%invalid_arg]
let sig_of_id ~(env : 'a mod_env) m = sig_of_mod_typ ~env @@ Id.typ m

let is_mod_typ ty =
  match elim_tattr ty with
  | TModSig _
  | TModLid _ -> true
  | _ -> false
let is_mod_var x = is_mod_typ @@ Id.typ x

let subst_tconstr map ty =
  make_trans (fun tr ty ->
      match ty with
      | TConstr(LId c, params) when Id.List.mem_assoc c map ->
          Some (TConstr(Id.List.assoc c map, List.map tr params))
      | _ -> None) ty

let subst_path_head_map map =
  make_trans (fun tr ty ->
      match ty with
      | TConstr(path, tys) -> Some (TConstr(Path.subst_head_map map path, List.map tr tys))
      | _ -> None)

let subst_path_head x lid = subst_path_head_map [x,lid]

let subst_path_prefix_map map =
  make_trans (fun tr ty ->
      match ty with
      | TConstr(path, tys) -> Some (TConstr(Path.subst_prefix_map map path, List.map tr tys))
      | _ -> None)

let subst_path_map map =
  make_trans (fun tr ty ->
      match ty with
      | TConstr(path, tys) -> Some (TConstr(List.subst ~eq:Path.eq  map path, List.map tr tys))
      | _ -> None)

let add_prefix_opt prefix path =
  match prefix with
  | None -> path
  | Some p -> Path.append p path

type 'a sig_elem =
  | Sig_types of 'a decl_item
  | Sig_ext of 'a ext
  | Sig_values of 'a tid
let _Sig_types decl = Sig_types decl
let _Sig_ext ext = Sig_ext ext
let _Sig_values x = Sig_values x

let map_sig_elem f elem =
  match elem with
  | Sig_types (c, (p, ty)) -> Sig_types (c, (p, f ty))
  | Sig_ext (c, (p, {ext_row_path; ext_row_args; ext_row_ret})) ->
      let ext_row_args = List.map f ext_row_args in
      let ext_row_ret = Option.map f ext_row_ret in
      Sig_ext (c, (p, {ext_row_path; ext_row_args; ext_row_ret}))
  | Sig_values x -> Sig_values (Id.map_typ f x)

let cons_prefix m (p, e) =
  let m' = Id.set_typ m () in
  let p' =
    match p with
    | None -> Some (LId m')
    | Some path -> Some (Path.cons m' path)
  in
  p', e

let rec flatten_signature ~env {sig_types; sig_ext; sig_values} : (path option * _ sig_elem) list =
  let sig_values_mod = List.filter (Id.typ |- is_mod_typ) sig_values in
  let none f x = None, f x in
  List.rev_flatten
    [List.map (none _Sig_types) @@ List.flatten sig_types;
     List.map (none _Sig_ext) sig_ext;
     List.map (none _Sig_values) sig_values;
     List.flatten_map (flatten_signature_of_mod ~env) sig_values_mod]

and flatten_signature_of_mod ~env m =
  let sgn =
    m
    |> sig_of_id ~env
    |> flatten_signature ~env
  in
  let path_map =
    sgn
    |> List.filter_map (function
           | (p, Sig_types (c, _)) ->
                   let path = add_prefix_opt p (LId c) in
                   Some (path, Path.cons m path)
           | _ -> None)
  in
  sgn
  |> List.map (cons_prefix m)
  |> Fmap.(list (snd (map_sig_elem (subst_path_map path_map))))

let types_in_signature ~(env : 'a mod_env) sgn : (path option * _ decl_item) list =
  sgn
  |> flatten_signature ~env
  |> List.filter_map (function (p, Sig_types x) -> Some (p,x) | _ -> None)

and types_in_module ~(env : 'a mod_env) m : (path option * _ decl_item) list =
  m
  |> flatten_signature_of_mod ~env
  |> List.filter_map (function (p, Sig_types x) -> Some (p,x) | _ -> None)

let fields_in_decl_item (decl : _ decl_item) =
  match decl with
  | _, (_, TRecord fields) -> List.map (fst |- Path._LId) fields
  | _ -> []

let fields_in_declaration (decl : _ declaration) =
  decl
  |> List.rev_flatten_map fields_in_decl_item

let fields_in_declarations (decls : _ declaration list) =
  List.flatten_map fields_in_declaration decls

(* TODO: use types_in_signature or flatten_signature *)
let rec fields_in_signature ~(env : 'a mod_env) sgn : path list =
  fields_in_declarations sgn.sig_types @@@
  (sgn.sig_values
   |> List.filter (is_mod_typ -| Id.typ)
   |> List.rev_flatten_map (fields_in_module ~env))

(* TODO: use types_in_module or flatten_signature_of_mod *)
and fields_in_module ~(env : 'a mod_env) m : path list =
  types_in_module ~env m
  |> List.rev_flatten_map (fun (p,decl) -> List.map (Pair.pair p) @@ fields_in_decl_item decl)
  |> List.map (Fun.uncurry add_prefix_opt)

let constrs_in_declaration (decl : _ declaration) : constr list =
  decl
  |> List.rev_flatten_map (function
         | _, (_, TVariant(VNonPoly, rows)) -> List.map row_constr rows
         | _ -> [])

let constrs_in_declarations (decls : _ declaration list) : constr list =
  List.rev_flatten_map constrs_in_declaration decls

(* TODO: use types_in_signature or flatten_signature *)
let rec constrs_in_signature ~(env : 'a mod_env) sgn =
  let constrs1 =
    sgn.sig_values
    |> List.filter (is_mod_typ -| Id.typ)
    |> List.rev_flatten_map (constrs_in_module ~add_prefix:true ~env)
  in
  let constrs2 =
    sgn.sig_types
    |> constrs_in_declarations
    |> List.rev_map Path._LId
  in
  constrs1 @@@ constrs2

(* TODO: use types_in_module or flatten_signature_of_mod *)
and constrs_in_module ?(add_prefix=false) ~(env : 'a mod_env) m =
  try
    sig_of_id ~env m
    |> constrs_in_signature ~env
    |&add_prefix&> List.map (Path.cons m)
  with Invalid_argument _ -> invalid_arg "constrs_defined_in_module"

let values_in_signature ~(env : 'a mod_env) sgn : (path option * _ tid) list =
  sgn
  |> flatten_signature ~env
  |> List.filter_map (function (p, Sig_values x) -> Some (p,x) | _ -> None)

let values_in_module ~(env : 'a mod_env) m : (path option * _ tid) list =
  m
  |> flatten_signature_of_mod ~env
  |> List.filter_map (function (p, Sig_values x) -> Some (p,x) | _ -> None)

let add_module_prefix_tconstr_map mod_path (prefix,decl) =
  let prefix' =
    match prefix with
    | None -> LId mod_path
    | Some p -> Path.cons mod_path p
  in
  let make (c,_) = c, LDot(prefix', Id.name c) in
  List.map make decl

let assoc_row constr rows =
  List.find (row_constr |- Id.(=) constr) rows

let assoc_row_with_pos ~sort constr rows =
  rows
  |&sort&> List.sort (Compare.on (row_constr |- Id.name))
  |> List.find_mapi (fun i row ->
      if Id.(constr = row.row_constr) then
        Some (i, row.row_args)
      else
        None)

let apply_tconstr pty tys =
  let _,(params,ty) = copy_tconstr_params pty in
  if List.length params <> List.length tys then invalid_arg "%s" __FUNCTION__;
  List.iter2 instantiate params tys;
  match ty with
  | TConstraint(ty', cs) ->
      List.iter (fun (p,ty) -> assert (eq p ty)) cs;
      ty'
  | _ -> ty
