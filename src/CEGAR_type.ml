open Util

type var = string
and base = TUnit | TInt | TBool | TAbst of string

and 'a constr =
  | TList
  | TTuple
  | TFixPred of ('a -> 'a)
  | TPath of int list (* used only for refinement *)
  | TSet

and 'a t =
  | TBase of base * ('a -> 'a list)
  | TConstr of 'a constr * 'a t list * ('a -> 'a list)
  | TFun of 'a t * ('a -> 'a t)
[@@deriving show { with_path = false }]

(** Constructors *)

let typ_result_base = TAbst "X"
let typ_result = TBase (typ_result_base, fun _ -> [])
let typ_unit = TBase (TUnit, fun _ -> [])
let typ_bool_empty = TBase (TBool, fun _ -> [])
let typ_bool_id = TBase (TBool, fun x -> [ x ])
let typ_bool () = if !Flag.PredAbst.bool_init_empty then typ_bool_empty else typ_bool_id
let typ_int = TBase (TInt, fun _ -> [])
let typ_abst s = TBase (TAbst s, fun _ -> [])
let typ_event = TFun (TFun (typ_unit, fun _ -> typ_unit), fun _ -> typ_unit)
let make_tfun typ1 typ2 = TFun (typ1, fun _ -> typ2)
let typ_unknown = TBase (TAbst "?", fun _ -> [])

let rec app typ ts =
  match (typ, ts) with
  | TFun (_, typ2), t :: ts' -> app (typ2 t) ts'
  | _, [] -> typ
  | _ -> assert false

let make_ttuple typs = TConstr (TTuple, typs, fun _ -> [])
let make_tset ty = TConstr (TSet, [ ty ], fun _ -> [])

(** Destructors/Inspectors *)

let rec decomp_base ty =
  match ty with
  | TBase (b, ps) -> Some (b, ps)
  | TConstr (TFixPred _, [ ty ], _) -> decomp_base ty
  | TConstr (TSet, _, ps) (* WORKAROUND *) -> Some (TAbst "set", ps)
  | _ -> None

let is_base ty = None <> decomp_base ty
let get_base ty = fst @@ Option.get @@ decomp_base ty
let is_typ_result ty = try get_base ty = typ_result_base with _ -> false
let is_ttuple ty = match ty with TConstr (TTuple, _, _) -> true | _ -> false

let rec arg_num x typ =
  match typ with
  | TBase _ -> 0
  | TConstr _ -> unsupported "CEGAR_type.arg_num: TConstr"
  | TFun (_, typ2) -> 1 + arg_num x (typ2 x)

(** Transformers *)

let rec map f ty =
  match f (map f) ty with
  | Some ty' -> ty'
  | None -> (
      match ty with
      | TBase _ -> ty
      | TConstr (c, tys, ps) -> TConstr (c, List.map (map f) tys, ps)
      | TFun (ty1, ty2) -> TFun (map f ty1, map f -| ty2))

let map_base f =
  let tr _ ty = match ty with TBase (b, ps) -> Some (f b ps) | _ -> None in
  fun ty -> map tr ty

let map_preds f ty = map_base (fun b ps -> TBase (b, f -| ps)) ty
let map_pred f ty = map_preds (List.map f) ty

module Ty = struct
  let bool = typ_bool
  let int = typ_int
end
