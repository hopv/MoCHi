open Util
open Typedtree

module Types = struct
  include Types

  let get_id (ty:type_expr) = ty.id
  let get_level (ty:type_expr) = ty.level
  let get_desc (ty:type_expr) = ty.desc

  let rec row_fields row =
    match get_desc row.row_more with
    | Tvariant row' ->
        row.row_fields @ row_fields row'
    | _ ->
        row.row_fields

  let rec row_repr_no_fields row =
    match get_desc row.row_more with
    | Tvariant row' -> row_repr_no_fields row'
    | _ -> row

  type row_desc_repr =
    Row of { fields: (Asttypes.label * row_field) list;
             more:   type_expr;
             closed: bool;
             fixed:  fixed_explanation option;
             name:   (Path.t * type_expr list) option }

  let row_repr row =
    let fields = row_fields row in
    let row = row_repr_no_fields row in
    Row { fields;
          more = row.row_more;
          closed = row.row_closed;
          fixed = row.row_fixed;
          name = row.row_name }

  let row_field_repr fi = fi

  let create desc =
    Private_type_expr.create desc ~level:0 ~scope:0 ~id:0

  let eq_type = (==)
end

module Typemod = struct
  include Typemod
  let type_structure tenv struc =
    let struc',_,_,tenv' = type_structure tenv struc in
    struc', tenv'
end

type 'k pattern_desc' = 'k pattern_desc
type 'k pattern' = 'k general_pattern
type 'k case' = 'k case

let decomp_Type_variant = function Types.Type_variant(constrs,_) -> constrs | _ -> assert false

let decomp_Reither = function Types.Reither(b, tys, _, _) -> b, tys | _ -> assert false

let decomp_Tpackage = function Types.Tpackage(path, idtys) -> path, idtys | _ -> assert false

let decomp_Const_string = function Asttypes.Const_string(s,_,_) -> s | _ -> assert false

let decomp_Tpat_construct pat_desc =
  match pat_desc with
  | Tpat_construct(_, _, _, Some _) -> unsupported "Patterns with type annotations"
  | Tpat_construct(loc, desc, ps, None) -> loc, desc, ps
  | _ -> assert false

let is_Tpat_value : type k. k pattern_desc' -> _ = function Tpat_value _ -> true | _ -> false
let decomp_Tpat_value : type k. _ -> k pattern_desc' -> _ = fun pat -> function
  | Tpat_value p -> Option.get @@ fst @@ split_pattern {pat with pat_desc=Tpat_value p}
  | _ -> assert false

let is_Val_unbound _ = false

let some_module mb_id = mb_id
let is_named_module mb_id = Option.is_some mb_id
let get_module_id mb_id = Option.get mb_id

let decomp_Mty_functor mty =
  match mty with
  | Types.Mty_functor(arg, mty2) -> arg, mty2
  | _ -> assert false

let decomp_Tmod_functor mty =
  match mty with
  | Tmod_functor(arg, expr) -> arg, expr
  | _ -> assert false

let decomp_Text_decl = function Text_decl(args,ret) -> args, ret | _ -> assert false

let is_Env_value_unbound = function Env.Env_value_unbound _ -> true | _ -> false
let is_Env_module_unbound = function Env.Env_module_unbound _ -> true | _ -> false
let summary_of_Env_copy_types = function Env.Env_copy_types summary -> summary | _ -> assert false
let summary_of_Env_value_unbound = function Env.Env_value_unbound(summary,_,_) -> summary | _ -> assert false
let summary_of_Env_module_unbound = function Env.Env_module_unbound(summary,_,_) -> summary | _ -> assert false

let init_path_arg = ()
