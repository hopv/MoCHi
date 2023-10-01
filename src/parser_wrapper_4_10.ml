open Util
open Asttypes
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
             name:   (Path.t * type_expr list) option }

  let row_repr row =
    let fields = row_fields row in
    let row = row_repr_no_fields row in
    Row { fields;
          more = row.row_more;
          closed = row.row_closed;
          name = row.row_name }

  let row_field_repr fi = fi

  let create desc =
    {desc; level=0; scope=0; id=0}

  let eq_type = (==)
end

module Ctype = struct
  include Ctype
  let full_expand ~may_forget_scope tenv typ =
    ignore may_forget_scope;
    full_expand tenv typ
  let is_equal = equal
end

module Typedtree = struct
  include Typedtree
  type functor_parameter =
    | Unit
    | Named of Ident.t option * string option loc * module_type
end

module Typemod = struct
  include Typemod
  let type_structure tenv struc =
    let struc',_,_,tenv' = type_structure tenv struc Location.none in
    struc', tenv'
end

type 'k pattern_desc' = pattern_desc
type 'k pattern' = Typedtree.pattern
type 'k case' = case

let decomp_Type_variant = function Types.Type_variant constrs -> constrs | _ -> assert false

let decomp_Reither = function Types.Reither(b, tys, _, _) -> b, tys | _ -> assert false

let decomp_Tpackage = function Types.Tpackage(path, ids, tys) -> path, List.combine ids tys | _ -> assert false

let decomp_Const_string = function Const_string(s,_) -> s | _ -> assert false

let decomp_Tpat_construct pat_desc =
  match pat_desc with
  | Tpat_construct(loc, desc, ps) -> loc, desc, ps
  | _ -> assert false

let is_Val_unbound _ = false

let some_module mb_id = mb_id
let is_named_module mb_id = Option.is_some mb_id
let get_module_id mb_id = Option.get mb_id

let is_Tpat_value _ = false
let decomp_Tpat_value _ _ = assert false

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
