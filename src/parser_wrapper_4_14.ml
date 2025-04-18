open Util
open Typedtree

module Types = struct
  include Types

  let create desc =
    let open Transient_expr in
    type_expr @@ create desc ~level:0 ~scope:0 ~id:0
end

module Typemod = struct
  include Typemod

  let type_structure tenv struc =
    let struc', _, _, _, tenv' = type_structure tenv struc in
    (struc', tenv')
end

type 'k pattern_desc' = 'k pattern_desc
type 'k pattern' = 'k general_pattern
type 'k case' = 'k case

let decomp_Type_variant = function Types.Type_variant (constrs, _) -> constrs | _ -> assert false
let decomp_Reither = function Types.Reither (b, tys, _) -> (b, tys) | _ -> assert false
let decomp_Tpackage = function Types.Tpackage (path, idtys) -> (path, idtys) | _ -> assert false
let decomp_Const_string = function Asttypes.Const_string (s, _, _) -> s | _ -> assert false

let decomp_Tpat_construct pat_desc =
  match pat_desc with
  | Tpat_construct (_, _, _, Some _) -> unsupported "Patterns with type annotations"
  | Tpat_construct (loc, desc, ps, None) -> (loc, desc, ps)
  | _ -> assert false

let is_Tpat_value : type k. k pattern_desc' -> _ = function Tpat_value _ -> true | _ -> false

let decomp_Tpat_value : type k. _ -> k pattern_desc' -> _ =
 fun pat -> function
  | Tpat_value p -> Option.get @@ fst @@ split_pattern { pat with pat_desc = Tpat_value p }
  | _ -> assert false

let is_Val_unbound _ = false
let some_module mb_id = mb_id
let is_named_module mb_id = Option.is_some mb_id
let get_module_id mb_id = Option.get mb_id

let decomp_Mty_functor mty =
  match mty with Types.Mty_functor (arg, mty2) -> (arg, mty2) | _ -> assert false

let decomp_Tmod_functor mty =
  match mty with Tmod_functor (arg, expr) -> (arg, expr) | _ -> assert false

let decomp_Text_decl = function Text_decl (_, args, ret) -> (args, ret) | _ -> assert false
let decomp_Texp_assert = function Texp_assert e -> e | _ -> assert false
let is_Env_value_unbound = function Env.Env_value_unbound _ -> true | _ -> false
let is_Env_module_unbound = function Env.Env_module_unbound _ -> true | _ -> false
let summary_of_Env_copy_types = function Env.Env_copy_types summary -> summary | _ -> assert false

let summary_of_Env_value_unbound = function
  | Env.Env_value_unbound (summary, _, _) -> summary
  | _ -> assert false

let summary_of_Env_module_unbound = function
  | Env.Env_module_unbound (summary, _, _) -> summary
  | _ -> assert false

let init_path_arg = ()
