open Ppxlib
open Ppx_util

let print_ident ~loc s = make_ident "Print" ~loc s
let pp_ident ~loc s = Ast_helper.Exp.ident { txt = Lident ("pp_" ^ s); loc }

let rec print_of_type mk_ident (ty : core_type) =
  let pot = print_of_type mk_ident in
  let loc = ty.ptyp_loc in
  match ty.ptyp_desc with
  | Ptyp_constr (c, tys) ->
      let id =
        match c.txt with
        | Lident s -> mk_ident ~loc:c.loc s
        | Ldot (m, "t") -> Ast_helper.Exp.ident { c with txt = Ldot (m, "print") }
        | _ -> Location.raise_errorf ~loc "Unsupported syntax of %%ty: %a" Pprintast.core_type ty
      in
      let args = no_labels @@ List.map pot tys in
      if tys = [] then id else Ast_helper.Exp.apply ~loc id args
  | Ptyp_tuple [ ty1; ty2 ] ->
      let t1 = pot ty1 in
      let t2 = pot ty2 in
      [%expr Print.pair [%e t1] [%e t2]]
  | Ptyp_tuple [ ty1; ty2; ty3 ] ->
      (* TODO: merge & generalize with the above *)
      let t1 = pot ty1 in
      let t2 = pot ty2 in
      let t3 = pot ty3 in
      [%expr Print.tuple [%e t1] [%e t2] [%e t3]]
  | Ptyp_var s -> Ast_helper.Exp.(ident ~loc { txt = Lident s; loc })
  | Ptyp_extension ({ txt = "e"; _ }, PStr [ { pstr_desc = Pstr_eval (e1, _); _ } ]) -> e1
  | Ptyp_tuple _ | Ptyp_arrow _ | Ptyp_any
  | Ptyp_object (_, _)
  | Ptyp_class (_, _)
  | Ptyp_alias (_, _)
  | Ptyp_variant (_, _, _)
  | Ptyp_poly (_, _)
  | Ptyp_package _ | Ptyp_extension _ ->
      Location.raise_errorf ~loc "Unsupported syntax of %%ty: %a" Pprintast.core_type ty

let expand_print ~ctxt (ty : core_type) =
  let _loc = Expansion_context.Extension.extension_point_loc ctxt in
  print_of_type print_ident ty

let expand_pp ~ctxt (ty : core_type) =
  let _loc = Expansion_context.Extension.extension_point_loc ctxt in
  print_of_type pp_ident ty

let print_extension =
  Extension.V3.declare "pr" Extension.Context.expression Ast_pattern.(ptyp __) expand_print

let pp_extension =
  Extension.V3.declare "pp" Extension.Context.expression Ast_pattern.(ptyp __) expand_pp

let pp_rule = Context_free.Rule.extension pp_extension
let print_rule = Context_free.Rule.extension print_extension
