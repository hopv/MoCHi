open Ppxlib
open Ppx_util

let type_constrs =
  List.map
    (fun s -> (Lident s, s))
    [
      "unit";
      "int";
      "bool";
      "unknown";
      "result";
      "abst";
      "exn";
      "string";
      "list";
      "ref";
      "option";
      "array";
      "set";
    ]

let ty_ident ~loc s = make_ident "Ty" ~loc s

let rec term_of_type (ty : core_type) =
  let loc = ty.ptyp_loc in
  match ty.ptyp_desc with
  | Ptyp_constr (id, tys) when List.mem_assoc id.txt type_constrs ->
      let s = ty_ident ~loc:id.loc @@ List.assoc id.txt type_constrs in
      let args = no_labels @@ List.map term_of_type tys in
      if tys = [] then s else Ast_helper.Exp.apply ~loc s args
  | Ptyp_arrow (Nolabel, ty1, ty2) ->
      let ty1 = term_of_type ty1 in
      let ty2 = term_of_type ty2 in
      [%expr Ty.fun_ [%e ty1] [%e ty2]]
  | Ptyp_tuple tys ->
      let tys = list_of ~loc @@ List.map term_of_type tys in
      [%expr Ty.tuple [%e tys]]
  | Ptyp_var s -> Ast_helper.Exp.(ident ~loc { txt = Lident s; loc })
  | Ptyp_extension ({ txt = "e"; _ }, PStr [ { pstr_desc = Pstr_eval (e1, _); _ } ]) -> e1
  | Ptyp_arrow _ | Ptyp_constr _ | Ptyp_any
  | Ptyp_object (_, _)
  | Ptyp_class (_, _)
  | Ptyp_alias (_, _)
  | Ptyp_variant (_, _, _)
  | Ptyp_poly (_, _)
  | Ptyp_package _ | Ptyp_extension _ ->
      Location.raise_errorf ~loc "Unsupported syntax of %%ty: %a" Pprintast.core_type ty

let expand ~ctxt (ty : core_type) =
  let _loc = Expansion_context.Extension.extension_point_loc ctxt in
  term_of_type ty

let extension = Extension.V3.declare "ty" Extension.Context.expression Ast_pattern.(ptyp __) expand
let rule = Context_free.Rule.extension extension
