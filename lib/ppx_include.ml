open Ppxlib
open Ppx_util

let supported_versions =
  [
    ("4", "08");
    ("4", "09");
    ("4", "10");
    ("4", "11");
    ("4", "12");
    ("4", "13");
    ("4", "14");
    ("5", "0");
    ("5", "1");
  ]

let expand ~ctxt (payload : payload) =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  match payload with
  | PStr
      [
        {
          pstr_desc =
            Pstr_eval ({ pexp_desc = Pexp_constant (Pconst_string ("Parser_wrapper", _, _)); _ }, _);
          _;
        };
      ] ->
      if not (List.mem (major, minor) supported_versions) then
        Location.raise_errorf ~loc "Unsupported OCaml version %s" Sys.ocaml_version;
      let txt = Lident (Format.sprintf "Parser_wrapper_%s_%s" major minor) in
      let pincl_mod = Ast_builder.Default.pmod_ident ~loc { txt; loc } in
      Ast_builder.Default.pstr_include ~loc { pincl_mod; pincl_loc = loc; pincl_attributes = [] }
  | _ -> Location.raise_errorf ~loc "Unsupported syntax of %%%%include"

let extension =
  Extension.V3.declare "include" Extension.Context.structure_item Ast_pattern.__ expand

let rule = Context_free.Rule.extension extension
