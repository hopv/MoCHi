open Ppxlib

let make_ident md ~loc s =
  let id = { txt = Ldot (Lident md, s); loc } in
  Ast_helper.Exp.ident id

let list_of ~loc ts = List.fold_right (fun t acc -> [%expr [%e t] :: [%e acc]]) ts [%expr []]
let id_of x = Ast_helper.Exp.ident ~loc:x.loc { x with txt = Lident x.txt }
let is_var e name = match e.pexp_desc with Pexp_ident id -> id.txt = Lident name | _ -> false
let unsupported_term loc = Location.raise_errorf ~loc "Unsupported syntax of %%term"
let no_label e = (Nolabel, e)
let no_labels xs = List.map no_label xs

let major, minor =
  match String.split_on_char '.' Sys.ocaml_version with
  | major :: minor :: _ -> (major, minor)
  | _ -> assert false
