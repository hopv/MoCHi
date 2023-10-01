open Ppxlib

class map = object
  inherit Ast_traverse.map

  method! longident lid =
    match lid with
    | Lident "__FUNCTION__" -> Lident "__LOC__"
    | _ -> lid
end
