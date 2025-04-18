open Ppxlib

let macros =
  [
    ("pr_loc", fun loc -> [%expr Format.printf "%s@." __LOC__]);
    ("unsupported", fun loc -> [%expr unsupported "%s" __FUNCTION__]);
    ("invalid_arg", fun loc -> [%expr invalid_arg "%s" __FUNCTION__]);
  ]

let rules =
  macros
  |> List.map (fun (s, make) ->
         Extension.V3.declare s Extension.Context.expression Ast_pattern.__ (fun ~ctxt _ ->
             make @@ Expansion_context.Extension.extension_point_loc ctxt))
  |> List.map Context_free.Rule.extension
