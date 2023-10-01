open Ppxlib
open Ppx_util

let rules =
  [Ppx_term.rule;
   Ppx_type.rule;
   Ppx_include.rule;
   Ppx_print.print_rule;
   Ppx_print.pp_rule]
  @ Ppx_macros.rules

let () =
  Driver.register_transformation
    ~rules
    "ppx_mochi"

let () =
  if int_of_string (major^minor) < 412 then
    Driver.register_transformation
      ~impl:(new Ppx_FUNCTION.map)#structure
      "ppx_function"
