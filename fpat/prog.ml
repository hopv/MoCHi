open Util
open Combinator

(** Programs *)

type t = {
  fdefs: Fdef.t list;
  types: TypEnv.t;
  main: string
}

let make fdefs types main = { fdefs = fdefs; types = types; main = main }

(** {6 Printers} *)

let pr ppf prog =
  Format.fprintf ppf
    "@[<v>%a@,%a@]"
    (List.pr Fdef.pr "@,") prog.fdefs
    (List.pr TypEnv.pr_elem "@,") prog.types

(** {6 Inspectors} *)

let is_defined prog f =
  try
    ignore (List.find (fun fdef -> Idnt.make fdef.Fdef.name = f) prog.fdefs);
    true
  with Not_found ->
    false

let fdef_of prog f =
  List.find (fun fdef -> Idnt.make fdef.Fdef.name = f) prog.fdefs

let fdefs_of prog f =
  prog.fdefs
  |> List.find_all (fun fdef -> Idnt.make fdef.Fdef.name = f)
  |> if_ ((=) [])
    (fun _ ->
       Logger.debug_assert_false
         ~on_failure:(fun () ->
             Format.printf "function \"%a\" not defined@," Idnt.pr f)
         ())
    id

(** assume that each fun.def. of a function f has the same arity? *)
let arity_of prog = fdef_of prog >> Fdef.arity_of

let coeffs prog = List.concat_map Fdef.coeffs prog.fdefs

(** @param x is a structured variable *)
let is_base prog = TypEnv.lookup prog.types >> Type.is_fun >> not (* @todo *)
