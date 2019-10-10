open Util
open Combinator

(** Function definitions *)

(** @require a.name = b.name => length a.args = length b.args *)
type t = {
  name: string;
  args: Pattern.t list; (* @require length length > 0 *)
  guard: Formula.t; (* a boolean expression that does not
                       involve side-effects and function calls *)
  body: Term.t
}

let make name args guard body =
  { name = name; args = args; guard = guard; body = body }

let name_of f = f.name
let args_of f = f.args
let guard_of f = f.guard
let body_of f = f.body

let pr ppf fdef =
  if Formula.is_true fdef.guard then
    Format.fprintf
      ppf
      "@[<hov2>%a =@ %a@]"
      (List.pr_app Pattern.pr "@ ")
      (Pattern.V (Idnt.make fdef.name) :: fdef.args)
      Term.pr fdef.body
  else
    Format.fprintf
      ppf
      "@[<hov2>@[<hov2>%a@ | %a@] =@ %a@]"
      (List.pr_app Pattern.pr "@ ")
      (Pattern.V (Idnt.make fdef.name) :: fdef.args)
      Formula.pr fdef.guard
      Term.pr fdef.body

let coeffs fdef = Formula.coeffs fdef.guard @ Term.coeffs fdef.body
let arity_of fdef = fdef.args |> List.length
