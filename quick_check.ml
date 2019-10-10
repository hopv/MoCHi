open Util
open Syntax
open Type
open Term_util

module RT = Ref_type

let generate ty =
  match ty with
  | TUnit -> Term.unit
  | TBool -> Term.bool @@ Random.bool ()
  | TInt -> Term.int @@ int_of_float @@ Random.gaussian 256.
  | TPrim s -> unsupported ("TPrim " ^ s)

let check ?limit t =
  let gen () = int_of_float @@ Random.gaussian 256. in
  try
    ignore @@ Eval.eval_print Format.dummy_formatter (ref 0) limit gen t;
    true
  with
  | Eval.RaiseExcep _ -> false
  | Eval.EventFail -> false
  | Eval.ReachLimit -> true
  | Eval.ReachBottom -> true

let rec repeat n t =
  n <= 0 || check ~limit:1000 t && repeat (n-1) t

let rec repeat_forever t =
  check t && repeat_forever t
