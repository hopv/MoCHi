open Util
open Type
open Term_util

let generate ty =
  match ty with
  | TUnit -> Term.unit
  | TBool -> Term.bool @@ Random.bool ()
  | TInt -> Term.int @@ int_of_float @@ Random.gaussian 256.

let check ?limit t =
  let gen ty _ =
    assert (ty = TBase TInt);
    Term.int @@ int_of_float @@ Random.gaussian 256.
  in
  try
    Eval.eval_print ?limit gen ignore t;
    true
  with
  | Eval.RaiseExcep _ -> false
  | Eval.EventFail -> false
  | Eval.ReachLimit -> true
  | Eval.ReachBottom -> true

let rec repeat n t = n <= 0 || (check ~limit:1000 t && repeat (n - 1) t)
let rec repeat_forever t = check t && repeat_forever t
