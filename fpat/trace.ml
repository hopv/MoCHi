open Util
open Combinator

(** Traces *)

(** @todo implement get_min_unsat_prefix *)

(** events *)
type elem =
  | Call of (Idnt.t * int) * Formula.t (*Guard*)
  | Arg of TypTermSubst.t
  | Ret of TypTermSubst.elem
  | Nop
  | Assume of Pva.t option * Formula.t
  | Error
type t = elem list

(** {6 Printers} *)

let cnt = ref 0
let pr_elem ppf = function
  | Call(_, t) ->
    cnt := !cnt + 1;
    Format.fprintf ppf "[@[<hov>%a.@," Formula.pr t
  | Arg(xttys) ->
    Format.fprintf ppf "%a@," Formula.pr (Formula.of_ttsub xttys)
  | Ret(x, tt) -> 
    cnt := !cnt - 1;
    Format.fprintf ppf "%a@]]@," Formula.pr (Formula.of_ttsub [x, tt])
  | Nop -> Format.fprintf ppf "nop"
  | Assume(pva_opt, phi) ->
    Format.fprintf ppf
      "assume(%a,%a)@," (Option.pr Pva.pr "_") pva_opt Formula.pr phi
  | Error -> Format.fprintf ppf "error"

let pr ppf trace =
  cnt := 0;
  List.pr pr_elem "" ppf trace;
  ignore (List.init !cnt (fun _ -> Format.fprintf ppf "@]"))

let rec function_calls_of = function
  | [] -> []
  | Call(x, _) :: tr' -> x :: function_calls_of tr'
  | Assume(Some(pva), _) :: tr' ->
    let Idnt.T(Idnt.T(x, cnt, n), -1, 0) = Pva.idnt_of pva in
    assert (n = List.length (Pva.args_of pva) - 1);
    (x, cnt) :: (Idnt.T(x, cnt, n), -1) :: function_calls_of tr'
  | _ :: tr' -> function_calls_of tr'
