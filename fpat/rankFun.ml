open Util
open Combinator

(** for ranking funciton annotations *)

type elem =
  | Rank of Idnt.t * (Idnt.t list * Term.t list)
  | Rank_game of int * Idnt.t * (Idnt.t list * Term.t list)
type t = elem list

(** {6 Options} *)

let num_rankfuns = ref 1

(** {6 Printers} *)

let pr_elem ppf = function
  | Rank(f, (args, ts)) ->
    Format.fprintf ppf "%a(%a) = %a" Idnt.pr f Idnt.pr_list args Term.pr_list ts
  | Rank_game(i, f, (args, ts)) ->
    Format.fprintf ppf "%a[%a](%a) = %a" Idnt.pr f Integer.pr i Idnt.pr_list args Term.pr_list ts

let pr ppf = Format.fprintf ppf "%a" (List.pr pr_elem "@,")

(** {6 Auxiliary constructors} *)

let mk_rank_elem (f,n) = Rank(f, n)
let mk_ranks = List.map mk_rank_elem

(** {6 Template generators} *)

let mk_templates ranks (f, tys) =
  let name_of = function Rank(x, _) -> x | Rank_game(_, x, _) -> x in
  let body_of = function Rank(_, ts) -> ts | Rank_game(_, _, ts) -> ts in
  try
    let xs, ts =
      ranks
      |> List.find (name_of >> Idnt.string_of >> (=) f)
      |> body_of
    in
    assert(List.length xs = List.length tys);
    let tenv = List.map2 Pair.make xs tys in
    f, (tenv, ts)
  with Not_found ->
    let tenv = List.map (fun ty -> Idnt.new_var (), ty) tys in
    let ts =
      List.gen !num_rankfuns
        (fun _ -> Template.mk_linexp tenv)
    in
    f, (tenv, ts)

let rec wfrel_of_aux (t1, t2) = function
  | [], [] -> []
  | prev :: rest1, next :: rest2 ->
    Formula.band
      [IntFormula.geq t1 t2;
       (*IntFormula.geq t2 IntTerm.zero;*)
       IntFormula.gt prev next;
       IntFormula.geq next IntTerm.zero]
    :: wfrel_of_aux (prev, next) (rest1, rest2)
  | _ -> assert false
let wfrel_of tmpss f1 args1 f2 args2 =
  let ts1 =
    let args1 = List.map (fst >> Term.mk_var) args1 in
    let xs1, ts1 = List.assoc_fail f1 tmpss in
    let xs1 = List.map fst xs1 in
    List.map (Term.subst (List.combine xs1 args1)) ts1
  in
  let ts2 =
    let args2 = List.map (fst >> Term.mk_var) args2 in
    let xs2, ts2 = List.assoc_fail f2 tmpss in
    let xs2 = List.map fst xs2 in
    List.map (Term.subst (List.combine xs2 args2)) ts2
  in
  (* List.length ts1 = List.length ts2 > 0 *)
  match ts1, ts2 with
  | prev :: rest1, next :: rest2 ->
    Formula.band
      [IntFormula.gt prev next;
       IntFormula.geq next IntTerm.zero]
    :: wfrel_of_aux (prev, next) (rest1, rest2)
    |> Formula.bor
  | _, _ -> assert false
