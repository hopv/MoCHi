open Util
open Combinator
open Term

(** Clauses of integer atoms *)

include Clause

let classify =
  List.partition_map
    (fun lit ->
       try `L(lit |> LinIntRel.of_literal) with Invalid_argument _ -> `R(lit))

let simplify lits =
  let las, lits' = classify lits in
  (las |> LinIntRel.simplify_clause |> List.map LinIntRel.literal_of)
  @ lits'
