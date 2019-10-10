open Util
open Combinator

type t = Formula.t list

let formula_of = Formula.bor

let simplify =
  List.unique
  >> (if_ (List.exists Formula.is_true)
        (const [Formula.mk_true])
        (List.filter (Formula.is_false >> not)))
let simplify = Logger.log_block1 "Disjunction.simplify" simplify
