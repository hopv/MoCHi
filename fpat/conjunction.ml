open Util
open Combinator

type t = Formula.t list

let formula_of = Formula.band

let simplify =
  List.unique
  >> (if_ (List.exists Formula.is_false)
        (const [Formula.mk_false])
        (List.filter (Formula.is_true >> not)))
let simplify = Logger.log_block1 "Conjunction.simplify" simplify
