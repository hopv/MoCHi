open Util
open Combinator
open Term

(** Clauses of boolean atoms *)

include Clause

let classify =
  List.partition_map
    (fun lit ->
       match lit |> Literal.term_of |> fun_args with
       | Var(_), [] -> `L(lit)
       | Const(Const.Not), [Var(_)] -> `L(lit)
       | _ -> `R(lit))

let pxs_nxs =
  List.partition_map
    (fun lit ->
       match lit |> Literal.term_of |> fun_args with
       | Var(x), [] -> `L(x)
       | Const(Const.Not), [Var(x)] -> `R(x)
       | _ -> assert false)
  
let simplify lits =
  let blits, lits' = classify lits in
  let pxs, nxs = pxs_nxs blits in
  if Set_.inter pxs nxs <> [] then [Literal.mk_true] else lits
let simplify = Logger.log_block1 "BoolClause.simplify" simplify
