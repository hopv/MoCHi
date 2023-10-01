open CEGAR_syntax

type filename = string
type node = UnitNode | BrNode | LineNode of int | EventNode of string
type counterexample =
  | CESafety of int list
  | CENonTerm of string Rose_tree.t
  | CEFairNonTerm of HORS_syntax.rules

type result = Safe of (var * Inter_type.t) list | Unsafe of counterexample

(* termination and fair-termination problems are reduced to safety problems *)
type spec =
  | Safety
  | NonTermination
  | FairNonTermination of Fair_termination_type.fairness

type result' =
  | RSafety of safety_result
  | RNonTermination of nontermination_result
  | RFairNonTermination of fair_nontermination_result

and safety_result =
  | SSafe of (var * Inter_type.t) list
  | SUnsafe of int list

and nontermination_result =
  | NTSafe of (var * Inter_type.t) list
  | NTUnsafe of string Rose_tree.t

and fair_nontermination_result =
  | FNTSafe of (var * Inter_type.t) list
  | FNTUnsafe of HORS_syntax.rules

(*
let decomp_unsafe_result = function
  | RSafety (SUnsafe _ -> true)
  | RTermination ()
  | RNonTermination of nontermination_result
  | RFairTermination of fair_termination_result
  | _ -> false

let is_unsafe_result = function
 *)
module type MC_safety_interface = sig
  type spec_safety
  val make_spec_safety : int -> spec_safety
  val check_safety : CEGAR_syntax.prog * spec_safety -> safety_result
end

module type MC_nontermination_interface = sig
  type spec_nontermination
  val make_spec_nontermination : string list -> spec_nontermination
  val check_nontermination : CEGAR_syntax.prog * spec_nontermination -> nontermination_result
end

module type MC_fair_nontermination_interface = sig
  type spec_fair_nontermination
  val make_spec_fair_nontermination : string list -> (string * string) list -> spec_fair_nontermination
  val check_fair_nontermination : CEGAR_syntax.prog * spec_fair_nontermination -> fair_nontermination_result
end

module MC_dummy = struct
  type spec_safety
  let make_spec_safety _ = failwith "Model checker is not available"
  let make_spec_nontermination _ = failwith "Model checker is not available"
  type spec_fair_nontermination
  let make_spec_fair_nontermination _ = failwith "Model checker is not available"
  let check_safety _ = failwith "Model checker is not available"
  type spec_nontermination
  let check_nontermination _ = failwith "Model checker is not available"
  let check_fair_nontermination _ = failwith "Model checker is not available"
end

let succ f x = f (x + 1)
let rec app3 f g =
  if Random.bool() then app3 (succ f) g
  else g f
