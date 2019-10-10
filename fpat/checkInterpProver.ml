open Util
open Combinator
open InterpProver

(** An nterpolating prover combinator for checking *)

let is_interpolant interp phi1 phi2 =
  SMTProver.implies_dyn [phi1] [interp]
  && SMTProver.implies_dyn [interp] [Formula.bnot phi2]
let is_interpolant =
  Logger.log_block3 "CheckInterpProver.is_interpolant"
    ~before:(fun interp phi1 phi2 ->
        Logger.printf "interp: %a@," Formula.pr interp;
        Logger.printf "phi1: %a@," Formula.pr phi1;
        Logger.printf "phi2: %a@," Formula.pr phi2)
    ~after:(Logger.printf "output: %a" Bool.pr)
    is_interpolant

let interpolate ip phi1 phi2 =
  try
    let interp = ip phi1 phi2 in
    if !Global.debug then
      if is_interpolant interp phi1 phi2 then interp else raise Unknown
    else interp
  with Unknown ->
    if SMTProver.implies_dyn [phi1] [Formula.bnot phi2] then raise Fail
    else raise NoInterpolant
let interpolate = Logger.log_block3 "CheckInterpProver.interpolate" interpolate

