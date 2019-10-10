open Util
open Combinator

type t = Formula.t -> Formula.t -> Formula.t

(** {6 Exceptions} *)

exception NoInterpolant
exception Fail
exception Unknown

(** {6 Options} *)

let interp_simplify = ref true

(** {6 CSIsat options} *)

let csisat_use_integer_heuristic = ref true
(* need to set true if boolean values are used without encoding to integers *)
let csisat_use_theory = ref true
let csisat_int_mode = ref true
let degree = ref 1

(** {6 Interpolating prover combinators} *)

let interpolate_quick ip phi1 phi2 =
  if SMTProver.is_valid_dyn (Formula.bnot phi1) then Formula.mk_false
  else if SMTProver.is_valid_dyn (Formula.bnot phi2) then Formula.mk_true
  else ip phi1 phi2
let interpolate_quick =
  Logger.log_block3 "InterpProver.interpolate_quick" interpolate_quick

let interpolate_simplify qelim ip phi1 phi2 =
  let bvs =
    Set_.inter
      (phi1 |> Formula.fvs |> List.unique)
      (phi2 |> Formula.fvs |> List.unique)
  in
  (phi1, phi2)
  |> Pair.lift
    (Formula.conjuncts_of
     >> Formula.band
     >> FormulaSimplifier.simplify
     >> qelim bvs)
  |> Pair.fold ip
  |> FormulaSimplifier.simplify
  |> FormulaSimplifier.simplify_dnf_interp phi1 phi2
let interpolate_simplify ?(qelim = fun _ -> id) =
  Logger.log_block3
    "InterpProver.interpolate_simplify"
    (interpolate_simplify qelim)

let interpolate_log ip phi1 phi2 =
  try ip phi1 phi2
  with
  | NoInterpolant ->
    Logger.printf0 "there is no interpolant@,";
    raise NoInterpolant
  | Fail ->
    Logger.printf0 "there is an interpolant but failed to find one@,";
    raise Fail
  | Unknown ->
    Logger.printf0 "unknown whether there is an interpolant or not@,";
    raise Unknown
let interpolate_log =
  Logger.log_block3
    "InterpProver.interpolate_log"
    ~before:(fun _ ->
        curry2 (Logger.printf "input: %a@," (Pair.pr Formula.pr Formula.pr)))
    ~after:(Logger.printf "output: %a" Formula.pr)
    interpolate_log

let interpolate_fresh p ip phi1 phi2 =
  (phi1, phi2)
  |> Pair.lift (fun phi ->
      Formula.fresh (phi |> Formula.fvs |> List.filter (p >> not)) phi)
  |> Pair.fold ip
let interpolate_fresh =
  Logger.log_block4 "InterpProver.interpolate_fresh" interpolate_fresh

(** {6 Dynamically linked solvers} *)

let ext_interpolate_csisat0 = ref (fun _ _ -> assert false : t)
let interpolate_csisat0_dyn phi1 phi2 =
  Logger.log_block2
    "InterpProver.interpolate_csisat0_dyn"
    !ext_interpolate_csisat0 phi1 phi2

let ext_interpolate_csisat =
  ref (fun _ _ _ -> assert false : (Idnt.t -> bool) -> t)
let interpolate_csisat_dyn p phi1 phi2 =
  Logger.log_block3
    "InterpProver.interpolate_csisat_dyn"
    !ext_interpolate_csisat p phi1 phi2

let ext_interpolate_csisat_gen =
  ref (fun _ _ _ -> assert false : (Idnt.t -> bool) -> t)
let interpolate_csisat_gen_dyn p phi1 phi2 =
  Logger.log_block3
    "InterpProver.interpolate_csisat_gen_dyn"
    !ext_interpolate_csisat_gen p phi1 phi2

let ext_interpolate_aisat =
  ref (fun _ _ _ -> assert false : (Idnt.t -> bool) -> t)
let interpolate_aisat_dyn p phi1 phi2 =
  Logger.log_block3
    "InterpProver.interpolate_aisat_dyn"
    !ext_interpolate_aisat p phi1 phi2

let ext_interpolate_z3 =
  ref (fun _ _ _ -> assert false : (Idnt.t -> bool) -> t)
let interpolate_z3_dyn p phi1 phi2 =
  Logger.log_block3
    "InterpProver.interpolate_z3_dyn"
    !ext_interpolate_z3 p phi1 phi2


let ext_interpolate = ref (fun _ _ _ -> assert false : (Idnt.t -> bool) -> t)
let link_dyn ip = ext_interpolate := ip
let get_dyn () = !ext_interpolate
let interpolate_dyn p phi1 phi2 =
  Logger.log_block3 "InterpProver.interpolate_dyn" !ext_interpolate p phi1 phi2
