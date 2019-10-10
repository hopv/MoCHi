open Util
open Combinator
open GenInterpProver

(** A generalized interpolating prover based on convex hull
    (see [Sato et al. PEPM'13] for detals) *)

let interpolate ch pids tenv lbs nubs =
  let lb' =
    lbs
    |> Formula.bor
    |> Logger.pprintf "lb:%a@," Formula.pr
    |> (if_
          (const ch)
          (Polyhedron.convex_hull_dyn
           >> FormulaSimplifier.simplify)
          id)
    |> Logger.pprintf "lb':%a@," Formula.pr
  in
  let nub'=
    nubs
    |> Formula.bor
    |> Logger.pprintf "nub:%a@," Formula.pr
    |> (if_
          (const ch)
          (Polyhedron.convex_hull_dyn
           >> FormulaSimplifier.simplify)
          id)
    |> Logger.pprintf "nub':%a@," Formula.pr
  in
  try
    let interp =
      InterpProver.interpolate_dyn
        (fun x -> List.mem_assoc x tenv || Idnt.is_coeff x)
        lb' nub'
    in
    List.map (flip Pair.make (tenv, interp)) pids
  with
  | InterpProver.NoInterpolant
  | InterpProver.Fail
  | InterpProver.Unknown ->
    List.map3
      (fun pid lb nub ->
         let interp =
           try
             InterpProver.interpolate_dyn
               (fun x -> List.mem_assoc x tenv || Idnt.is_coeff x)
               lb' nub
           with
           | InterpProver.NoInterpolant
           | InterpProver.Fail
           | InterpProver.Unknown ->
             (* resort to an ordinary interpolation *)
             try
               InterpProver.interpolate_dyn
                 (fun x -> List.mem_assoc x tenv || Idnt.is_coeff x)
                 lb nub
             with
             | InterpProver.NoInterpolant ->
               raise GenInterpProver.NoInterpolant
             | InterpProver.Fail ->
               raise GenInterpProver.Fail
             | InterpProver.Unknown ->
               raise (Global.NotImplemented "integer interpolation")
         in
         pid, (tenv, interp))
      pids lbs nubs
let interpolate =
  Logger.log_block5
    "CHGenInterpProver.interpolate"
    ~after:(Logger.printf "output:@,  %a" PredSubst.pr)
    interpolate
