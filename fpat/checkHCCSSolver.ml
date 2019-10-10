open Util
open Combinator

let solve solver hcs =
  let sol = solver hcs in
  Logger.debug_assert
    (fun () ->
       if HCCS.is_solution hcs sol then true
       else begin
         Logger.printf "solution:@,  %a@," PredSubst.pr sol;
         false
       end);
  sol
let solve solver = Logger.log_block2 "CheckHCCSSolver.solve" solve solver

let solve_part_check hcs0 solver hcs =
  let sol = solver hcs in
  Logger.debug_assert (fun () -> FwHCCSSolver.is_partial_solution hcs0 sol);
  sol
let solve_part_check hcs0 =
  Logger.log_block3 "CheckHCCSSolver.solve_part_check" solve_part_check hcs0
