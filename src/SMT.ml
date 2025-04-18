open Util
open! Type
open Syntax
open! Type_util
open! Term_util

let make_var_rmap xs =
  xs |> List.map CEGAR_trans.trans_var |> List.map2 (fun x y -> (FpatInterface.conv_var y, x)) xs

let conv_formula t =
  let defs, t' = CEGAR_trans.trans_term t in
  if defs <> [] then [%unsupported];
  FpatInterface.conv_formula t'

let inv_term t = t |> FpatInterface.inv_term |> CEGAR_trans.trans_inv_term
let inv_var rmap x = List.assoc x rmap
let check_sat t = t |> conv_formula |> Fpat.SMTProver.is_sat_dyn

let get_solution ?fv t =
  let fv = match fv with None -> get_fv t | Some fv -> fv in
  let rmap = make_var_rmap fv in
  t |> conv_formula |> Fpat.PolyConstrSolver.solve_dyn |> Fmap.(list (inv_var rmap * inv_term))
