open! Util
open! Syntax
open! Type_util
open! Term_util

type env = (id * typ) list

type t = {
  assertion : (id * Ref_type.t) list;
  ref_env : (id * Ref_type.t) list;
  ext_ref_env : (id * (string option * Ref_type.t)) list;
  abst_env : env;
  abst_cps_env : env;
  abst_cegar_env : env;
  inlined : id list;
  inlined_f : id list;
  fairness : Fair_termination_type.fairness;
}

let init =
  {
    assertion = [];
    ref_env = [];
    ext_ref_env = [];
    abst_env = [];
    abst_cps_env = [];
    abst_cegar_env = [];
    inlined = [];
    inlined_f = [];
    fairness = [];
  }
