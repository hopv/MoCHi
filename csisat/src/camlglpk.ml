(*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *
 *  Copyright (C) 2007-2008  Dirk Beyer and Damien Zufferey.
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CSIsat web page:
 *    http://www.cs.sfu.ca/~dbeyer/CSIsat/
 *)

type t

external create: unit -> t = "lp_create"
external delete: t -> unit = "lp_delete"

(*
external set_name: t -> string -> unit = "lp_set_name"
external get_name: t -> string = "lp_get_name"
*)

external set_maximize: t -> unit = "lp_set_maximize"
external set_minimize: t -> unit = "lp_set_minimize"

external add_row: t -> int -> unit = "lp_add_row"
external add_col: t -> int -> unit = "lp_add_col"

external set_row_bnd_free:   t -> int -> unit                   = "lp_set_row_bnd_free"
external set_row_bnd_lower:  t -> int -> float -> unit          = "lp_set_row_bnd_lower"
external set_row_bnd_upper:  t -> int -> float -> unit          = "lp_set_row_bnd_upper"
external set_row_bnd_double: t -> int -> float -> float -> unit = "lp_set_row_bnd_double"
external set_row_bnd_fixed:  t -> int -> float -> unit          = "lp_set_row_bnd_fixed"

external set_col_bnd_free:   t -> int -> unit                   = "lp_set_col_bnd_free"
external set_col_bnd_lower:  t -> int -> float -> unit          = "lp_set_col_bnd_lower"
external set_col_bnd_upper:  t -> int -> float -> unit          = "lp_set_col_bnd_upper"
external set_col_bnd_double: t -> int -> float -> float -> unit = "lp_set_col_bnd_double"
external set_col_bnd_fixed:  t -> int -> float -> unit          = "lp_set_col_bnd_fixed"

external set_obj_coef: t -> int -> float -> unit             = "lp_set_obj_coef"
external set_mat_row: t -> int -> int -> float array -> unit = "lp_set_mat_row"
external set_mat_col: t -> int -> int -> float array -> unit = "lp_set_mat_col"

external simplex: t -> bool -> bool = "lp_simplex" (*second param: with/out presolve*)
external simplex_exact: t -> bool = "lp_simplex_exact"
external get_stat: t -> int = "lp_get_stat"
external get_obj_val: t -> float = "lp_get_obj_val"
external get_row_stat: t -> int -> int = "lp_get_row_stat"
external get_row_primal: t -> int -> float = "lp_get_row_primal"
external get_rows_primal: t -> int -> float array -> unit = "lp_get_rows_primal"
external get_row_dual: t -> int -> float = "lp_get_row_dual"
external get_rows_dual: t -> int -> float array -> unit = "lp_get_rows_dual"
external get_col_stat: t -> int -> int = "lp_get_col_stat"
external get_col_primal: t -> int -> float = "lp_get_col_primal"
external get_cols_primal: t -> int -> float array -> unit  = "lp_get_cols_primal"
external get_col_dual: t -> int -> float = "lp_get_col_dual"
external get_cols_dual: t -> int -> float array -> unit = "lp_get_cols_dual"
external is_col_basic: t -> int -> bool = "lp_is_col_basic"
external is_row_basic: t -> int -> bool = "lp_is_row_basic"

external interior: t -> bool = "lp_interior"
external ipt_obj_val: t -> float = "lp_ipt_obj_val"
external ipt_row_primal: t -> int -> float = "lp_ipt_row_primal"
external ipt_rows_primal: t -> int -> float array -> unit = "lp_ipt_rows_primal"
external ipt_row_dual: t -> int -> float = "lp_ipt_row_dual"
external ipt_rows_dual: t -> int -> float array -> unit = "lp_ipt_rows_dual"
external ipt_col_primal: t -> int -> float = "lp_ipt_col_primal"
external ipt_cols_primal: t -> int -> float array -> unit = "lp_ipt_cols_primal"
external ipt_col_dual: t -> int -> float = "lp_ipt_col_dual"
external ipt_cols_dual: t -> int -> float array -> unit = "lp_ipt_cols_dual"

external dump_problem: t -> unit = "lp_dump_problem"
