open Util
open Combinator

(** Floating point numbers *)

let pr ppf f = Format.fprintf ppf "%9.6f" f

let num_of_positive_float f =
  let m, e = frexp f in
  let sm = string_of_float m in
  let s = String.make 16 '0' in
  (** sm starts with "0." *)
  let _ = String.blit sm 2 (Bytes.of_string s) 0 (String.length sm - 2) in
  let e' = Num.power_num (Num.Int 2) (Num.num_of_int e) in
  Num.div_num
    (Num.mult_num (Num.num_of_string s) e')
    (Num.power_num (Num.Int 10) (Num.Int 16))
let num_of_float f =
  let n = int_of_float f in
  if f = float_of_int n then Num.Int n
  else if f < 0.0 then Num.minus_num (num_of_positive_float (abs_float f))
  else num_of_positive_float f

let rat_of_float f =
  Q.of_float f |> Q.num |> Z.to_int,
  Q.of_float f |> Q.den |> Z.to_int

let of_q q =
  (Q.num q |> Big_int_Z.float_of_big_int) /.
  (Q.den q |> Big_int_Z.float_of_big_int)

let round f =
  let f_ceil = ceil f in
  let f_floor = floor f in
  if (f_ceil -. f < f -. f_floor)
  then int_of_float f_ceil
  else int_of_float f_floor

let sum = List.fold_left (fun x1 x2 -> x1 +.(*/*) x2) 0.(*Num.num_of_int 0*)
let prod = List.fold_left (fun x1 x2 -> x1 *.(*/*) x2) 1.(*Num.num_of_int 1*)
(** @return the sum of floating point numbers *)
let sum_list = List.fold_left (+.) 0.0

let rand (s, e) seed =
  (float_of_int (Integer.rand seed)) /. 65536. *. (e -. s) +. s
