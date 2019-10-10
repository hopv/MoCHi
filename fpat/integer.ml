open Util
open Combinator

(** Integers *)

let pr ppf n = Format.fprintf ppf "%d" n

(** @return the factorial of n *)
let rec fact n = if n = 0 then 1 else n * fact (n - 1)
(** @return n1 to the power of n2 *)
let rec pow n1 n2 = if n2 = 0 then 1 else n1 * pow n1 (n2 - 1)
(** the greatest representable integer *)
let max_int = pow 2 30 - 1
(** the smallest representable integer *)
let min_int = -pow 2 30
(** @return the product of the integers from 1 to n *)
(** @return the sum of the integers from 0 to n *)
let rec sum n = if n = 0 then 0 else n + sum (n - 1)
(* let sum = fold_left (fun x -> fun y -> x + y) 0 *)
(** @return the sum of integers ns *)
let sum_list ns = List.fold_left (+) 0 ns
let rec prod n = if n = 1 then 1 else n * prod (n - 1)
(** @return the product of integers ns *)
let prod_list ns = List.fold_left ( * ) 1 ns
(** @return the maximum of integers *)
let max = max
(** @return the maximum of integers ns *)
let max_list = function
  | [] -> assert false
  | n :: ns' -> List.fold_left max n ns'
(** @return the minimum of integers
    @ensure -(min x y) = max (-x) (-y) *)
let min = min
(** @return the minimum of integers *)
let min_list = function
  | [] -> assert false
  | n :: ns' -> List.fold_left min n ns'
let rec gcd n1 n2 =
  if n2 = 0 then n1 |> abs (* we need this because (-6) mod 4 = -2 in OCaml *)
  else gcd n2 (n1 mod n2)
(** @return the greatest common divisor of n1 and n2
    @ensure gcd 0 0 = 0 *)
let gcd = Logger.log_block2 "Integer.gcd" gcd
let gcd_list ns = List.fold_left gcd 0 ns
(** @return the greatest common divisor of integers ns
    @ensure gcd_list [0; ...; 0] = 0 *)
let gcd_list = Logger.log_block1 "Integer.gcd_list" gcd_list
let lcm n1 n2 = if n1 = 0 && n2 = 0 then 0 else n1 * n2 / gcd n1 n2
(** @return the least common multiplier of n1 and n2
    @ensure lcm 0 0 = 0 *)
let lcm = Logger.log_block2 "Integer.lcm" lcm
let lcm_list (n :: ns) = List.fold_left lcm n ns
(** @return the least common multiplier of integers ns
    @ensure lcm_list [0; ...; 0] = 0 *)
let lcm_list = Logger.log_block1 "Integer.lcm_list" lcm_list
let rand seed =
  let multiplier = 25173 in
  let increment = 13849 in
  let modulus = 65536 in
  (multiplier * seed + increment) mod modulus
