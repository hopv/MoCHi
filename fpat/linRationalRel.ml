open Util
open Combinator
open Term

(** Linear relations with rational coefficients *)

let lin_int_rel_of (c, (kxs, k)) =
  let lcm = Integer.lcm_list (snd k :: List.map (fst >> snd) kxs) in
  (Const.real_to_int c,
   (List.map (Pair.map_fst (fun k -> fst k * lcm / snd k)) kxs,
    fst k * lcm / snd k))
