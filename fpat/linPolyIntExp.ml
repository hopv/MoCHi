open Util
open Combinator

(** Linear expressions with integer polynomial coefficients *)

module Coeff = struct
  type t = PolyIntExp.t
  let make = PolyIntExp.of_int
  let to_int _ = assert false
  let pr = PolyIntExp.pr
  let zero = PolyIntExp.zero
  let one = PolyIntExp.one
  let (=) = PolyIntExp.equiv
  let (>) = PolyIntExp.(>)
  let (+) = PolyIntExp.add
  let ( * ) = PolyIntExp.mul
  let ( / ) = PolyIntExp.div
  let simplify n = n
  let gcd _ = assert false
end
include LinExp.Make(Coeff)
