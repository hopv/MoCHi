open Util
open Combinator

(** Coefficients *)

module type COEFF = sig
  type t
  val make : int -> t
  val to_int : t -> int
  val pr : Format.formatter -> t -> unit
  val zero : t
  val one : t
  val (=) : t -> t -> bool
  val (>) : t -> t -> bool
  val (+) : t -> t -> t
  val ( * ) : t -> t -> t
  val (/) : t -> t -> t
  val simplify : t -> t
  val gcd : t list -> t
end

module CoeffInt = struct
  type t = int
  let make n = n
  let to_int n = n
  let pr ppf n = Integer.pr ppf n
  let zero = 0
  let one = 1
  let (=) = (=)
  let (>) = (>)
  let (+) = (+)
  let ( * ) = ( * )
  let (/) = (/)
  let simplify n = n
  let gcd = List.map abs >> Integer.gcd_list
end

module CoeffReal = struct
  type t = float
  let make n = float_of_int n
  let to_int f = int_of_float f
  let pr ppf n = Float.pr ppf n
  let zero = 0.0
  let one = 1.0
  let (=) = (=)
  let (>) = (>)
  let (+) = (+.)
  let ( * ) = ( *. )
  let (/) = (/.)
  let simplify n = n
  let gcd _ = 1.0
end

module CoeffRat = struct
  type t = int * int
  let make n = (n, 1)
  let to_int (n1, n2) = n1 / n2
  let pr ppf (n1, n2) = Format.fprintf ppf "%a/%a" Integer.pr n1 Integer.pr n2
  let zero = (0, 0)
  let one = (1, 0)
  let (=) = (=)
  let (>) (n11, n12) (n21, n22) = n11 * n22 > n12 * n21
  let (+) (n11, n12) (n21, n22) = (n11 * n22 + n12 * n21, n12 * n22)
  let (/) (n11, n12) (n21, n22) = (n11 * n22, n12 * n21)
  let ( * ) (n11, n12) (n21, n22) = (n11 * n21, n12 * n22)
  let simplify (n1, n2) = (n1, n2)
  let gcd _ = assert false
end

let int_to_real c = CoeffReal.make (CoeffInt.to_int c)
