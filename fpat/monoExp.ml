open Util
open Combinator

(** Monomial expressions *)

module Make = functor (Coeff : Coeff.COEFF) -> struct
  type t = Coeff.t * Idnt.t list

  (** {6 Auxiliary constructors} *)

  (* val of_int : int -> t *)
  let of_int n = Coeff.make n, []

  (** {6 Printers} *)

  (* val pr : Format.formatter -> t -> unit *)
  let pr ppf (n, xs) =
    let open Coeff in
    if n > make 0 then
      if n = make 1 then
        Format.fprintf
          ppf
          "%a"
          (List.pr Idnt.pr " ") xs
      else
        Format.fprintf
          ppf
          "%a %a"
          Coeff.pr n
          (List.pr Idnt.pr " ") xs
    else if n < make 0 then
      if n = make (-1) then
        Format.fprintf
          ppf
          "(-%a)"
          (List.pr Idnt.pr " ") xs
      else
        Format.fprintf
          ppf
          "(-%a %a)"
          Coeff.pr (make (-1) * n)
          (List.pr Idnt.pr " ") xs
    else
      assert false

  (** {6 Operators} *)

  (* val normalize : t -> t *)
  let normalize (n, xs) =
    n, List.sort compare xs

  (* val mul_coeff : Coeff.t -> t -> t *)
  let mul_coeff m (n, xs) =
    let open Coeff in
    m * n, xs
end
