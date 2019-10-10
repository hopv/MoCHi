open Util
open Combinator

(** Linear relations *)

module Make = functor (Coeff : Coeff.COEFF) -> struct
  module Exp = LinExp.Make(Coeff)

  type t = Const.t * Exp.t

  (** {6 Printers} *)

  (* val pr : Format.formatter -> t -> unit *)
  let pr ppf (c, lin) =
    Format.fprintf ppf "%a %s 0" Exp.pr lin (Const.string_of_infix c)
  let pr_list ppf ls = Format.fprintf ppf "@[<v>%a@]" (List.pr pr "@,") ls

  (** {6 Auxiliary constructors} *)

  (* val make : Const.t -> LinIntExp.t -> t *)
  let make c lin = c, lin

  (** {6 Inspectors} *)

  let fvs (c, lin) = Exp.fvs lin

  let coeffs_of vs (c, lin) =
    Exp.const lin ::
    List.map
      (fun v -> try Exp.coeff lin v with Not_found -> Exp.coeff_zero)
      vs,
    c
end
