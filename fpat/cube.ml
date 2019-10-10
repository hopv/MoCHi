open Util
open Combinator

type t = Literal.t list

(** {6 Printers} *)

let pr ppf = Format.fprintf ppf "@[<hov>%a@]" (List.pr Literal.pr " /\\@ ")

(** {6 Auxiliary constructors} *)

exception NonCube

let of_formula =
  NNF.of_formula
  >> NNF.formula_of
  >> Formula.lazy_para
    (object
      method fatom atm = [atm |> Literal.of_atom]
      method ftrue () = []
      method ffalse () = [Literal.mk_false]
      method fnot phi _ = [phi |> Literal.of_formula |> Literal.bnot]
      method fand _ ls1 _ ls2 = Lazy.force ls1 @ Lazy.force ls2
      method for_ _ _ _ _ = raise NonCube
      method fimply _ _ _ _ = raise NonCube
      method fiff _ _ _ _ = raise NonCube
      method fforall _ _ _ = raise NonCube
      method fexists _ _ _ = raise NonCube
    end)

(** {6 Auxiliary destructors} *)

let conjunction_of = List.map Literal.formula_of
let formula_of = conjunction_of >> Conjunction.formula_of
