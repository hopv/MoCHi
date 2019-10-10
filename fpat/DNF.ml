open Util
open Combinator
open Formula

type t = Cube.t list

(** {6 Auxiliary destructors} *)

let cubes_of = id
let disjunction_of = List.map (Cube.formula_of)
let formula_of = disjunction_of >> Disjunction.formula_of

(** {6 Printers} *)

let pr ppf = formula_of >> Format.fprintf ppf "%a" Formula.pr

(** {6 Auxiliary constructors} *)

let of_formula =
  Formula.fold
    (object
      method fatom atm = fun b ->
        if b then
          [[ atm |> Literal.of_atom ]]
        else
          [[ atm |> Literal.of_atom |> Literal.bnot ]]
      method ftrue () = fun b ->
        if b then
          [[]]
        else
          []
      method ffalse () = fun b ->
        if b then
          []
        else
          [[]]
      method fnot r = fun b ->
        r (not b)
      method fand r1 r2 = fun b ->
        if b then
          Vector.multiply (@) (r1 b) (r2 b)
        else
          r1 b @ r2 b
      method for_ r1 r2 = fun b ->
        if b then
          r1 b @ r2 b
        else
          Vector.multiply (@) (r1 b) (r2 b)
      method fimply r1 r2 = fun b ->
        if b then
          r1 (not b) @ r2 b
        else
          Vector.multiply (@) (r1 (not b)) (r2 b)
      method fiff r1 r2 = fun b ->
        if b then
          Vector.multiply (@) (r1 b) (r2 b) @
          Vector.multiply (@) (r1 (not b)) (r2 (not b))
        else
          Vector.multiply (@) (r1 (not b)) (r2 b) @
          Vector.multiply (@) (r2 (not b)) (r1 b)
      method fforall _ _ = fun b ->
        raise (Global.NotImplemented "DNF.of_formula")
      method fexists _ _ = fun b ->
        raise (Global.NotImplemented "DNF.of_formula")
    end)
let of_formula phi = of_formula phi true

(** {6 Morphisms} *)

let map_cube f = List.map f
let map_literal f = map_cube (List.map f)
