open Util
open Combinator

include Formula

(** {6 Auxiliary destructors} *)

let formula_of = id

(** {6 Auxiliary constructors} *)

let of_formula =
  fold
    (object
      method fatom atm = fun b ->
        if b then of_atom atm else atm |> of_atom |> bnot
      method ftrue () = fun b ->
        if b then mk_true else mk_false
      method ffalse () = fun b ->
        if b then mk_false else mk_true
      method fnot r = fun b ->
        r (not b)
      method fand r1 r2 = fun b ->
        if b then band [r1 b; r2 b] else bor [r1 b; r2 b]
      method for_ r1 r2 = fun b ->
        if b then bor [r1 b; r2 b] else band [r1 b; r2 b]
      method fimply r1 r2 = fun b ->
        if b then bor [r1 (not b); r2 b] else band [r1 (not b); r2 b]
      method fiff r1 r2 = fun b ->
        if b then band [bor [r1 (not b); r2 b]; bor [r1 b; r2 (not b)]]
        else bor [band [r1 (not b); r2 b]; band [r1 b; r2 (not b)]]
      method fforall xty r1 = fun b ->
        if b then forall [xty] (r1 b) else exists [xty] (r1 b)
      method fexists xty r1 = fun b ->
        if b then exists [xty] (r1 b) else forall [xty] (r1 b)
    end)
let of_formula phi = of_formula phi true
let of_formula =
  Logger.log_block1 "NNF.of_formula"
    ~before:(Logger.printf "input: %a@," pr)
    ~after:(Logger.printf "output: %a" pr)
    of_formula

(** {6 Morphisms} *)

let map_literal f =
  para
    (object
      method fatom = Literal.of_atom >> f >> Literal.formula_of
      method ftrue () = mk_true
      method ffalse () = mk_false
      method fnot phi _ =
        (* @invariant phi is an atom *)
        phi
        |> Literal.of_formula
        |> Literal.bnot
        |> f
        |> Literal.formula_of
      method fand _ phi1' _ phi2' = band [phi1'; phi2']
      method for_ _ phi1' _ phi2' = bor [phi1'; phi2']
      method fimply _ _ _ _ = assert false
      method fiff _ _ _ _ = assert false
      method fforall xty _ phi' = forall [xty] phi'
      method fexists xty _ phi' = exists [xty] phi'
    end)
