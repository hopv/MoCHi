open Util
open Combinator

(** Atoms on reals *)

let simplify atm =
  atm
  |> Formula.of_atom
  |> (try_ LinRealRel.simplify_formula
        (function
          | Invalid_argument _ ->
            try_ PolyRealRel.simplify_formula
              (function
                | Invalid_argument _ ->
                  Atom.pr Format.std_formatter atm;
                  assert false
                | e -> raise e)
          | e -> raise e))
  |> Formula.atom_of

let eq t1 t2 = Atom.eq Type.mk_real t1 t2
let neq t1 t2 = Atom.neq Type.mk_real t1 t2
let gt t1 t2 = NumAtom.gt Type.mk_real t1 t2
let lt t1 t2 = NumAtom.lt Type.mk_real t1 t2
let geq t1 t2 = NumAtom.geq Type.mk_real t1 t2
let leq t1 t2 = NumAtom.leq Type.mk_real t1 t2

let eq0 t = eq t RealTerm.zero |> Formula.of_atom
let neq0 t = neq t RealTerm.zero |> Formula.of_atom
let gt0 t = gt t RealTerm.zero |> Formula.of_atom
let lt0 t = lt t RealTerm.zero |> Formula.of_atom
let geq0 t = geq t RealTerm.zero |> Formula.of_atom
let leq0 t = leq t RealTerm.zero |> Formula.of_atom
