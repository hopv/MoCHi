open Util
open Combinator
open Term

include Formula

(** {6 Auxiliary destructors} *)

let formula_of = id
let atom_of = term_of >> Atom.of_term

(** {6 Auxiliary constructors} *)

let mk_atom c ts = Term.mk_app (Term.mk_const c) ts |> of_term
let of_formula = id
let of_atom = Atom.term_of >> of_term

let eq ty t1 t2 = Atom.eq ty t1 t2 |> of_atom
let neq ty t1 t2 = Atom.neq ty t1 t2 |> of_atom

(** {6 Morphisms} *)

let fold fp fn lit =
  match lit |> term_of |> fun_args with
  | Const(Const.Not), [t] -> fn (Atom.of_term t)
  | _ -> fp (atom_of lit)

(** {6 Inspectors} *)

let is_pos = fold (fun _ -> true) (fun _ -> false)
let is_pva pvs = fold (Atom.is_pva pvs) (Atom.is_pva pvs)
