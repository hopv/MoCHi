open Util
open Combinator

(** Atoms on unit, booleans, integers, tuples, uninterpreted
    functions, and algebraic data structures *)
(** support uninterpreted predicates and user-defined predicates *)

(*include NumAtom*)

let disable_elim_lt_gt = ref false

(** {6 Morphisms} *)

(* does not support t1 =b t2 and t1 <>b t2 *)
let fold f atm =
  (*Logger.printf "folding %a@," Atom.pr atm;*)
  match atm |> Atom.term_of |> Term.fun_args with
  | Term.Var(x), ts -> f#fvar x ts
  | Term.Const(Const.Eq(ty)), [t1; t2] -> f#feq ty t1 t2
  | Term.Const(Const.Neq(ty)), [t1; t2] -> f#fneq ty t1 t2
  | Term.Const(Const.Lt(ty)), [t1; t2] -> f#flt ty t1 t2
  | Term.Const(Const.Gt(ty)), [t1; t2] -> f#fgt ty t1 t2
  | Term.Const(Const.Leq(ty)), [t1; t2] -> f#fleq ty t1 t2
  | Term.Const(Const.Geq(ty)), [t1; t2] -> f#fgeq ty t1 t2
  | Term.Const(Const.Divides(n)), [t] -> f#fdivides n t
  | Term.Const(c), ts -> f#fterm c ts
  | _ ->
    Logger.debug_assert_false ~on_failure:(fun () ->
        Format.printf "not supported (in CunAtom.fold): %a@," Atom.pr atm)
      ()
(*let fold f atm = Logger.log_block2 "CunAtom.fold" fold f atm*)

let fold_brel f =
  fold
    (object
      method fvar x ts = f#fvar x ts
      method feq ty t1 t2 = f#fbrel (Const.Eq(ty)) t1 t2
      method fneq ty t1 t2 = f#fbrel (Const.Neq(ty)) t1 t2
      method flt ty t1 t2 = f#fbrel (Const.Lt(ty)) t1 t2
      method fgt ty t1 t2 = f#fbrel (Const.Gt(ty)) t1 t2
      method fleq ty t1 t2 = f#fbrel (Const.Leq(ty)) t1 t2
      method fgeq ty t1 t2 = f#fbrel (Const.Geq(ty)) t1 t2
      method fdivides n t = f#fdivides n t
      method fterm c ts = f#fterm c ts
    end)

let fold_brel_ty f =
  fold_brel
    (object
      method fvar = f#fvar
      method fbrel c t1 t2 =
        if Const.is_ubrel c then f#fubrel c t1 t2
        else if Const.is_bbrel c then f#fbbrel c t1 t2
        else if Const.is_ibrel c then f#fibrel c t1 t2
        else if Const.is_rbrel c then f#frbrel c t1 t2
        else if Const.is_brel c then f#fbrel c t1 t2
        else
          Logger.debug_assert_false ~on_failure:(fun () ->
              Format.printf
                "error in CunAtom.find_brel_ty: %a@,"
                Atom.pr (Atom.mk_brel c t1 t2))
            ()
      method fdivides n t = f#fdivides n t
      method fterm c ts = f#fterm c ts
    end)

(** {6 Printers} *)

let pr ppf =
  fold_brel
    (object
      method fvar x ts =
        Format.fprintf ppf "%a(%a)" Idnt.pr x (List.pr Term.pr ",") ts
      method fbrel c t1 t2 =
        Format.fprintf ppf
          "%a %s %a"
          Term.pr t1 (Const.string_of_infix c) Term.pr t2
      method fdivides n t = Format.fprintf ppf "%d | %a" n Term.pr t
      method fterm c ts =
        Format.fprintf ppf "%s %a" (Const.string_of c) (List.pr Term.pr " ") ts
    end)
let _ = Atom.ext_pr := pr

(** {6 Operators} *)

let bnot =
  fold_brel
    (object
      method fvar x ts = Literal.mk_var x ts |> Literal.bnot
      (* Atom.eq Type.Bool t Formula.mk_false *)
      method fbrel c t1 t2 = Literal.mk_brel (Const.not c) t1 t2
      method fdivides n t = IntLiteral.divides n t |> Literal.bnot
      method fterm c ts = assert false
    end)

(** replace atoms [t1 < t2] and [t1 > t2] respectively with
    [t1 + 1 <= t2] and [t1 >= t2 + 1] *)
let elim_lt_gt =
  fold
    (object
      method fvar = Atom.mk_var
      method feq = Atom.eq
      method fneq = Atom.neq
      method flt ty t1 t2 =
        if not !disable_elim_lt_gt && Type.is_int ty then begin
          Logger.printf0 "elim_lt!!@,";
          NumAtom.leq ty (IntTerm.add t1 (IntTerm.one)) t2
        end else NumAtom.lt ty t1 t2
      method fgt ty t1 t2 =
        if not !disable_elim_lt_gt && Type.is_int ty then begin
          Logger.printf0 "elim_gt!!@,";
          NumAtom.geq ty t1 (IntTerm.add t2 (IntTerm.one))
        end else NumAtom.gt ty t1 t2
      method fleq =  NumAtom.leq
      method fgeq = NumAtom.geq
      method fdivides = IntAtom.divides
      method fterm = Atom.make
    end)
let elim_lt_gt =
  Logger.log_block1 "CunAtom.elim_lt_gt"
    ~before:(Logger.printf "input: %a@," Atom.pr)
    ~after:(Logger.printf "output: %a" Atom.pr)
    elim_lt_gt

(** replace atoms [t1 =b t2] and [t1 <>b t2]
    with [t1 iff t2] and [not (t1 iff t2)] respectively
    if [no_iff], then [iff] is encoded by [and, or, not]
    @require types inferred *)
let rec elim_beq_bneq no_iff atm =
  fold
    (object
      method fvar = Formula.mk_var
      method feq ty t1 t2 =
        if Type.is_bool ty then
          (t1, t2)
          |> Pair.lift Formula.of_term
          |> Pair.lift (Formula.map_atom (elim_beq_bneq no_iff))
          |> (if no_iff
              then uncurry2 Formula.mk_iff_disj
              else uncurry2 Formula.mk_iff)
        else NumFormula.eq ty t1 t2
      method fneq ty t1 t2 =
        if Type.is_bool ty then
          (t1, t2)
          |> Pair.lift Formula.of_term
          |> Pair.lift (Formula.map_atom (elim_beq_bneq no_iff))
          |> (if no_iff
              then uncurry2 Formula.mk_not_iff_conj
              else uncurry2 Formula.mk_iff >> Formula.bnot)
        else NumFormula.neq ty t1 t2
      method flt = NumFormula.lt
      method fgt = NumFormula.gt
      method fleq = NumFormula.leq
      method fgeq = NumFormula.geq
      method fdivides = IntFormula.divides
      method fterm = Formula.mk_atom
    end)
    atm
let elim_beq_bneq ?(no_iff = true) =
  Logger.log_block1 "CunAtom.elim_beq_bneq"
    ~before:(Logger.printf "input: %a@," Atom.pr)
    ~after:(Logger.printf "output: %a" Formula.pr)
    (elim_beq_bneq no_iff)

(** replace atoms [t1 <> t2] with [not t1 = t2]
    @note does not transform [t1] and [t2] in [t1 =b t2] and [t1 <>b t2] *)
let elim_neq_by_not_eq =
  fold
    (object
      method fvar = Literal.mk_var
      method feq = Literal.eq
      method fneq ty t1 t2 = Literal.eq ty t1 t2 |> Literal.bnot
      method flt = NumLiteral.lt
      method fgt = NumLiteral.gt
      method fleq = NumLiteral.leq
      method fgeq = NumLiteral.geq
      method fdivides = IntLiteral.divides
      method fterm = Literal.mk_atom
    end)

(** replace atoms [t1 > t2] with [t2 < t1] *)
let elim_gt =
  fold
    (object
      method fvar = Atom.mk_var
      method feq = Atom.eq
      method fneq = Atom.neq
      method flt = NumAtom.lt
      method fgt ty t1 t2 = NumAtom.lt ty t2 t1
      method fleq = NumAtom.leq
      method fgeq = NumAtom.geq
      method fdivides = IntAtom.divides
      method fterm = Atom.make
    end)

(** replace atoms [t1 >= t2] with [t2 <= t1] *)
let elim_geq =
  fold
    (object
      method fvar = Atom.mk_var
      method feq = Atom.eq
      method fneq = Atom.neq
      method flt = NumAtom.lt
      method fgt = NumAtom.gt
      method fleq = NumAtom.leq
      method fgeq ty t1 t2 = NumAtom.leq ty t2 t1
      method fdivides = IntAtom.divides
      method fterm = Atom.make
    end)

(** replace atoms [t1 <> t2] with [t1 < t2 || t1 > t2] *)
let elim_neq =
  fold
    (object
      method fvar = Formula.mk_var
      method feq = NumFormula.eq
      method fneq ty t1 t2 =
        if ty = Type.mk_int || ty = Type.mk_real || Type.is_var(*@todo*) ty
        then Formula.bor [NumFormula.lt ty t1 t2; NumFormula.gt ty t1 t2]
        else Formula.neq ty t1 t2
      method flt = NumFormula.lt
      method fgt = NumFormula.gt
      method fleq = NumFormula.leq
      method fgeq = NumFormula.geq
      method fdivides = IntFormula.divides
      method fterm = Formula.mk_atom
    end)

(** eliminate atoms "t1 = t2" and "t1 <> t2" respectively with
    "t1 <= t2 && t1 >= t2" and "t1 < t2 || t1 > t2" *)
let elim_eq_neq =
  fold
    (object
      method fvar = Formula.mk_var
      method feq ty t1 t2 =
        if ty = Type.mk_int || ty = Type.mk_real || Type.is_var(*@todo*) ty
        then Formula.band [NumFormula.leq ty t1 t2; NumFormula.geq ty t1 t2]
        else Formula.eq ty t1 t2
      method fneq ty t1 t2 =
        if ty = Type.mk_int || ty = Type.mk_real || Type.is_var(*@todo*) ty
        then Formula.bor [NumFormula.lt ty t1 t2; NumFormula.gt ty t1 t2]
        else Formula.neq ty t1 t2
      method flt = NumFormula.lt
      method fgt = NumFormula.gt
      method fleq = NumFormula.leq
      method fgeq = NumFormula.geq
      method fdivides = IntFormula.divides
      method fterm = Formula.mk_atom
    end)

let elim_neg =
  fold_brel_ty
    (object
      method fvar = Formula.mk_var
      method fubrel = Formula.mk_brel
      method fbbrel = Formula.mk_brel
      method fibrel c t1 t2 =
        try Formula.mk_brel c t1 t2 |> PolyIntRel.simplify_formula
        with Invalid_argument _ ->
          Format.printf "???: %a@," Formula.pr (Formula.mk_brel c t1 t2);
          assert false;
          Formula.mk_brel c t1 t2
      method frbrel = Formula.mk_brel
      method fbrel c t1 t2 =(*@todo*)
        try Formula.mk_brel c t1 t2 |> PolyIntRel.simplify_formula
        with Invalid_argument _ ->
          Format.printf "???: %a@," Formula.pr (Formula.mk_brel c t1 t2);
          assert false;
          Formula.mk_brel c t1 t2
      method fdivides = IntFormula.divides
      method fterm = Formula.mk_atom
    end)

let linearize =
  fold_brel_ty
    (object
      method fvar = Formula.mk_var
      method fubrel = Formula.mk_brel
      method fbbrel = Formula.mk_brel
      method fibrel c t1 t2 = Atom.mk_brel c t1 t2 |> IntAtom.linearize
      method frbrel = Formula.mk_brel(*@todo*)
      method fbrel = Formula.mk_brel
      method fdivides = IntFormula.divides
      method fterm = Formula.mk_atom
    end)

let real_to_int =
  fold_brel
    (object
      method fvar = Atom.mk_var
      method fbrel c t1 t2 =
        try
          Formula.mk_brel c t1 t2
          |> LinRealRel.of_formula
          |> LinRealRel.lin_rat_rel_of
          |> LinRationalRel.lin_int_rel_of
          |> LinIntRel.formula_of
          |> Formula.atom_of
        with Invalid_argument(_) ->
        try
          Atom.mk_brel
            (Const.real_to_int c)
            (CunTerm.real_to_int t1)
            (CunTerm.real_to_int t2)
        with Invalid_argument(_) -> Atom.mk_brel c t1 t2
      method fdivides = IntAtom.divides
      method fterm = Atom.make
    end)

let int_to_real =
  fold_brel
    (object
      method fvar = Atom.mk_var
      method fbrel c t1 t2 =
        Atom.mk_brel
          (Const.int_to_real c)
          (CunTerm.int_to_real t1)
          (CunTerm.int_to_real t2)
      method fdivides = IntAtom.divides
      method fterm = Atom.make
    end)

(** @require psub is a map *)
let subst_pvars psub =
  fold_brel
    (object
      method fvar p ts =
        try
          let tenv, phi = List.assoc p psub in
          Formula.subst
            (try List.map2 (fun (x, _) t -> x, t) tenv ts
             with _ ->
               Format.printf "p: %a@.tenv: %a@.ts: %a@."
                 Idnt.pr p TypEnv.pr tenv Term.pr_list ts;
               assert false)
            phi
        with Not_found -> Formula.mk_var p ts
      method fbrel = Formula.mk_brel
      method fdivides = IntFormula.divides
      method fterm = Formula.mk_atom
    end)

(** {6 Simplifiers} *)

let simplify_ub =
  fold_brel_ty
    (object
      method fvar = Atom.mk_var
      method fubrel = UnitAtom.simplify
      method fbbrel = BoolAtom.simplify
      method fibrel = Atom.mk_brel
      method frbrel = Atom.mk_brel
      method fbrel = Atom.mk_brel
      method fdivides = IntAtom.divides
      method fterm = Atom.make
    end)

let simplify =
  fold_brel_ty
    (object
      method fvar = Atom.mk_var
      method fubrel = UnitAtom.simplify
      method fbbrel = BoolAtom.simplify
      method fibrel c t1 t2 =
        Atom.mk_brel c (CunTerm.simplify t1) (CunTerm.simplify t2)
        |> elim_lt_gt |> IntAtom.simplify
      method frbrel c t1 t2 =
        Atom.mk_brel c (CunTerm.simplify t1) (CunTerm.simplify t2)
        |> RealAtom.simplify
      method fbrel c t1 t2 =
        let t1 = CunTerm.simplify t1 in
        let t2 = CunTerm.simplify t2 in
        match c with
        | Const.Eq ty ->
          if t1 = t2 then Atom.mk_true
          else Atom.eq ty t1 t2
        |  Const.Neq ty ->
          if t1 = t2 then Atom.mk_false
          else Atom.neq ty t1 t2
        | Const.Lt ty -> if t1 = t2 then Atom.mk_false else NumAtom.lt ty t1 t2
        | Const.Gt ty -> if t1 = t2 then Atom.mk_false else NumAtom.gt ty t1 t2
        | Const.Leq ty -> if t1 = t2 then Atom.mk_true else NumAtom.leq ty t1 t2
        | Const.Geq ty -> if t1 = t2 then Atom.mk_true else NumAtom.geq ty t1 t2
        | _ -> Atom.mk_brel c t1 t2
      method fdivides = IntAtom.divides
      method fterm = Atom.make
    end)
let simplify =
  Logger.log_block1 "CunAtom.simplify"
    ~before:(Logger.printf "input: %a@," Atom.pr)
    ~after:(Logger.printf "output: %a" Atom.pr)
    simplify

let negate =
  fold_brel
    (object
      method fvar x ts = Literal.mk_var x ts |> Literal.bnot
      method fbrel c t1 t2 =
        Atom.mk_brel (Const.not c) t1 t2 |> simplify |> Literal.of_atom
      method fdivides n t = IntLiteral.divides n t |> Literal.bnot
      method fterm c ts = Literal.mk_atom c ts |> Literal.bnot
    end)

(** {6 Inspectors} *)

let size =
  fold_brel
    (object
      method fvar x ts = Integer.sum_list (List.map CunTerm.size ts) + 1
      method fbrel c t1 t2 = CunTerm.size t1 + CunTerm.size t2 + 1
      method fdivides n t = CunTerm.size t + 1
      method fterm c ts = assert false
    end)

let sexp_of =
  fold
    (object
      method fvar x ts =
        if ts = [] then Idnt.string_of x
        else
          "(" ^
          Idnt.string_of x ^ " " ^
          String.concat " " (List.map CunTerm.sexp_of ts) ^
          ")"
      method feq ty t1 t2 =
        "(= " ^ CunTerm.sexp_of t1 ^ " " ^ CunTerm.sexp_of t2 ^ ")"
      method fneq ty t1 t2 =
        "(not (= " ^ CunTerm.sexp_of t1 ^ " " ^ CunTerm.sexp_of t2 ^ "))"
      method flt ty t1 t2 =
        "(< " ^ CunTerm.sexp_of t1 ^ " " ^ CunTerm.sexp_of t2 ^ ")"
      method fgt ty t1 t2 =
        "(> " ^ CunTerm.sexp_of t1 ^ " " ^ CunTerm.sexp_of t2 ^ ")"
      method fleq ty t1 t2 =
        "(<= " ^ CunTerm.sexp_of t1 ^ " " ^ CunTerm.sexp_of t2 ^ ")"
(*
          "(or " ^
            "(< " ^ CunTerm.sexp_of t1 ^ " " ^ CunTerm.sexp_of t2 ^ ") " ^
              "(= " ^ CunTerm.sexp_of t1 ^ " " ^ CunTerm.sexp_of t2 ^ "))"
 *)
      method fgeq ty t1 t2 =
        "(>= " ^ CunTerm.sexp_of t1 ^ " " ^ CunTerm.sexp_of t2 ^ ")"
(*
          "(or " ^
            "(< " ^ CunTerm.sexp_of t1 ^ " " ^ CunTerm.sexp_of t2 ^ ") " ^
              "(= " ^ CunTerm.sexp_of t1 ^ " " ^ CunTerm.sexp_of t2 ^ "))"
 *)
      method fdivides n t = assert false
      method fterm c ts = assert false
    end)

let is_linear =
  fold_brel_ty
    (object
      method fvar _ ts = List.for_all CunTerm.is_linear ts
      method fubrel _ t1 t2 = CunTerm.is_linear t1 && CunTerm.is_linear t2
      method fbbrel _ t1 t2 = CunTerm.is_linear t1 && CunTerm.is_linear t2
      method fibrel c t1 t2 = LinIntRel.is_linear (Formula.mk_brel c t1 t2)
      method frbrel c t1 t2 = CunTerm.is_linear t1 && CunTerm.is_linear t2
      (*@todo*)
      method fbrel _ t1 t2 = CunTerm.is_linear t1 && CunTerm.is_linear t2
      method fdivides _ t = CunTerm.is_linear t (* @todo*)
      method fterm c ts = false
    end)

let ufuns_of f_formula =
  fold_brel
    (object
      method fvar _ ts = List.concat_map (CunTerm.ufuns_of f_formula) ts
      method fbrel _ t1 t2 =
        CunTerm.ufuns_of f_formula t1 @ CunTerm.ufuns_of f_formula t2
      method fdivides _ t1 = CunTerm.ufuns_of f_formula t1
      method fterm c ts = List.concat_map (CunTerm.ufuns_of f_formula) ts
    end)

(* assume NNF *)
let elim_ufuns =
  fold
    (object
      method fvar = Atom.mk_var
      method feq ty t1 t2 =
        if CunTerm.has_ufun t1 || CunTerm.has_ufun t2
        then Atom.mk_true
        else Atom.eq ty t1 t2
      method fneq ty t1 t2 =
        if CunTerm.has_ufun t1 || CunTerm.has_ufun t2
        then Atom.mk_true
        else Atom.neq ty t1 t2
      method flt = NumAtom.lt
      method fgt = NumAtom.gt
      method fleq = NumAtom.leq
      method fgeq = NumAtom.geq
      method fdivides = IntAtom.divides
      method fterm = Atom.make
    end)
