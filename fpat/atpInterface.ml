open Combinator
open Util
open Term

let of_term =
  CunTerm.fold
    (object
      method fvar x [] = Atp_batch.Var(Idnt.serialize x)
      method funit () = assert false
      method ftrue () = assert false
      method ffalse () = assert false
      method fint n = Atp_batch.Fn(string_of_int n, [])
      method fbigint n = Atp_batch.Fn(Big_int_Z.string_of_big_int n, [])
      method frational _ _ = assert false
      method freal f = Atp_batch.Fn(string_of_float f, [])
      method fstring _ = assert false
      method fneg _ r = Atp_batch.Fn("-", [r])
      method fadd _ r1 r2 = Atp_batch.Fn("+", [r1; r2])
      method fsub _ r1 r2 = Atp_batch.Fn("-", [r1; r2])
      method fmul _ r1 r2 = Atp_batch.Fn("*", [r1; r2])
      method fdiv _ r1 r2 = assert false
      method fmax _ r1 r2 = assert false
      method fmin _ r1 r2 = assert false
      method fmod r1 r2 = assert false
      method ftuple _ _ = assert false
      method fproj _ _ _ = assert false
      method fsempty ty = assert false
      method fsadd ty r1 r2 = assert false
      method fsunion ty r1 r2 = assert false
      method fsintersect ty r1 r2 = assert false
      method fsdiff ty r1 r2 = assert false
      method fscomplement ty r = assert false
      method fkon _ _ _ = assert false
      method faccessor _ _ _ _ = assert false
      method fufun _ _ _ = assert false
      method farray n rs = assert false
      method faget a n = assert false
      method faset a n m e = assert false
      method fcoerce ty t = assert false
      method fformula phi = assert false
    end)

let of_atom =
  CunAtom.fold
    (object
      method fvar x ts = assert false
      method feq ty t1 t2 =
        Atp_batch.Atom(Atp_batch.R("=", [of_term t1; of_term t2]))
      method fneq ty t1 t2 =
        (* do we need this even though Nelson-Oppen does not support "<>"? *)
        Atp_batch.Not
          (Atp_batch.Atom(Atp_batch.R("=", [of_term t1; of_term t2])))
      method flt ty t1 t2 =
        Atp_batch.Atom(Atp_batch.R("<", [of_term t1; of_term t2]))
      method fgt ty t1 t2 =
        Atp_batch.Atom(Atp_batch.R(">", [of_term t1; of_term t2]))
      method fleq ty t1 t2 =
        Atp_batch.Atom(Atp_batch.R("<=", [of_term t1; of_term t2]))
      method fgeq ty t1 t2 =
        Atp_batch.Atom(Atp_batch.R(">=", [of_term t1; of_term t2]))
      method fdivides n t = assert false
      method frecognizer ty x t1 = assert false
      method fsmem ty x t1 = assert false
      method fssubset ty x t1 = assert false
      method fterm c ts = assert false
    end)

let of_formula =
  Formula.fold
    (object
      method fatom atm = atm |> of_atom
      method ftrue () = Atp_batch.True
      method ffalse () = Atp_batch.False
      method fnot s = Atp_batch.Not(s)
      method fand s1 s2 = Atp_batch.And(s1, s2)
      method for_ s1 s2 = Atp_batch.Or(s1, s2)
      method fimply s1 s2 = Atp_batch.Imp(s1, s2)
      method fiff s1 s2 = Atp_batch.Iff(s1, s2)
      method fforall (x, _) s = Atp_batch.Forall(Idnt.serialize x , s)
      method fexists (x, _) s = Atp_batch.Exists(Idnt.serialize x , s)
    end)

let rec term_of = function
  | Atp_batch.Var(id) ->
    Term.mk_var (Idnt.deserialize id)
  | Atp_batch.Fn(s, []) when String.is_int s ->
    IntTerm.make (int_of_string s)
  | Atp_batch.Fn("+", [t1; t2]) ->
    IntTerm.add (term_of t1) (term_of t2)
  | Atp_batch.Fn("-", [t1; t2]) ->
    IntTerm.sub (term_of t1) (term_of t2)
  | Atp_batch.Fn("*", [t1; t2]) ->
    IntTerm.mul (term_of t1) (term_of t2)
  | Atp_batch.Fn("-", [t]) ->
    IntTerm.neg (term_of t)
  | Atp_batch.Fn(s, ts) ->
    raise (Global.NotImplemented "AtpInterface.term_of")

let rec formula_of p =
  match p with
  | Atp_batch.True ->
    Formula.mk_true
  | Atp_batch.False ->
    Formula.mk_false
  | Atp_batch.Not(p) ->
    Formula.bnot (formula_of p)
  | Atp_batch.And(p1, p2) ->
    Formula.band [formula_of p1; formula_of p2]
  | Atp_batch.Or(p1, p2) ->
    Formula.bor [formula_of p1; formula_of p2]
  | Atp_batch.Imp(p1, p2) ->
    Formula.imply (formula_of p1) (formula_of p2)
  | Atp_batch.Iff(p1, p2) ->
    Formula.mk_iff (formula_of p1) (formula_of p2)
  | Atp_batch.Forall(x, p) ->
    Formula.forall [Idnt.deserialize x, Type.mk_int(*@todo*)] (formula_of p)
  | Atp_batch.Exists(x, p) ->
    Formula.exists [Idnt.deserialize x, Type.mk_int(*@todo*)] (formula_of p)
  | Atp_batch.Atom(Atp_batch.R("=", [t1; t2])) ->
    IntFormula.eq (term_of t1) (term_of t2)
  | Atp_batch.Atom(Atp_batch.R("<", [t1; t2])) ->
    IntFormula.lt (term_of t1) (term_of t2)
  | Atp_batch.Atom(Atp_batch.R("<=", [t1; t2])) ->
    IntFormula.leq (term_of t1) (term_of t2)
  | Atp_batch.Atom(Atp_batch.R(">", [t1; t2])) ->
    IntFormula.gt (term_of t1) (term_of t2)
  | Atp_batch.Atom(Atp_batch.R(">=", [t1; t2])) ->
    IntFormula.geq (term_of t1) (term_of t2)
  | Atp_batch.Atom(Atp_batch.R("divides", [t1; t2])) ->
    raise (Global.NotImplemented "AtpInterface.formula_of: divides")
  (*IntFormula.divides (term_of t1) (term_of t2)*)
  | _ ->
    Atp_batch.print_formula Atp_batch.print_atom p;
    print_newline();
    Logger.debug_assert_false ()

(** {6 Functions for ATP formulas} *)

let theory =
  let theory_bool = (* true <> false *)
    Atp_batch.Not
      (Atp_batch.Atom
         (Atp_batch.R
            ("=", [Atp_batch.Fn("true", []);
                   Atp_batch.Fn("false", [])])))
  in
  let theory_list = (* forall x. len x >= 0 *)
    let id = Idnt.string_of (Idnt.new_var ()) in
    Atp_batch.Forall
      (id,
       Atp_batch.Atom
         (Atp_batch.R
            (">=",
             [Atp_batch.Fn("len", [Atp_batch.Var(id)]);
              Atp_batch.Fn("0", [])])))
  in
  theory_bool
(*Atp_batch.And(theory_bool, theory_list)*)

let langs = Atp_batch.add_default [Atp_batch.int_lang]

let is_valid_atp p = Atp_batch.nelop langs (Atp_batch.Imp(theory, p))
let is_valid_atp =
  Logger.log_block1
    "AtpInterface.is_valid_atp"
    ~before:(formula_of >> Logger.printf "input: %a@," Formula.pr)
    is_valid_atp

(** {6 Functions for formulas} *)

let real_qelim =
  Formula.map_atom (CunAtom.elim_beq_bneq ~no_iff:false)
  >> of_formula
  >> Atp_batch.real_qelim
  >> formula_of
  >> FormulaSimplifier.simplify
let real_qelim =
  Logger.log_block1
    "AtpInterface.real_qelim"
    ~before:(Logger.printf "input: %a@," Formula.pr)
    ~after:(Logger.printf "output: %a" Formula.pr)
    real_qelim

let integer_qelim =
  Formula.map_atom (CunAtom.elim_beq_bneq ~no_iff:false)
  >> of_formula
  >> Atp_batch.integer_qelim
  >> formula_of
  >> FormulaSimplifier.simplify
let integer_qelim =
  Logger.log_block1
    "AtpInterface.integer_qelim"
    ~before:(Logger.printf "input: %a@," Formula.pr)
    ~after:(Logger.printf "output: %a" Formula.pr)
    integer_qelim

let cnf =
  of_formula
  >> Atp_batch.simplify
  >> Atp_batch.cnf
  >> formula_of
  >> FormulaSimplifier.simplify

let rec eval = function
  | Atp_batch.Var(_) -> assert false
  | Atp_batch.Fn("+", [s; t]) -> eval s + eval t
  | Atp_batch.Fn("-", [s; t]) -> eval s - eval t
  | Atp_batch.Fn("*", [s; t]) -> eval s * eval t
  | Atp_batch.Fn("-", [s]) -> -eval s
  | Atp_batch.Fn(s, []) when String.is_int s -> int_of_string s
  | _ -> assert false

let is_valid = of_formula >> is_valid_atp

let _ =
  Qelim.ext_integer_qelim := integer_qelim;
  Qelim.ext_real_qelim := real_qelim
