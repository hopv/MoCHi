open Util
open Combinator
open Term

(** Formulas on unit, booleans, integers, and predicate variable applications *)

(*
val eq_pva : Pva.t -> Pva.t -> Formula.t
 *)
let eq_pva pva1 pva2 =
  Pva.fold (fun p1 tts1 ->
      Pva.fold (fun p2 tts2 ->
          assert (p1 = p2);
          List.map2 NumFormula.eq_tt tts1 tts2 |> Formula.band)
        pva2)
    pva1

let size =
  Formula.fold
    (object
      method fatom atm = CunAtom.size atm
      method ftrue () = 1
      method ffalse () = 1
      method fnot s = s + 1
      method fand s1 s2 = s1 + s2 + 1
      method for_ s1 s2 = s1 + s2 + 1
      method fimply s1 s2 = s1 + s2 + 1
      method fiff s1 s2 = s1 + s2 + 1
      method fforall _ s1 = s1 + 1
      method fexists _ s1 = s1 + 1
    end)

let sexp_of ?(smt2=false) =
  let imply = if smt2 then "=> " else "implies " in
  Formula.fold
    (object
      method fatom = CunAtom.sexp_of
      method ftrue () = "true"
      method ffalse () = "false"
      method fnot s = "(not " ^ s ^ ")"
      method fand s1 s2 = "(and " ^ s1 ^ " " ^ s2 ^ ")"
      method for_ s1 s2 = "(or " ^ s1 ^ " " ^ s2 ^ ")"
      method fimply s1 s2 = "(" ^ imply ^ s1 ^ " " ^ s2 ^ ")"
      method fiff s1 s2 = "(iff " ^ s1 ^ " " ^ s2 ^ ")"
      method fforall (x, ty) s = assert false
      method fexists (x, ty) s = assert false
    end)


let is_pvar p = String.starts_with p "|$" && String.ends_with p "|"

let pvar_of p = String.sub p 2 (String.length p - 3) |> Idnt.make

(* @assume: let bindings are used only for formulas *)
let rec of_sexp is_real pvars env =
  let term_of_sexp = if is_real then RealTerm.of_sexp else IntTerm.of_sexp in
  function
  | Sexp.L(Sexp.S(p) :: es) when is_pvar p ->
    Pva.make
      (pvar_of p)
      (List.map (fun e -> term_of_sexp e,
                          if is_real then Type.mk_real
                          else Type.mk_int) es)
    |> Pva.to_formula
  | Sexp.L(Sexp.S(p) :: es) when List.mem p pvars ->
    Pva.make
      (Idnt.make p)
      (List.map (fun e -> term_of_sexp e,
                          if is_real then Type.mk_real
                          else Type.mk_int) es)
    |> Pva.to_formula
  | Sexp.S(p) when List.mem p pvars -> (* 0-ary predvar app *)
    Pva.make (Idnt.make p) [] |> Pva.to_formula
  | Sexp.L(Sexp.S("=") :: e1 :: e2 :: []) ->
    IntFormula.eq (term_of_sexp e1) (term_of_sexp e2)
  | Sexp.L(Sexp.S("<") :: e1 :: e2 :: []) ->
    IntFormula.lt (term_of_sexp e1) (term_of_sexp e2)
  | Sexp.L(Sexp.S(">") :: e1 :: e2 :: []) ->
    IntFormula.gt (term_of_sexp e1) (term_of_sexp e2)
  | Sexp.L(Sexp.S("<=") :: e1 :: e2 :: []) ->
    IntFormula.leq (term_of_sexp e1) (term_of_sexp e2)
  | Sexp.L(Sexp.S(">=") :: e1 :: e2 :: []) ->
    IntFormula.geq (term_of_sexp e1) (term_of_sexp e2)
  | Sexp.S("true") -> Formula.mk_true
  | Sexp.S("false") -> Formula.mk_false
  | Sexp.S(x) when List.mem_assoc x env -> (* let bounded boolean variable *)
    List.assoc x env
  | Sexp.L(Sexp.S("not") :: e :: []) ->
    Formula.bnot (of_sexp is_real pvars env e)
  | Sexp.L(Sexp.S("and") :: es) ->
    Formula.band (List.map (of_sexp is_real pvars env) es)
  | Sexp.L(Sexp.S("or") :: es) ->
    Formula.bor (List.map (of_sexp is_real pvars env) es)
  | Sexp.L(Sexp.S("implies") :: e1 :: e2 :: [])
  | Sexp.L(Sexp.S("=>") :: e1 :: e2 :: []) ->
    Formula.imply
      (of_sexp is_real pvars env e1)
      (of_sexp is_real pvars env e2)
  | Sexp.L(Sexp.S("iff") :: e1 :: e2 :: []) ->
    Formula.mk_iff
      (of_sexp is_real pvars env e1)
      (of_sexp is_real pvars env e2)
  | Sexp.L(Sexp.S("forall") :: tenv :: e :: []) ->
    (* Formula.forall (TypEnv.of_sexp tenv) (of_sexp is_real pvars env e) *)
    of_sexp is_real pvars env e
  | Sexp.L(Sexp.S("exists") :: tenv :: e :: []) ->
    Formula.exists (TypEnv.of_sexp tenv) (of_sexp is_real pvars env e)
  | Sexp.L(Sexp.S("let") :: binds :: e :: []) ->
    let env = mk_binding_env is_real pvars env binds @ env in
    of_sexp is_real pvars env e
  | e ->
    Format.printf "sexp: %a@," Sexp.pr e;
    assert false
and mk_binding_env is_real pvars env = function
  | Sexp.L(ps) ->
    ps
    |> List.map
      (function
        | Sexp.L([Sexp.S(x); e]) -> x, of_sexp is_real pvars env e
        | e ->
          Format.printf "sexp(pat): %a@," Sexp.pr e;
          assert false)
  | e ->
    Format.printf "sexp(binds): %a@," Sexp.pr e;
    assert false
let of_sexp ?(is_real=false) ?(pvars=[]) ?(env=[]) =
  of_sexp is_real pvars env

(** {6 Inspectors} *)

(** @return whether t does not contain a subexpression of the type unit *)
let is_wo_unit phi =
  raise (Global.NotImplemented "CunFormula.is_wo_unit")
let is_wo_unit_var phi = Formula.fvs_unit phi = []
let is_wo_bool_var phi = Formula.fvs_bool phi = []

(** @return a formula [s] s.t. [equiv s t && is_wo_unit s] *)
let elim_unit phi =
  Formula.map_atom (CunAtom.simplify_ub >> Formula.of_atom) phi
let elim_unit = Logger.log_block1 "CunFormula.elim_unit" elim_unit

(** case analysis on possible valuations for boolean variables *)
let case_analysis_boolean simplify f phis =
  let bool_vars =
    phis
    |> List.concat_map Formula.fvs_bool
    |> List.unique
  in
  if bool_vars = [] then f phis
  else
    let venvs = TypTermSubst.bool_valuations bool_vars in
    venvs
    |> List.map
      (fun venv ->
         phis
         |> List.map (Formula.subst (TypTermSubst.tsub_of venv)
                      >> simplify)
         |> f)
    |> List.map2
      (fun venv phi -> Formula.band [phi; Formula.of_ttsub venv])
      venvs
    |> Formula.bor
let case_analysis_boolean =
  Logger.log_block3
    "CunFormula.case_analysis_boolean"
    ~before:(fun _ _ -> Logger.printf "phis: %a@," (List.pr Formula.pr ","))
    case_analysis_boolean

let linearize = Formula.map_atom CunAtom.linearize


(* val of_c_formula : t -> t *)
let of_c_formula =
  Formula.map_atom
    (fun atm ->
       match atm |> Atom.term_of |> Term.fun_args with
       | Var(_), [] ->
         if true(*@todo ty = Type.mk_int*) then
           Atom.neq Type.mk_int (atm |> Atom.term_of) IntTerm.zero
           |> Formula.of_atom
         else if false(*ty = Type.mk_bool*) then Formula.of_atom atm
         else assert false
       | Const(bop), [_; _] ->
         let [_; _], ty = Type.args_ret (Const.type_of bop) in
         if ty = Type.mk_int then
           Atom.neq Type.mk_int (atm |> Atom.term_of) IntTerm.zero
           |> Formula.of_atom
         else if ty = Type.mk_bool then Formula.of_atom atm
         else assert false
       | _ -> assert false)

(** check whether the conjunction of [phis1] implies that of [phis2] *)
let mk_implies simplify is_valid phis1 phis2 =
  Set_.diff phis2 phis1
  |> ExtConjunction.simplify simplify
  |> (if_ ((=) [])
        (const true)
        (Formula.band >> Formula.imply (Formula.band phis1) >> is_valid))

(* obsolete? *)
(* phi1 and phi2 share only variables that satisfy p *)
let mk_implies_bvs simplify is_valid p phi1 phi2 =
  let phi1 =
    Formula.fresh (phi1 |> Formula.fvs |> List.filter (p >> not)) phi1
  in
  let phi2 =
    Formula.fresh (phi2 |> Formula.fvs |> List.filter (p >> not)) phi2
  in
  mk_implies simplify is_valid [phi1] [phi2]

(* val is_disjunctive : t -> bool *)
let is_disjunctive =
  DNF.of_formula >> DNF.disjunction_of >> List.length >> (<=) 2

(** @deprecated ?? *)
let simplify_conjuncts_ simplify is_valid ts =
  let (sub, ts'), ts =
    ts
    |> ExtConjunction.simplify simplify
    |> List.partition_map
      (fun t -> try `L(LinIntRel.of_formula t)
        with Invalid_argument _ -> `R(t))
    |> Pair.map_fst
      (List.partition_map
         (function
           | (Const.Eq(ty), ([1, x], n)) when Type.is_int ty ->
             `L(x, IntTerm.make (-n))
           | la -> `R(LinIntRel.formula_of la)))
  in
  List.map
    (fun (x, t) -> Atom.eq Type.mk_int (Term.mk_var x) t |> Formula.of_atom)
    sub
  @ List.filter (Formula.subst sub >> is_valid >> not) (ts' @ ts)

(* lift [f] that takes a formula on integers to unit and booleans *)
let lift_int simplify f =
  Formula.map_atom (CunAtom.elim_beq_bneq ~no_iff:false)
  >> elim_unit
  >> simplify
  (* @todo elim boolean variables *)
  >> f

(* val is_linear : Formula.t -> bool *)
let is_linear = Formula.fold_band CunAtom.is_linear

let simplify =
  Formula.map_atom (CunAtom.simplify_ub >> CunAtom.elim_beq_bneq)
  >> Formula.map_atom (CunAtom.simplify >> Formula.of_atom)

(*val subst_pvars : t -> Formula.t -> Formula.t*)
let subst_pvars psub = Formula.map_atom (CunAtom.subst_pvars psub)
let subst_pvars psub = subst_pvars psub >> Formula.remove_annot

let rec ufuns_of phi =
  Formula.fold
    (object
      method fatom = CunAtom.ufuns_of ufuns_of
      method ftrue () = []
      method ffalse () = []
      method fnot r1 = r1
      method fand r1 r2 = r1 @ r2
      method for_ r1 r2 = r1 @ r2
      method fimply r1 r2 = r1 @ r2
      method fiff r1 r2 = r1 @ r2
      method fforall (x, _) r1 = Set_.diff r1 [x]
      method fexists (x, _) r1 = Set_.diff r1 [x]
    end)
    phi
