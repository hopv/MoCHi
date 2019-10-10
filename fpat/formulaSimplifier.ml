open Util
open Combinator
open Term
open Formula

(** Formula simplifier *)

let rec simplify phi =
  lazy_para
    (object
      method fatom = CunAtom.simplify >> Formula.of_atom
      method ftrue () = mk_true
      method ffalse () = mk_false
      method fnot phi _ = bnot phi
      method fand phi1 _ phi2 _ =
        Formula.band [phi1; phi2]
        |> Formula.conjuncts_of
        |> List.map simplify
        |> ExtConjunction.simplify simplify
        |> band
      method for_ phi1 _ phi2 _ =
        Formula.bor [phi1; phi2]
        |> Formula.disjuncts_of
        |> List.map simplify
        |> ExtDisjunction.simplify simplify
        |> bor
      method fimply _ phi1 _ phi2 = imply (Lazy.force phi1) (Lazy.force phi2)
      method fiff _ phi1 _ phi2 = mk_iff (Lazy.force phi1) (Lazy.force phi2)
      method fforall xty _ phi1 = forall [xty] (Lazy.force phi1)
      method fexists xty _ phi1 = exists [xty] (Lazy.force phi1)
    end)
    phi
let simplify =
  NNF.of_formula
  >> NNF.map_literal CunLiteral.simplify
  >> NNF.formula_of
  >> simplify
let simplify =
  Logger.log_block1 "FormulaSimplifier.simplify"
    ~before:(Logger.printf "input: %a@," pr)
    ~after:(Logger.printf "output: %a" pr)
    simplify

let rec fix f x = let x' = f x in if x = x' then x else fix f x'

(** @assume phi has already simplified by
    Qelim.simplify_eqint_ps_quick2 or something *)
(* transform
   ((var1 = (l1, l2)) &&
    (... && ((var2 = (l1, l2)) && var3 = (proj(0) var2))))
   into ((var1 = (l1, l2)) && var3 = (proj(0) var1)) *)
let reduce_same_decl phi =
  let rec mk_subst subst form t =
    match Term.fun_args t with
    | Term.Const(Const.And), [t1; t2] ->
      begin
        match Term.fun_args t1 with
        | Term.Const(Const.Eq(ty)), [t1'; t2'] when Term.is_var t1' ->
          if List.mem_assoc t2' form then
            let subst = (Term.var_of t1', List.assoc t2' form) :: subst in
            mk_subst subst form t2
          else
            let (subst, t2) = mk_subst subst ((t2', t1') :: form) t2 in
            let t1 = Formula.eq ty t1' t2' in
            (subst, Formula.mk_and t1 t2)
        | _ ->
          let (subst1, t1') = mk_subst subst form t1 in
          let (subst2, t2') = mk_subst subst form t2 in
          (subst1 @ subst2, Formula.mk_and t1' t2')
      end
    | t, ts -> subst, Term.mk_app t ts |> Formula.of_term
  in
  phi
  |> Formula.term_of
  |> mk_subst [] []
  |> uncurry2 Formula.subst
let reduce_same_decl phi = fix reduce_same_decl phi
let reduce_same_decl =
  Logger.log_block1 "FormulaSimplifier.reduce_same_decl"
    ~before:(Logger.printf "input: %a@," Formula.pr)
    ~after:(Logger.printf "output: %a" Formula.pr)

let minimize_disjuncts phi = function
  | [phi] -> [phi]
  | phis ->
    Set_.minimal
      (fun phis -> SMTProver.implies_dyn [phi] [Formula.bor phis])
      phis
let minimize_disjuncts =
  Logger.log_block2 "minimizing # of disjunctions"
    ~before:(fun _ -> Formula.bor >> Logger.printf "input: %a@," Formula.pr)
    ~after:(Formula.bor >> Logger.printf "output: %a" Formula.pr)
    minimize_disjuncts

let minimize_conjuncts phi = function
  | [phi] -> [phi]
  | phis -> Set_.minimal (fun phis -> SMTProver.implies_dyn phis [phi]) phis
let minimize_conjuncts =
  Logger.log_block2 "minimizing # of conjunctions"
    ~before:(fun _ -> Formula.band >> Logger.printf "input: %a@," Formula.pr)
    ~after:(Formula.band >> Logger.printf "output: %a" Formula.pr)
    minimize_conjuncts

let simplify_dnf_interp phi1 phi2 =
  Formula.disjuncts_of
  >> minimize_disjuncts phi1
  >> List.map (Formula.conjuncts_of
               >> minimize_conjuncts (Formula.bnot phi2)
               >> Formula.band)
  >> Formula.bor

let rec minimize tenv phis1 phis2 =
  match phis1 with
  | [] -> Formula.band phis2
  | phi :: phis' ->
    if SMTProver.implies_dyn ~tenv (phis' @ phis2) [phi]
    then minimize tenv phis' phis2
    else minimize tenv phis' (phi :: phis2)
let minimize tenv phis = minimize tenv phis []

(*
let rec loop_conj phis1 phis2 phis3 =
  match phis1 with
  | [] -> phis2 @ phis3
  | phi::phis1' ->
    begin
      try
        if implies (Fol.list_conj (phis1' @ phis2)) phi
        then loop_conj phis1' phis2 phis3
        else loop_conj phis1' (phi::phis2) phis3
      with Common.Nonlinear -> loop_conj phis1' phis2 (phi::phis3)
    end

let rec loop_disj phis1 phis2 phis3 =
  match phis1 with
  | [] -> phis2 @ phis3
  | phi::phis1' ->
    begin
      try
        if implies phi (Fol.list_disj (phis1' @ phis2))
        then loop_disj phis1' phis2 phis3
        else loop_disj phis1' (phi::phis2) phis3
      with Common.Nonlinear -> loop_disj phis1' phis2 (phi::phis3)
    end

let rec minimize phi =
  match phi with
  | Fol.And(_, _) ->
      Fol.list_conj (Fol.simplify_conj_list (loop_conj (List.map minimize (Fol.conjs_of phi)) [] []))
  | Fol.Or(_, _) ->
      Fol.list_disj (Fol.simplify_disj_list (loop_disj (List.map minimize (Fol.disjs_of phi)) [] []))
  | _ -> phi
*)
