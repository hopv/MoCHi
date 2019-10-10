open Combinator
open Util

(** {6 Constructors} *)

(* exists tenv. pv /\ phi *)
type head = {
  tenv: TypEnv.t;
  pv: PredVar.t option; (* PredVar.t *)
  phi: Formula.t
}
(* pvas /\ phi *)
type body = {
  pvas: Pva.t list;
  phi: Formula.t
}
type t = {
  head: head;
  body: body
}

(* disabling this may cause the same ray counterexamples to be sampled
   repeatedly? *)
let disable_conj = ref false

(** {6 Printers} *)

let pr_head ppf h =
  if h.tenv = [] then
    if Formula.is_true h.phi then
      Format.fprintf ppf "@[<v>%a@]" (Option.pr PredVar.pr "bot") h.pv
    else
      Format.fprintf ppf
        "@[<v>%a /\\ %a@]"
        Formula.pr h.phi
        (Option.pr PredVar.pr "bot") h.pv
  else if Formula.is_true h.phi then
    Format.fprintf ppf
      "@[<v>exists %a. %a@]"
      TypEnv.pr_compact h.tenv
      (Option.pr PredVar.pr "bot") h.pv
  else
    Format.fprintf ppf
      "@[<v>exists %a. %a /\\ %a@]"
      TypEnv.pr_compact h.tenv
      Formula.pr h.phi
      (Option.pr PredVar.pr "bot") h.pv

let pr_head_tex ppf h =
  if h.tenv = [] then
    if Formula.is_true h.phi then
      Format.fprintf ppf "@[<v>%a@]" (Option.pr PredVar.pr_tex "bot") h.pv
    else
      Format.fprintf ppf
        "@[<v>%a \\land %a@]"
        Formula.pr_tex h.phi
        (Option.pr PredVar.pr_tex "bot") h.pv
  else if Formula.is_true h.phi then
    Format.fprintf ppf
      "@[<v>\\exists %a. %a@]"
      TypEnv.pr_compact_tex h.tenv
      (Option.pr PredVar.pr_tex "bot") h.pv
  else
    Format.fprintf ppf
      "@[<v>\\exists %a. %a \\land %a@]"
      TypEnv.pr_compact_tex h.tenv
      Formula.pr_tex h.phi
      (Option.pr PredVar.pr_tex "bot") h.pv

let pr_body ppf b =
  Format.fprintf ppf "@[<hov>";
  List.pr Pva.pr ",@ " ppf b.pvas;
  if not (Formula.is_true b.phi) then
    begin
      if b.pvas <> [] then Format.fprintf ppf ",@ ";
      Formula.pr ppf b.phi
    end;
  Format.fprintf ppf "@]"

let pr_body_tex ppf b =
  Format.fprintf ppf "@[<hov>";
  List.pr Pva.pr_tex ",@ " ppf b.pvas;
  if not (Formula.is_true b.phi) then
    begin
      if b.pvas <> [] then Format.fprintf ppf ",@ ";
      Formula.pr_tex ppf b.phi
    end;
  Format.fprintf ppf "@]"

let pr ppf hc =
  match hc.head.pv with
  | None -> Format.fprintf ppf "@[<hov2>?-@ %a.@]" pr_body hc.body
  | Some(pv) ->
    Format.fprintf ppf "@[<hov2>%a :-@ %a.@]" pr_head hc.head pr_body hc.body

let pr_tex ppf hc =
  match hc.head.pv with
  | None -> Format.fprintf ppf "@[<hov2>?-\\\\@ %a.\\\\@]" pr_body_tex hc.body
  | Some(pv) ->
     Format.fprintf ppf "@[<hov2>%a \\models\\\\@ %a.\\\\@]"
                    pr_head_tex hc.head pr_body_tex hc.body

(** {6 Auxiliary constructors} *)

let mk_head ?(tenv = []) ?(phi = Formula.mk_true) pvopt =
  { tenv = tenv; pv = pvopt; phi = phi }
let mk_body pvas phi = { pvas = pvas; phi = phi }
let make h b = { head = h; body = b }

let mk_def ?(tenv = []) ?(hphi = Formula.mk_true) hpv bpvas bphi =
  make (mk_head ~tenv ~phi:hphi (Some hpv)) (mk_body bpvas bphi)
let mk_def_pva ?(tenv = []) ?(hphi = Formula.mk_true) hpva bpvas bphi =
  let hpv, phi = Pva.pvar_of hpva in
  mk_def ~tenv ~hphi:hphi hpv bpvas (Formula.band [phi; bphi])
let mk_goal bpvas bphi = make (mk_head None) (mk_body bpvas bphi)

let body_of_formulas =
  List.partition_map
    (fun phi -> try `L(Pva.of_formula phi) with Global.NoMatch _ -> `R(phi))
  >> Pair.map_snd Formula.band
  >> uncurry2 mk_body

let of_formulas pvs phi phis =
  let body = body_of_formulas phis in
  try
    Formula.let_pva phi
      (fun pva tts -> mk_def_pva (Pva.make pva tts) body.pvas body.phi)
  with
  | Global.NoMatch _ ->
    try
      Formula.let_exists phi
        (fun x ty phi ->
           try
             let phis1, phi0, phis2 =
               List.pick (Formula.is_pva pvs) (Formula.conjuncts_of phi)
             in
             (* pvs(phis1, phis2) = [] *)
             Formula.let_pva phi0
               (fun pva tts ->
                  mk_def_pva ~tenv:[x,ty] (Pva.make pva tts) body.pvas body.phi)
           with Not_found -> raise (Global.NoMatch "no pva in phi"))
    with Global.NoMatch _ ->
      phi
      |> Formula.bnot
      |> List.return
      |> (@) [body.phi]
      |> Formula.band
      |> mk_goal body.pvas

let of_clause pvs lits =
  let lits1, lits2 =
    lits |> List.partition (Literal.formula_of >> Formula.is_exists)
  in
  let (phis11, phis12), phis2 =
    lits2
    |> List.partition (Literal.is_pva pvs)
    |> Pair.map
      (List.partition Literal.is_pos
       >> Pair.map
         (List.map (CunLiteral.simplify >> Literal.formula_of))
         (List.map (CunLiteral.negate >> Literal.formula_of)))
      (List.map (CunLiteral.negate >> Literal.formula_of))
  in
  match phis11, lits1 with
  | [], [] -> of_formulas pvs Formula.mk_false (phis12 @ phis2)
  | [], [l] -> of_formulas pvs (Literal.formula_of l) (phis12 @ phis2)
  | [phi], [] -> of_formulas pvs phi (phis12 @ phis2)
  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () ->
          Format.printf "@,not a Horn clause:@, @[%a@]@," Clause.pr lits)
      ()
let of_clause =
  Logger.log_block2 "HornClause.of_clause"
    ~before:(fun _ -> Logger.printf "input: %a@," Clause.pr)
    ~after:(Logger.printf "output: %a" pr)
    of_clause

(** {6 Morphisms} *)

let head_map ftenv fpv fphi h =
  { pv = fpv h.pv; tenv = ftenv h.tenv; phi = fphi h.phi }
let body_map fpvas fphi b =
  { pvas = fpvas b.pvas; phi = fphi b.phi }

let ae_fold f hc =
  f hc.head.tenv hc.head.pv hc.head.phi
    hc.body.pvas hc.body.phi
let fold fnone fsome hc =
  match hc.head.pv with
  | None -> fnone hc.body.pvas hc.body.phi
  | Some(pv) -> fsome pv hc.body.pvas hc.body.phi

let map fhead fbody hc = make (fhead hc.head) (fbody hc.body)
let map_head f = map f id
let map_body f = map id f
let map_bpvas f = map id (body_map f id)
let map_phi f = map (head_map id id f) (body_map id f)

(** {6 Inspectors} *)

let head_fvs head =
  head.pv
  |> Option.fold [] PredVar.fvs
  |> (@) (Formula.fvs head.phi)
  |> List.unique
  |> List.filter (flip List.mem_assoc head.tenv >> not)
let head_fvs_bool head =
  head.pv
  |> Option.fold [] PredVar.fvs_bool
  |> (@) (Formula.fvs_bool head.phi)
  |> List.unique
  |> List.filter (flip List.mem_assoc head.tenv >> not)
let head_fvs_ty head =
  head.pv
  |> Option.fold [] PredVar.fvs_ty
  |> (@) (Formula.fvs_ty head.phi)
  |> TypEnv.merge
  |> List.filter (fst >> flip List.mem_assoc head.tenv >> not)
let body_fvs body =
  body.pvas
  |> List.concat_map Pva.fvs
  |> (@) (Formula.fvs body.phi)
  |> List.unique
let body_fvs_bool body =
  body.pvas
  |> List.concat_map Pva.fvs_bool
  |> (@) (Formula.fvs_bool body.phi)
  |> List.unique
let body_fvs_ty body =
  body.pvas
  |> List.concat_map Pva.fvs_ty
  |> (@) (Formula.fvs_ty body.phi)
  |> TypEnv.merge

let pat_match_head h1 h2 =
  match h1, h2 with
  | None, None -> []
  | Some(p1), Some(p2) -> PredVar.pat_match p1 p2
  | _, _ -> assert false

let tenv_of_head head = head.tenv
let pv_of_head head = head.pv
let phi_of_head (head : head) = head.phi
let pvas_of_body body = body.pvas
let phi_of_body body = body.phi

let head_of hc = hc.head
let body_of hc = hc.body

let htenv_of hc = hc.head.tenv
let hpv_of hc = hc.head.pv
let hphi_of hc = hc.head.phi
let bpvas_of hc = hc.body.pvas
let bphi_of hc = hc.body.phi

let nodesB hc = List.map (Pva.idnt_of >> Option.return) hc.body.pvas
let nodeH hc =
  match hc.head.pv with
  | None -> None
  | Some(pv) -> Some(PredVar.idnt_of pv)
let nodes hc = nodeH hc :: nodesB hc

let eq_shapeB hc1 hc2 =
  Bag.equiv
    (List.map Pva.idnt_of hc1.body.pvas)
    (List.map Pva.idnt_of hc2.body.pvas)
(* only for non-existentially quantified HCCSs *)
let eq_shapeH hc1 hc2 = nodeH hc1 = nodeH hc2
let eq_shape hc1 hc2 = eq_shapeH hc1 hc2 && eq_shapeB hc1 hc2

let eq_body_loose body1 body2 =
  body1.pvas = body2.pvas
  && Set_.equiv
    (Formula.conjuncts_of body1.phi)
    (Formula.conjuncts_of body2.phi)
let eq_loose hc1 hc2 = hc1.head = hc2.head && eq_body_loose hc1.body hc2.body

let cong hc1 hc2 =
  match hc1.head.pv, hc2.head.pv with
  | None, None -> true
  | Some(pv1), Some(pv2) -> PredVar.cong pv1 pv2
  | _, _ -> false

let pvsB hc = List.map Pva.idnt_of hc.body.pvas
let pvsH hc =
  match hc.head.pv with
  | None -> []
  | Some pv -> [PredVar.idnt_of pv]
let pvs hc = pvsB hc @ pvsH hc

let is_goal hc = hc.head.pv = None
let is_root = is_goal
let is_coeff hc =
  match hc.head.pv with
  | None -> false
  | Some(pv) -> Idnt.is_coeff (PredVar.idnt_of pv)

let is_cyclic hc = Set_.subset (pvsH hc) (pvsB hc)
let is_trivial hc =
  match hpv_of hc with
  | None -> false
  | Some pv -> List.mem (Pva.of_pvar pv) (bpvas_of hc)

let use hc =
  let pvs = pvsB hc in
  fun pv -> List.mem pv pvs

let def hc =
  let pvs = pvsH hc in
  fun pv -> List.mem pv pvs

let fvsH hc = hc.head |> head_fvs
let fvsH_bool hc = hc.head |> head_fvs_bool
let fvsH_ty hc = hc.head |> head_fvs_ty
let fvsB hc = hc.body |> body_fvs
let fvsB_bool hc = hc.body |> body_fvs_bool
let fvsB_ty hc = hc.body |> body_fvs_ty
let fvs_wo_head hc = Set_.diff (fvsB hc) (fvsH hc)
let fvs hc = (fvsH hc @ fvsB hc) |> List.unique
let fvs_ty hc = (fvsH_ty hc @ fvsB_ty hc) |> TypEnv.merge

let coeffsB hc =
  hc.body.pvas
  |> List.concat_map Pva.coeffs
  |> (@) (Formula.coeffs hc.body.phi)
  |> List.unique
let coeffsH hc = hc.head.pv |> Option.fold [] (Pva.of_pvar >> Pva.coeffs)
let coeffs hc = coeffsB hc @ coeffsH hc |> List.unique

let ufunsB hc =
  hc.body.pvas
  |> List.concat_map (Pva.ufuns_of CunFormula.ufuns_of)
  |> (@) (CunFormula.ufuns_of hc.body.phi)
  |> List.unique
let ufunsH hc =
  hc.head.pv
  |> Option.fold [] (Pva.of_pvar >> Pva.ufuns_of CunFormula.ufuns_of)
let ufuns hc = ufunsB hc @ ufunsH hc |> List.unique

let tenvB hc = hc.body.pvas |> List.concat_map Pva.tenv_of |> List.unique
let tenvH hc = hc.head.pv |> Option.fold [] (Pva.of_pvar >> Pva.tenv_of)
let tenv hc = tenvB hc @ tenvH hc |> List.unique

(** {6 Operators} *)

let subst_varsB sub =
  (* @todo no need to mask sub with h?
     or substitute vars in h!? *)
  map_body (body_map (List.map (Pva.subst sub)) (Formula.subst sub))

let subst_tvars tsub =
  map
    (head_map
       (TypEnv.subst tsub)
       (Option.map (PredVar.subst_tvars tsub))
       (Formula.subst_tvars tsub))
    (body_map
       (List.map (Pva.subst_tvars tsub))
       (Formula.subst_tvars tsub))

let substB fresh simplify psub hc =
  let lookup =
    if fresh then PredSubst.lookup_fresh else PredSubst.lookup
  in
  let pvas', phis =
    hc.body.pvas
    |> List.partition_map
      (fun pva ->
         try
           `R(lookup psub pva)
         with Not_found ->
           `L(pva))
  in
  if phis = [] then
    hc
  else
    make hc.head (mk_body pvas' (Formula.band (hc.body.phi :: phis)))
    |> simplify
let substB ?(fresh = true) ?(simplify = id) =
  Logger.log_block2
    "HornClause.substB"
    ~before:(fun _ -> Logger.printf "input: %a@," pr)
    ~after:(Logger.printf "output: %a" pr)
    (substB fresh simplify)

let substH fresh simplify psub hc =
  let lookup = if fresh then PredSubst.lookup_fresh else PredSubst.lookup in
  match hc.head.pv with
  | None -> hc
  | Some(pv) ->
    try
      pv
      |> Pva.of_pvar
      |> lookup psub
      |> Formula.mk_and hc.head.phi
      |> Formula.exists hc.head.tenv
      |> Formula.bnot
      |> List.return
      |> List.cons hc.body.phi
      |> Formula.band
      |> mk_goal hc.body.pvas
      |> simplify
    with Not_found -> hc
let substH ?(fresh = true) ?(simplify = id) =
  Logger.log_block2 "HornClause.substH"
    ~before:(fun _ -> Logger.printf "input: %a@," pr)
    ~after:(Logger.printf "output: %a" pr)
    (substH fresh simplify)

let subst fresh simplify psub =
  substB ~fresh ~simplify psub >> substH ~simplify psub
let subst ?(fresh = true) ?(simplify = id) =
  Logger.log_block2 "HornClause.subst"
    ~before:(fun psub hc ->
        Logger.printf2 "input:@,  psub: %a@,  hc: %a@," PredSubst.pr psub pr hc)
    (subst fresh simplify)

let fresh hc = subst_varsB (hc |> fvs_wo_head |> TermSubst.of_vars) hc

let alpha hc =
  match hc.head.pv with
  | None -> make hc.head hc.body
  | Some(p) ->
    let p', vmap = PredVar.alpha p in
    mk_def p' hc.body.pvas hc.body.phi |> subst_varsB (TermSubst.of_vmap vmap)

let simplify =
  map
    (head_map id id FormulaSimplifier.simplify)
    (body_map (List.map Pva.simplify) FormulaSimplifier.simplify)

let rec fix f x i =
  if i >= 10 then x(*assert false*) (* @todo bug *)
  else let x' = f x in if eq_loose x x' then x else fix f x' (i+1)

let simplify_light vs0 hc =
  (hc.body.pvas, hc.body.phi)
  |> QelimBody.elim_light (vs0 @ fvsH hc)
  |> uncurry2 mk_body
  |> make hc.head
let simplify_light vs0 hc = fix (simplify_light vs0) hc 0
let simplify_light =
  Logger.log_block2 "HornClause.simplify_light"
    ~before:(fun vs0 -> Logger.printf "input: %a@," pr)
    ~after:(Logger.printf "output: %a" pr)
    simplify_light

let simplify_full tenv vs0 hc =
  (* variables that must not be eliminated *)
  let vs = vs0 @ fvsH hc in
  let pvas', phi' =
    (hc.body.pvas, hc.body.phi)
    |> QelimBody.elim_full tenv vs
  in
  let num_eliminated = List.length pvas' - List.length hc.body.pvas in
  if num_eliminated <> 0 then
    Logger.printf
      "# of eliminated pred. var. apps.: %a@,"
      Integer.pr num_eliminated;
  let num_dup = Pva.num_dup pvas' in
  if num_dup <> 0 then
    Logger.printf
      "# of duplicate predicate variables: %a@,"
      Integer.pr num_dup;
  make hc.head (mk_body pvas' phi')
let simplify_full ?(tenv=[]) =
  Logger.log_block2 "HornClause.simplify_full"
    ~before:(fun _ -> Logger.printf "input:@,  %a@," pr)
    ~after:(Logger.printf "output:@,  %a" pr)
    (simplify_full tenv)

let elim_disj hc =
  hc.body.phi
  |> FormulaSimplifier.simplify
  |> DNF.of_formula
  |> DNF.map_literal CunLiteral.simplify
  |> DNF.disjunction_of
  |> List.map (mk_body hc.body.pvas >> make hc.head)

let conj_hcs_of hc =
  hc.body.phi
  |> FormulaSimplifier.simplify
  |> Formula.map_atom CunAtom.elim_beq_bneq
  |> Formula.map_atom CunAtom.elim_eq_neq
  |> DNF.of_formula
  |> DNF.map_literal CunLiteral.simplify
  |> DNF.map_literal
    (Literal.fold (CunAtom.elim_lt_gt >> Literal.of_atom) CunAtom.bnot)
  |> DNF.disjunction_of
  |> List.map (mk_body hc.body.pvas >> make hc.head)

let simplify_ hc =
  let vs = fvsH hc @ List.concat_map Pva.fvs hc.body.pvas in
  hc |> map_phi (FormulaSimplifier.simplify
                 >> QelimBody.elim_int_vars_full vs)

let normalize2 ?(force=true) hc =
  hc.body.pvas
  |> List.map @@ Pva.fold (fun p ->
      List.map (fun tt ->
          if force || not (Term.is_var (TypTerm.term_of tt)) then
            let tt' = TypTerm.fresh tt in
            tt', Formula.eq_tt tt' tt
          else tt, Formula.mk_true)
      >> List.split
      >> (Pair.map
            (Pva.make p
             >> (fun pva ->
                 Logger.debug_assert
                   (fun () -> pva |> Pva.args_of |> Bag.duplicated |> not);
                 pva))
            Formula.band))
  |> List.split
  |> Pair.map_snd
    (List.cons hc.body.phi >> Formula.band >> FormulaSimplifier.simplify)
  |> uncurry2 mk_body
  |> make hc.head
(*|> simplify_*)

let split_bool_non_bool hc =
  hc.body.phi
  |> Cube.of_formula
  |> BoolCube.classify
  |> Pair.lift (List.map Literal.formula_of >> Formula.band)
  |> Pair.lift (mk_body hc.body.pvas >> make hc.head)

let simplified_form_of tenvs hc =
  let h, ttsub =
    match hc.head.pv with
    | None ->
      { pv = None; tenv = hc.head.tenv; phi = hc.head.phi },
      []
    | Some(pv) ->
      tenvs
      |> List.assoc_fail (PredVar.idnt_of pv)
      |> Pair.unfold
        (PredVar.make (PredVar.idnt_of pv)
         >> Option.return
         >> fun pv ->
         { pv = pv; tenv = hc.head.tenv; phi = hc.head.phi })
        (TypTermSubst.pat_match (PredVar.args_of pv))
  in
  hc.body.pvas
  |> List.map
    (fun pva ->
       tenvs
       |> List.assoc_fail (Pva.idnt_of pva)
       |> Pair.unfold
         (Pva.of_tenv (Pva.idnt_of pva))
         (List.map2
            (fun tt (x, ty) ->
               Formula.eq_tt (Term.mk_var x, ty) tt)
            (Pva.args_of pva)))
  |> List.split
  |> Pair.map_snd
    (List.flatten
     >> List.cons hc.body.phi
     >> Formula.band
     >> Formula.subst (TypTermSubst.tsub_of ttsub))
  |> uncurry2 mk_body
  |> make h

let and_body =
  List.map (fun b -> b.pvas, b.phi)
  >> List.unzip
  >> Pair.map List.flatten Formula.band
  >> uncurry2 mk_body

let simplify_bodies =
  List.map (fun b -> b.pvas, b.phi)
  >> List.partition (fst >> (=) [])
  >> Pair.map
    (List.map snd
     >> if_ ((=) [])
       (const [])
       (Formula.bor
        >> Pair.make []
        >> uncurry2 mk_body
        >> List.return))
    (List.map (uncurry2 mk_body))(*@todo*)
  >> uncurry2 (@)

let lookup hc pva =
  let hc' = fresh hc in
  let sub = Pva.pat_match (hc'.head.pv |> Option.elem_of) pva in
  mk_body
    (List.map (Pva.subst sub) hc'.body.pvas)
    (Formula.subst sub hc'.body.phi)

let lookup_eq hc pva =
  let hc' = fresh hc in
  let sub = Pva.pat_match (hc'.head.pv |> Option.elem_of) pva in
  let b =
    mk_body
      (List.map (Pva.subst sub) hc'.body.pvas)
      (Formula.subst sub hc'.body.phi)
  in
  let bvs = Pva.fvs pva in
  b, List.filter (fst >> flip List.mem bvs >> not) (body_fvs_ty b)

(** {6 Inspectors} *)

let is_solution hc sol =
  hc
  |> subst (*~simplify:(simplify [])*) sol
  |> Logger.pprintf "validity checking:@,  %a@," pr
  |> fold
    (fun _ phi ->
       try
         phi
         |> Formula.bnot
         |> SMTProver.is_valid_dyn
         |> Logger.pprintf "%a" Bool.pr_yn
       with
       | SMTProver.Unknown ->
         (* Logger.printf "SMTProver.Unknown returned.@."; *)
         phi
         |> Formula.bnot
         |> Qelim.integer_qelim_dyn
         |> SMTProver.is_valid_dyn
         |> Logger.pprintf "%a" Bool.pr_yn)
    (fun _ _ _ -> assert false)
let is_solution = Logger.log_block2 "HornClause.is_solution" is_solution

let aux ?(real=false) phi m =
  phi
  |> FormulaSimplifier.simplify (* assume NNF and without not *)
  (* @note do not use Formula.map_atom CunAtom.elim_eq_neq here, or
     it results in sampling x = y from
       phi = x <> y
       m = {x |-> -0.666666666667, y |-> 0.333333333333 } *)
  |> Formula.map_atom (CunAtom.elim_lt_gt >> Formula.of_atom)
  |> Formula.atoms
  |> List.map @@ CunAtom.fold_brel_ty
    (object
      method fvar = assert false
      method fubrel = assert false
      method fbbrel = assert false
      method fibrel c t1 t2 =
        match c with
        | Const.Neq ty ->
          if SMTProver.is_valid_dyn
              (Formula.subst m (Formula.mk_brel (Const.Lt ty) t1 t2)
               |> (if real
                   then Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)
                   else id))
          then Formula.mk_brel (Const.Lt ty) t1 t2
               |> Formula.map_atom (CunAtom.elim_lt_gt >> Formula.of_atom)
          else if SMTProver.is_valid_dyn
              (Formula.subst m (Formula.mk_brel (Const.Gt ty) t1 t2)
               |> (if real
                   then Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)
                   else id))
          then Formula.mk_brel (Const.Gt ty) t1 t2
               |> Formula.map_atom (CunAtom.elim_lt_gt >> Formula.of_atom)
          else Formula.mk_brel (Const.Eq ty) t1 t2
        | _ ->
          let a = Formula.mk_brel c t1 t2 in
          if SMTProver.is_valid_dyn
              (Formula.subst m a
               |> (if real
                   then Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)
                   else id))
          then a
          else Formula.mk_brel (Const.not c) t1 t2
      method frbrel c t1 t2 = assert false(*@todo*)
      method fbrel c t1 t2 =
        match c with
        | Const.Neq ty ->
          if SMTProver.is_valid_dyn
              (Formula.subst m (Formula.mk_brel (Const.Lt ty) t1 t2)
               |> (if real
                   then Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)
                   else id))
          then Formula.mk_brel (Const.Lt ty) t1 t2
               |> Formula.map_atom (CunAtom.elim_lt_gt >> Formula.of_atom)
          else if SMTProver.is_valid_dyn
              (Formula.subst m (Formula.mk_brel (Const.Gt ty) t1 t2)
               |> (if real
                   then Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)
                   else id))
          then Formula.mk_brel (Const.Gt ty) t1 t2
               |> Formula.map_atom (CunAtom.elim_lt_gt >> Formula.of_atom)
          else Formula.mk_brel (Const.Eq ty) t1 t2
        | _ ->
          let a = Formula.mk_brel c t1 t2 in
          if SMTProver.is_valid_dyn
              (Formula.subst m a
               |> (if real
                   then Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)
                   else id))
          then a
          else Formula.mk_brel (Const.not c) t1 t2
      method fdivides = assert false
      method frecognizer = assert false
      method fsmem = assert false
      method fssubset = assert false
      method fterm = assert false
    end)
  |> Formula.band
  |> FormulaSimplifier.simplify

let polytope_of ?(real=false) phi = function
  | Polyhedron.Point m ->
    if !Polyhedron.enable_pol
    then Polyhedron.Polytope (aux ~real phi m, m)
    else Polyhedron.Point m
  | Polyhedron.ExPoint(m, dist) ->
    if !Polyhedron.enable_pol
    then Polyhedron.ExPolytope (aux ~real phi m, m)
    else Polyhedron.ExPoint(m, dist)
  | s -> s

let find_point_cex ?(retint=false) ?(extremal=true) ?(refute_all=false) hc sol =
  let phi1 = hc.body.phi in
  let phi2 =
    Option.fold
      Formula.mk_false
      (Pva.of_pvar >> PredSubst.lookup_fresh sol) hc.head.pv
    :: List.map (PredSubst.lookup_fresh sol >> Formula.bnot) hc.body.pvas
    |> Formula.bor
  in
  if SMTProver.implies_dyn [phi1] [phi2] then None
  else
    let cex =
      let old = !SMTProver.var_type in
      SMTProver.var_type := Type.mk_real;
      let phi12_real =
        (if !disable_conj
         then phi1
         else Formula.mk_and phi1 (Formula.bnot phi2))
        |> FormulaSimplifier.simplify
        |> Formula.map_atom CunAtom.elim_eq_neq
        |> Formula.map_atom (CunAtom.elim_lt_gt >> Formula.of_atom)
        |> Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)
      in
      let phi2_real =
        if extremal then
          phi2
          |> FormulaSimplifier.simplify
          |> Formula.map_atom CunAtom.elim_eq_neq
          |> Formula.map_atom (CunAtom.elim_lt_gt >> Formula.of_atom)
          |> Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)
        else Formula.mk_true
      in
      let xs1 = phi1 |> Formula.fvs |> List.unique in
      let model =
        Polyhedron.find_extremal ~retint phi12_real phi2_real
        |> (if refute_all then
              Polyhedron.map_model
                (List.filter_map (fun (x, v) ->
                     if List.mem x xs1 then Some(x, v) else None))
            else id)
      in
      SMTProver.var_type := old;
      model
    in
    Some(polytope_of ~real:(not retint) phi1 cex)

let formula_of_body body =
  (List.map Pva.to_formula body.pvas @ [body.phi]) |> Formula.band

let formula_of =
  ae_fold
    (fun htenv hpv hphi bpvas bphi ->
       let hphi =
         match hpv with
         | None -> Formula.mk_false
         | Some(pv) ->
           [pv |> Pva.of_pvar |> Pva.to_formula; hphi]
           |> Formula.band
           |> Formula.exists htenv
       in
       Formula.imply (formula_of_body { pvas = bpvas; phi = bphi }) hphi)
let formula_of = Logger.log_block1 "HornClause.formula_of" formula_of

let formula_of_forward lbs hc =
  hc
  |> substB ~simplify:(simplify_full []) lbs
  |> fold
    (fun pvas phi ->
       if false && SMTProver.is_sat_dyn phi then
         begin
           Format.printf "%a is satisfiable@," Formula.pr phi;
           assert false
         end;
       (* pvas may be not [] *)
       (* @todo pvas are bot? *)
       if pvas = [] then phi else Formula.mk_false)
    (fun _ _ _ -> Format.printf "%a@," pr hc; assert false)

let rename pvmap =
  map
    (head_map id (Option.map (PredVar.rename pvmap)) id)
    (body_map (List.map (Pva.rename pvmap)) id)

let normalize hc =
  let vmap =
    List.mapi
      (fun i (x, _) -> x, Idnt.make ("x" ^ string_of_int i))
      hc.head.tenv
  in
  let hc' =
    map_head
      (head_map
         (List.map (Pair.map_fst (fun x -> List.assocF x vmap)))
         (Option.map (PredVar.rename_vars vmap))
         (Formula.rename vmap))
      hc
  in
  let vmap =
    hc' |> fvs |> List.mapi
      (fun i x -> x, Idnt.make ("x" ^ string_of_int (i + List.length vmap)))
  in
  map
    (head_map id (Option.map (PredVar.rename_vars vmap)) (Formula.rename vmap))
    (body_map (List.map (Pva.rename_vars vmap)) (Formula.rename vmap))
    hc'

let int_to_real =
  map
    (head_map
       TypEnv.int_to_real
       (Option.map PredVar.int_to_real)
       (Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)))
    (body_map
       (List.map Pva.int_to_real)
       (Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)))

(* @todo Issue #156 *)
let elim_ufuns =
  map id
    (body_map id (Formula.map_atom (CunAtom.elim_ufuns >> Formula.of_atom)))

let defmatch defs (pva, m) =
  let hres_P =
    List.filter (nodeH >> (=) (Some (Pva.idnt_of pva))) defs
  in
  List.map
    (fun dc ->
       match hpv_of dc with
       | None -> failwith "defmatch"
       | Some pv ->
         let exists_vars =
           Set_.diff (fvs_ty dc) (fvsH_ty dc)
         in
         let exists = List.map fst exists_vars in
         let sub' = List.map (fun i -> Pair.make i (Term.new_var ())) exists in
         let matchsub = Pva.pat_match pv pva |> (@) sub' in
         (* Logger.printf "matchsub:%a@." TermSubst.pr matchsub; *)
         (*
         let matchphi =
           Pva.pat_match pv pva
           |> formula_of_tsub
         in
         *)
         (* atms_i * phi_i *)
         bpvas_of dc
         |> List.map (Pva.subst matchsub)
         |> List.map (flip Pair.make m),
         bphi_of dc
         |> Formula.subst matchsub)
    (* Formula.mk_and (bphi_of dc) matchphi *)
    hres_P
