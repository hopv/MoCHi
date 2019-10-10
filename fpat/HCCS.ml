open Combinator
open Util

let resolve_inc = ref false

type t = HornClause.t list
(* type 'a t = HornClause.t list * 'a list *)
(*
  `Goal of HornClause.body
  `Formula of Formula.t
  `WF of PredVar.t
  `DWF of PredVar.t
*)
type node = Idnt.t option

(** {6 Printers} *)

let pr ppf = Format.fprintf ppf "@[<v>%a@]" (List.pr HornClause.pr "@,@,")
let pr_tex ppf =
  Format.fprintf ppf "@[<v>%a@]" (List.pr HornClause.pr_tex "@,@,")


(** {6 Auxiliary constructors} *)

let of_psub =
  List.map
    (fun (p, (tenv, phi)) -> HornClause.mk_def (PredVar.make p tenv) [] phi)

let of_formula0 pvs =
  CNF.of_formula_loose >> CNF.to_clauses >> List.map (HornClause.of_clause pvs)
let of_formula0 =
  Logger.log_block2
    "HCCS.of_formula0"
    ~before:(fun _ -> Logger.printf "input: %a@," Formula.pr)
    ~after:(Logger.printf "output: %a" pr)
    of_formula0

let rec of_formula env phi =
  match phi |> Formula.term_of |> Term.fun_args with
  | Term.Const(Const.And), [phi1; phi2] ->
    (phi1, phi2)
    |> Pair.lift (Formula.of_term >> of_formula env)
    |> uncurry2 (@)
  | Term.Const(Const.Imply), [phi1; phi2] ->
    (phi1, phi2)
    |> (Pair.map
          (Formula.of_term >> Formula.conjuncts_of >> (@) env)
          Formula.of_term)
    |> uncurry2 of_formula
  | _ -> [HornClause.of_formulas (List.concat_map Formula.fvs (phi :: env)) phi env]

let rec of_smtlib1 = function
  | [] -> []
  | Sexp.S("benchmark") :: Sexp.S(name) :: es -> of_smtlib1 es
  | Sexp.S(":status") :: Sexp.S(status) :: es -> of_smtlib1 es
  | Sexp.S(":logic") :: Sexp.S(logic) :: es -> of_smtlib1 es
  | Sexp.S(":extrafuns")
    :: Sexp.L([Sexp.L([Sexp.S(var); Sexp.S(typ)])])
    :: es -> of_smtlib1 es
  | Sexp.S(":extrapreds")
    :: Sexp.L([Sexp.L((Sexp.S(pvar)) :: args)])
    :: es -> of_smtlib1 es
  | Sexp.S(":formula") :: e :: es ->
    e
    |> CunFormula.of_sexp
    |> (fun phi -> of_formula0 (Formula.fvs phi) phi)
    |> (@) (of_smtlib1 es)
  | es ->
    Format.printf "sexp: %a@," Sexp.pr (Sexp.L(es));
    assert false
let of_smtlib1 (Sexp.L(es)) = of_smtlib1 es

(** only for sv-benchmarks/clauses benchmarks (with (set-logic HORN)) *)
let rec of_smtlib2 is_real pvars =
  function
  | [] -> []
  | Sexp.L(Sexp.S("set-info") :: _) :: es
  | Sexp.L([Sexp.S("set-logic"); Sexp.S("HORN")]) :: es ->
    of_smtlib2 is_real pvars es
  | Sexp.L(Sexp.S("set-option") :: _) :: es ->
    of_smtlib2 is_real pvars es
  | (Sexp.L([Sexp.S("declare-fun"); Sexp.S(id); args_ty; ret_ty]) as e) :: es ->
    let is_real =
      match args_ty, ret_ty with
      | Sexp.L(tys), Sexp.S("Bool") ->
        begin
          match List.unique tys with
          | [] -> is_real
          | [Sexp.S("Real")] -> true
          | [_] -> false
          | _ ->
            Format.printf
              "mix use of Real and Int is not supported: %a@."
              Sexp.pr e;
            assert false
        end
      | _ ->
        Format.printf "not pvar: %a@," Sexp.pr e;
        assert false
    in
    of_smtlib2 is_real (id::pvars) es
  | Sexp.L([Sexp.S("declare-const"); Sexp.S(id); ty]) :: es ->
    of_smtlib2 is_real pvars es
  | Sexp.L([Sexp.S("check-sat")]) :: es
  | Sexp.L([Sexp.S("get-model")]) :: es ->
    of_smtlib2 is_real pvars es
  | Sexp.L([Sexp.S("assert"); e]) :: es ->
    e
    |> CunFormula.of_sexp ~is_real ~pvars
    |> (fun phi -> of_formula0 (Formula.fvs phi) phi)
    |> (@) (of_smtlib2 is_real pvars es)
  | es ->
    Format.printf "sexp: %a@," Sexp.pr (Sexp.L(es));
    assert false
let of_smtlib2 = of_smtlib2 false [] >> List.rev

(** {6 Morphisms} *)

let map_phi f = List.map (HornClause.map_phi f)
let map_pred f = List.classify HornClause.eq_shapeH >> List.map f

(** {6 Inspectors} *)

let fvs = List.concat_map HornClause.fvs >> List.unique
let coeffs = List.concat_map HornClause.coeffs >> List.unique
let ufuns = List.concat_map HornClause.ufuns >> List.unique

let pvsB = List.concat_map HornClause.pvsB
let pvsH = List.concat_map HornClause.pvsH
let pvs hcs = pvsH hcs @ pvsB hcs (*List.concat_map HornClause.pvs*)
let used_pvs = pvsB
let defined_pvs = pvsH
let undefined_pvs hcs = Set_.diff (pvsB hcs) (pvsH hcs)
let unused_pvs hcs = Set_.diff (pvsH hcs) (pvsB hcs)
let mpvs = pvsB (* returns a bag *) >> Bag.get_dup_elems >> List.unique
let bpvs = pvsH (* returns a bag *) >> Bag.get_dup_elems >> List.unique
let num_pvs = pvs >> List.unique >> List.length

let tenvB = List.concat_map HornClause.tenvB >> List.unique
let tenvH = List.concat_map HornClause.tenvH  >> List.unique
let tenv = List.concat_map HornClause.tenv >> List.unique

let defs_of = List.filter (HornClause.is_goal >> not)
let goals_of = List.filter (HornClause.is_goal)

let nodesB = List.concat_map HornClause.nodesB
let nodesH = List.map HornClause.nodeH
let nodes = List.concat_map HornClause.nodes

let nodes_with p =
  List.filter_map
    (HornClause.fold
       (fun pvas phi -> if p None pvas phi then Some(None) else None)
       (fun pv pvas phi ->
          let nd = Some(PredVar.idnt_of pv) in
          if p nd pvas phi then Some(nd) else None))

let find nd = List.find (HornClause.nodeH >> (=) nd)
let find_all nd = List.find_all (HornClause.nodeH >> (=) nd)

let preds_of nd = find_all nd >> pvsB >> List.unique >> List.map Option.some

let psub_of =
  List.filter_map
    (HornClause.fold
       (fun _ _ -> None(* @todo *))
       (fun pv pvas phi ->
          if pvas = [] then
            PredVar.fold (fun p tenv -> Some(p, (tenv, phi))) pv
          else
            None(* @todo *)))

let lookup hcs pva =
  hcs
  |> find_all (Some(Pva.idnt_of pva))
  |> (if_ ((=) [])
        (fun _ -> raise Not_found)
        (List.map (flip HornClause.lookup pva)
         >> HornClause.simplify_bodies))

let lookup_eq hcs pva =
  hcs
  |> find_all (Some(Pva.idnt_of pva))
  |> (if_ ((=) [])
        (fun _ -> raise Not_found)
        (List.map (flip HornClause.lookup_eq pva)))

let formula_of_bodies =
  List.map
    (fun b ->
       HornClause.phi_of_body b
       :: (HornClause.pvas_of_body b |> List.map Pva.to_formula)
       |> Formula.band)
  >> Formula.bor

let formula_of_bodies_eq =
  List.map
    (fun (b, tenv) ->
       HornClause.phi_of_body b
       :: (HornClause.pvas_of_body b |> List.map Pva.to_formula)
       |> Formula.band
       |> (fun phi ->
           Formula.to_rename_tsub
             FormulaSimplifier.simplify
             (Set_.diff (Formula.fvs phi) (List.map fst tenv))
             phi
           |> snd)
       |> FormulaSimplifier.simplify
       |> Formula.exists tenv)
  >> Formula.bor
let formula_of_bodies_eq =
  Logger.log_block1 "HCCS.formula_of_bodies_eq" formula_of_bodies_eq

let lookupF hcs pva = try lookup hcs pva with Not_found -> assert false
let lookupD hcs pva =
  try lookup hcs pva
  with Not_found -> [HornClause.mk_body [pva] Formula.mk_true]

let det_lookup hcs =
  Logger.pprintf "looking up %a@," (Printer.coerce Pva.idnt_of Idnt.pr)
  >> lookup hcs
  >> (*List.elem_of_singleton*)(function
      | [x] -> x
      | _ -> assert false)

let det_lookupF hcs pva = try det_lookup hcs pva with Not_found -> assert false
let det_lookupD hcs pva =
  try det_lookup hcs pva
  with Not_found -> HornClause.mk_body [pva] Formula.mk_true

let forward_data_flow_analysis init step eq hcs =
  hcs
  |> pvs
  |> List.unique
  |> List.map Option.some
  |> (fun nds -> None :: nds)
  |> List.map (Pair.unfold id init)
  |> fix (fun ds ->
      List.map (fun (nd, _) ->
          preds_of nd hcs
          |> List.map (Pair.unfold id (flip List.assoc ds))
          |> step nd
          |> Pair.make nd)
        ds)
    (List.for_all2 (comp2 eq snd snd))

let reachable =
  forward_data_flow_analysis
    (const [])
    (fun nd ->
       List.concat_map snd
       >> (fun nds -> nd :: nds)
       >> List.unique)
    Set_.equiv
let reachable = Logger.log_block1 "HCCS.reachable" reachable

(** {5 Predicates} *)

let is_tree = pvsB (* returns a multi-set *) >> Bag.non_duplicated
(*mpvs >> (=) []*)

let is_non_disjunctive =
  nodesH (* returns a multi-set *)(* pvsH cannot be used here *)
  >> Bag.non_duplicated

let is_linear_def hcs =
  let pvsH = pvsH hcs in
  fun p -> Bag.num_occurrences p pvsH = 1

let is_affine_def hcs =
  let pvsH = pvsH hcs in
  fun p -> Bag.num_occurrences p pvsH <= 1

let is_linear_use hcs =
  let pvsB = pvsB hcs in
  fun p -> Bag.num_occurrences p pvsB = 1

let is_affine_use hcs =
  let pvsB = pvsB hcs in
  fun p -> Bag.num_occurrences p pvsB <= 1

let is_well_defined hcs = Set_.subset (pvsB hcs) (pvsH hcs)
let is_non_redundant hcs = Set_.subset (pvsH hcs) (pvsB hcs)

let defined hcs =
  let pvsH = pvsH hcs in
  fun p -> List.mem p pvsH

let not_defined hcs =
  let pvsH = pvsH hcs in
  fun p -> not (List.mem p pvsH)

let used hcs =
  let pvsB = pvsB hcs in
  fun p -> List.mem p pvsB

let not_used hcs =
  let pvsB = pvsB hcs in
  fun p -> not (List.mem p pvsB)

(** {6 Operators} *)

let rename_vars vmap hcs = assert false
let rename pvmap = List.map (HornClause.rename pvmap)

let normalize hcs =
  let pvmap =
    List.mapi
      (fun i (pv, _) -> pv, Idnt.make ("|$P" ^ string_of_int i ^ "|"))
      (tenv hcs)
  in
  hcs |> rename pvmap |> List.map HornClause.normalize

let fresh_pvars hcs =
  let pvmap =
    List.mapi
      (fun i (pv, _) -> pv, Idnt.new_pvar ())
      (tenv hcs)
  in
  hcs |> rename pvmap

let simplify = List.map HornClause.simplify
let simplify_lv1 = List.filter (HornClause.bphi_of >> Formula.is_false >> not)
let simplify_lv2 ?(tenv=[]) =
  simplify
  >> List.filter
    (HornClause.fold
       (fun _ phi -> try SMTProver.is_sat_dyn ~tenv phi with SMTProver.Unknown -> true)
       (fun pv pvas phi ->
          not (List.mem (Pva.of_pvar pv) pvas) &&
          try SMTProver.is_sat_dyn ~tenv phi with SMTProver.Unknown -> true))

let simplify_light vs = List.map (HornClause.simplify_light vs)
let simplify_full ?(tenv=[]) vs =
  List.map (HornClause.simplify_full ~tenv vs) >> List.unique
let simplify_full ?(tenv=[]) =
  Logger.log_block2 "HCCS.simplify_full" (simplify_full ~tenv)


let subst_varsB sub = List.map (HornClause.subst_varsB sub) >> simplify_lv1
let subst_tvars tsub = List.map (HornClause.subst_tvars tsub)

let substB simplify_hc psub =
  List.map (HornClause.substB ~simplify:simplify_hc psub)
  >> simplify_lv1
let substB ?(simplify_hc = id) =
  Logger.log_block2 "HCCS.substB" (substB simplify_hc)

let substH simplify_hc psub =
  List.map (HornClause.substH ~simplify:simplify_hc psub)
  >> simplify_lv1
let substH ?(simplify_hc = id) =
  Logger.log_block2 "HCCS.substH" (substH simplify_hc)

let subst simplify_hc psub =
  List.map (HornClause.subst ~simplify:simplify_hc psub)
  >> simplify_lv1
let subst ?(simplify_hc = id) =
  Logger.log_block2 "HCCS.subst" (subst simplify_hc)

(** remove P(x) :- true. by substituting P(x) = true *)
let simplify_trivial no_inline hccs =
  let aux hccs =
    hccs
    |> Logger.pprintf "check: %a@," pr
    |> List.filter
      (HornClause.fold
         (fun _ _ -> false)
         (fun pv pvas phi ->
            pvas = [] && Formula.is_true phi &&
            pv |> PredVar.idnt_of |> no_inline |> not))
    |> Logger.pprintf "detect: %a@," pr
    |> List.map
      (HornClause.head_of
       >> HornClause.pv_of_head
       >> Option.elem_of
       >> flip PredSubst.elem_of_pvar Formula.mk_true)
    |> flip subst hccs
  in
  let rec loop n  hccs =
    let hccs' = aux hccs in
    if hccs = hccs' then hccs' else loop (n+1) hccs'
  in
  loop 0 hccs
let simplify_trivial ?(no_inline=(fun _ -> false)) =
  Logger.log_block1
    "HCCS.simplify_trivial"
    (simplify_trivial no_inline)

let fresh = List.map HornClause.fresh
let fresh_label = List.map (Pair.map_snd HornClause.fresh)

let alpha = List.map HornClause.alpha

let elim_non_defined ten hcs =
  let not_defined = not_defined hcs in
  hcs
  |> tenv
  |> List.filter_map
    (fun (p, ty) ->
       if not_defined p then
         PredSubst.mk_elem
           p
           (PredVar.args_of (PredVar.of_type p ty))
           Formula.mk_false
         |> Option.some
       else
         None)
  |> flip (substB ~simplify_hc:(HornClause.simplify_full ~tenv:ten [])) hcs
let elim_non_defined ?(tenv=[]) =
  Logger.log_block1
    "HCCS.elim_non_defined"
    ~after:(Logger.printf "output:@,  %a" pr)
    (elim_non_defined tenv)

let complement hcs =
  let not_defined = not_defined hcs in
  hcs
  |> tenvB
  |> List.filter_map
    (fun (p, ty) -> if not_defined p then Some(PredVar.of_type p ty) else None)
  |> List.map (fun pv -> HornClause.mk_def pv [] Formula.mk_false)
  |> (@) hcs

let rec resolve_body_inc
    ?(simplify_body = id)
    hcs body =
  try
    let lpvas, pva, rpvas =
      body
      |> HornClause.pvas_of_body
      |> List.pick (Pva.idnt_of >> defined hcs)
    in
    pva
    |> lookupF hcs
    |> List.map
      (fun b ->
         [b; HornClause.mk_body (lpvas @ rpvas) (HornClause.phi_of_body body)]
         |> HornClause.and_body
         |> simplify_body)
    |> HornClause.simplify_bodies
    |> List.concat_map (resolve_body_inc ~simplify_body:simplify_body hcs)
  with Not_found -> [body]

let resolve_hc_inc tenv hcs hc =
  hc
  |> HornClause.body_of
  |> resolve_body_inc
    ~simplify_body:
      (HornClause.make (HornClause.head_of hc)
       >> HornClause.simplify_full ~tenv []
       >> HornClause.body_of)
    hcs
  |> List.map (HornClause.make (HornClause.head_of hc))

let resolve_hc_sim tenv hcs hc =
  let pvas1, pvas2 =
    let nds = List.map HornClause.nodeH hcs in
    List.partition
      (fun pva -> List.mem (Some(Pva.idnt_of pva)) nds)
      (HornClause.bpvas_of hc)
  in
  if pvas1 = [] then
    [hc]
  else
    pvas1
    |> List.map (lookupD hcs)
    |> List.cons
      (HornClause.mk_body pvas2 (HornClause.bphi_of hc)
       |> List.return)
    |> Vector.product HornClause.and_body
    |> List.map
      (HornClause.make (HornClause.head_of hc)
       >> HornClause.simplify_full ~tenv [])

let resolve_hc tenv hcs hc =
  if !resolve_inc then resolve_hc_inc tenv hcs hc
  else resolve_hc_sim tenv hcs hc
let resolve_hc ?(tenv=[]) =
  Logger.log_block2
    "HCCS.resolve_hc"
    ~before:(fun _ -> Logger.printf "input:@,  %a@," HornClause.pr)
    ~after:(Logger.printf "output:@,  %a" pr)
    (resolve_hc tenv)

let resolve_hc_fixed hcs hc =
  fix
    (List.concat_map (resolve_hc hcs))
    (comp2 Set_.equiv
       (List.concat_map HornClause.bpvas_of)
       (List.concat_map HornClause.bpvas_of))
    [hc]

let resolve tenv hcs1 hcs2 =
  hcs2
  |> List.concat_map (resolve_hc ~tenv hcs1)
  |> simplify_lv1
let resolve ?(tenv=[]) =
  Logger.log_block2
    "HCCS.resolve"
    ~before:(fun hcs1 hcs2 ->
        Logger.printf2 "input:@, hcs1: %a@, hcs2: %a@," pr hcs1 pr hcs2)
    ~after:(Logger.printf "output: %a" pr)
    (resolve tenv)

let resolve_fixed hcs1 hcs2 =
  hcs2
  |> List.concat_map (resolve_hc_fixed hcs1)
  |> simplify_lv1

let rec fixpoint hcs =
  match hcs with
  | [] -> []
  | hc :: hcs' ->
    let hcs'' = resolve_hc_fixed hcs' hc in
    hcs'' @ fixpoint (resolve hcs'' hcs')


let rec depend pvs0 hcs =
  let hcs1, hcs2 =
    List.partition (HornClause.pvs >> Set_.intersects pvs0) hcs
  in
  pvs0
  |> Set_.diff (List.unique (pvs hcs1))
  |> if_ ((=) []) (const hcs1) (flip depend hcs2 >> (@) hcs1)

let rec backward_depend
    ?(mask = [])
    nds hcs =
  let hcs1, hcs2 =
    List.partition (HornClause.nodeH >> flip List.mem nds) hcs
  in
  hcs1
  |> pvsB
  |> List.unique
  |> List.map Option.some
  |> (if_ ((=) [])
        (const hcs1)
        (flip Set_.diff mask
         >> flip (backward_depend ~mask:mask) hcs2
         >> (@) hcs1))

let split_bool_non_bool = List.map HornClause.split_bool_non_bool >> List.unzip

let split_bool_non_bool_label =
  List.map
    (fun (l, hc) ->
       let hc1, hc2 = HornClause.split_bool_non_bool hc in
       (l, hc1), (l, hc2))
  >> List.unzip

let normalize2 ?(force=true)  = List.map (HornClause.normalize2 ~force)

let elim_disj = List.concat_map HornClause.elim_disj

let conj_hccs_of = List.concat_map HornClause.conj_hcs_of

let expand_dag_at p hcs =
  Logger.printf "expanding at %a@," Idnt.pr p;
  let pvs = ref [] in
  let hcs1, hcs2, hcs3 =
    let hcs2 = backward_depend [Some p] hcs in
    let hcs1, hcs3 =
      Set_.diff hcs hcs2
      |> List.partition (fun hc -> HornClause.use hc p)
    in
    hcs1, hcs2, hcs3
    (*hcs |>
      List.partition3_map
        (fun hc ->
         if HornClause.use hc p then
           `L(hc)
         else if HornClause.def hc p then
           `C(hc)
         else
           `R(hc))*)
  in
  let hcs1' =
    hcs1
    |> List.map @@ HornClause.map_bpvas @@ List.map
      (if_
         (Pva.idnt_of >> (=) p)
         (fun pva ->
            let p' = Idnt.new_pvar () in
            pvs := p' :: !pvs;
            Pva.make p' (Pva.args_of pva))
         id)
  in
  let hcs2' =
    let is =
      List.concat_mapi
        (fun i hc -> if HornClause.def hc p then [i] else [])
        hcs2
    in
    List.duplicate hcs2 (List.length !pvs)
    |> List.map fresh_pvars
    |> List.mapi
      (fun k ->
         List.mapi
           (fun j hc ->
              if List.mem j is then
                HornClause.fold
                  (fun _ _ -> assert false)
                  (fun pv pvas phi ->
                     HornClause.mk_def
                       (PredVar.make (List.nth !pvs k) (PredVar.args_of pv))
                       pvas
                       phi)
                  hc
              else
                hc))
    |> List.concat
    (*(HornClause.fold
           (fun _ _ -> assert false)
           (fun pv pvas phi ->
            (* @todo if pvas <> [], this function is not very efficient *)
            List.map
              (fun p ->
               HornClause.make
                 (PredVar.make
                    p
                    (PredVar.args_of pv) |>
                    Option.return)
                 pvas
                 phi)
              !pvs))*)
  in
  !pvs |> List.map (flip Pair.make p),
  hcs1' @ hcs2' @ hcs3

let rec expand_dag hcs =
  let mpvs = mpvs hcs in
  Logger.printf2
    "#mpvs %a@,#hcs %a@,"
    Integer.pr (List.length mpvs)
    Integer.pr (List.length hcs);
  match mpvs with
  | [] -> hcs, []
  | _ :: _ ->
    let p =
      try
        let r = reachable hcs in
        List.find
          (fun p ->
             List.assoc (Some p) r
             |> List.map Option.elem_of
             |> Set_.intersects (Set_.diff mpvs [p])
             |> not)
          mpvs
      with Not_found ->
        assert false
    in
    hcs
    |> expand_dag_at p
    |> Pair.map_snd expand_dag
    |> (fun (inv_map, (hcs', inv_map')) ->
        hcs',
        inv_map'
        |> List.map (fun (p1, p2) -> p1, (List.assoc_default p2 p2 inv_map))
        |> (@) inv_map)
let expand_dag =
  Logger.log_block1
    "HCCS.expand_dag"
    ~before:(Logger.printf "input: %a@," pr)
    ~after:(fun (hcs, inv_map) ->
        Logger.printf2
          "output: %a, [%a]"
          pr hcs
          (List.pr (Pair.pr Idnt.pr Idnt.pr) "; ") inv_map)
    expand_dag

let tree_partition_of hcs =
  let mpvs = mpvs hcs in
  let rec aux seeds hcs =
    match seeds with
    | [] -> []
    | seed :: seeds' ->
      let hcs_dep =
        backward_depend
          ~mask:(List.map Option.return mpvs)
          [seed]
          hcs
      in
      let hcs_rest = Set_.diff hcs hcs_dep in
      Set_.diff
        (Set_.inter (undefined_pvs hcs_dep) mpvs |> List.unique)
        (used_pvs hcs_rest)
      |> List.map Option.some
      |> (@) seeds'
      |> flip aux hcs_rest
      |> List.cons (seed, hcs_dep)
  in
  aux [None] hcs
let tree_partition_of =
  Logger.log_block1
    "HCCS.tree_partition_of"
    ~after:(List.length >> Logger.printf "# of trees: %a" Integer.pr)
    tree_partition_of

let merge hcs =
  hcs
  |> List.classify HornClause.eq_shape
  |> List.map
    (function
      | [] -> assert false
      | hc :: _ as hcs ->
        let pvas =
          hc |> HornClause.bpvas_of |> List.sort compare
          |> List.map Pva.fresh
        in
        HornClause.make
          (HornClause.head_of hc)
          (HornClause.mk_body
             pvas
             (hcs
              |> List.map
                (fun hc' ->
                   List.map2
                     CunFormula.eq_pva
                     (hc' |> HornClause.bpvas_of |> List.sort compare)
                     pvas
                   |> List.cons (HornClause.bphi_of hc')
                   |> Formula.band
                   |> Formula.subst
                     (HornClause.pat_match_head
                        (HornClause.hpv_of hc')
                        (HornClause.hpv_of hc))
                     (* @todo should rename free vars? *))
              |> Formula.bor)))

let reducible is_exc hcs =
  let is_affine_use = is_affine_use hcs in
  let is_linear_def = is_linear_def hcs in
  fun hc ->
    HornClause.fold
      (fun _ _ -> false)
      (fun pv pvas _ ->
         let p = PredVar.idnt_of pv in
         not (is_exc p) &&
         is_linear_def p &&
         not (HornClause.is_cyclic hc) &&
         (List.length pvas <= 1 (*@todo*) || is_affine_use p))
      hc

let rec reduce tenv is_exc hcs =
  hcs
  |> merge
  |> Logger.pprintf "after merge: %a@," pr
  |> elim_disj
  |> simplify_full ~tenv []
  |> Logger.pprintf "after simplify_full: %a@," pr
  |> (try_
        (let_
           (reducible is_exc)
           (fun reducible ->
              List.pick reducible
              >> (fun (hcs1, hc, hcs2) ->
                  let [p] = HornClause.pvsH hc in
                  Logger.printf "%a eliminated@," Idnt.pr p;
                  resolve ~tenv [hc] (hcs1 @ hcs2))))
        (function Not_found -> id | _ -> assert false))
  |> if_ (List.eq_length hcs) (const hcs) (reduce tenv is_exc)
let reduce ?(tenv=[]) =
  Logger.log_block2
    "HCCS.reduce"
    ~before: (fun _ -> Logger.printf "input:@,  %a@," pr)
    ~after: (Logger.printf "output:@,  %a" pr)
    (reduce tenv)

let simplified_form_of hcs =
  let tenvs =
    hcs
    |> tenv
    |> List.map (Pair.map_snd TypEnv.of_type)
  in
  tenvs, List.map (HornClause.simplified_form_of tenvs) hcs

(** {6 Inspectors} *)

let is_solution hcs sol = List.for_all (flip HornClause.is_solution sol) hcs
let is_solution =
  Logger.log_block2
    "HCCS.is_solution"
    ~before:(fun hcs sol ->
         Logger.printf "Horn clauses:@,  %a@," pr hcs;
         Logger.printf "solution:@,  %a@," PredSubst.pr sol)
    is_solution

(** {6 Inspectors} *)

(** {6 Printers} *)

let pr_verbose ppf hcs =
  Format.fprintf
    ppf
    "@[<v># of constrs.: %a@,# of pred. vars.: %a@,@,%a@]"
    Integer.pr (List.length hcs)
    Integer.pr (num_pvs hcs)
    (List.pr HornClause.pr "@,@,") hcs

(** {6 Exporters} *)

let string_of_node = function
  | None -> "bot"
  | Some(p) -> Idnt.string_of p

let save_graphviz filename hcs =
  let not_defined = not_defined hcs in
  let bpvs = bpvs hcs in
  let mpvs = mpvs hcs in
  let ns =
    hcs
    |> nodes
    |> List.unique
    |> List.map
      (function
        | None -> string_of_node None, ""
        | Some(p) ->
          string_of_node (Some(p)),
          "["
          ^ (if not_defined p then
               "style = \"filled,dashed\""
             else
               "style = \"filled,solid\"")
          ^ (if List.mem p bpvs then
               ", shape=diamond"
             else
               "")
          ^ (if List.mem p mpvs then
               ", fillcolor=red"
             else
               ", fillcolor=white")
          ^ "]")
  in
  let es =
    hcs
    |> List.concat_mapi
      (fun i hc ->
         List.map
           (fun nd -> HornClause.nodeH hc, nd, i)
           (HornClause.nodesB hc))
    |> List.map
      (fun (nd1, nd2, i) ->
         string_of_node nd1,
         string_of_node nd2,
         "[label = " ^ string_of_int i ^ "]")
  in
  Graph_.save_graphviz filename ns es
let save_graphviz = Logger.log_block2 "HCCS.save_graphviz" save_graphviz

let save_smtlib filename hcs =
  let hcs = normalize hcs in
  let oc = open_out filename in
  let ocf = Format.formatter_of_out_channel oc in
  let tenv = hcs |> tenv in
  let vs = hcs |> fvs |> List.map Idnt.string_of in
  Format.fprintf ocf "@[<v>";
  Format.fprintf ocf "(benchmark %a@," String.pr filename;
  Format.fprintf ocf ":status unknown@,";
  Format.fprintf ocf ":logic QF_UFLRA@,";
  List.iter (Format.fprintf ocf ":extrafuns ((%a Real))@," String.pr) vs;
  List.iter
    (fun (p, ty) ->
       let args =
         PredVar.of_type p ty
         |> PredVar.normalize_args
         |> PredVar.args_of
         |> List.map (fst >> Idnt.string_of)
       in
       Format.fprintf
         ocf
         ":extrapreds ((%a %a))@,"
         String.pr (p |> Idnt.string_of)
         (List.pr String.pr " ") args)
    tenv;
  List.iter
    (HornClause.formula_of
     >> CunFormula.sexp_of
     >> Format.fprintf ocf ":formula@,  %a@," String.pr)
    hcs;
  Format.fprintf ocf ")@]@?";
  close_out oc
let save_smtlib = Logger.log_block2 "HCCS.save_smtlib" save_smtlib

let save_smtlib2 filename hcs =
  let oc = open_out filename in
  let ocf = Format.formatter_of_out_channel oc in
  let is_real = ref false in
  let string_of_ty = function
    | ty when Type.is_int ty -> " Int"
    | ty when Type.is_real ty -> " Real"
    | ty when Type.is_bool ty -> " Bool"
    | ty when Type.is_var ty -> if !is_real then " Real" else " Int"
    | ty when Type.is_unit ty -> " Int" (* TODO: fix *)
    | ty -> Format.printf "unsupported type: %a@." Type.pr ty;
      assert false
  in
  let args_ty ty =
    let args, ret = Type.args_ret ty in
    assert(Type.is_bool ret);
    List.map string_of_ty args
  in
  let tenv = hcs |> tenv in
  let pvs =
    hcs
    |> pvs
    |> List.unique
    |> List.map (Pair.unfold Idnt.string_of (TypEnv.lookup tenv >> args_ty))
  in
  Format.fprintf ocf "@[<v>";
  Format.fprintf ocf "(set-logic HORN)@,";
  Format.fprintf ocf
    "(set-info :source |@,  Benchmark: %a@,  Generated by MoCHi@,|)@,"
    String.pr !Global.target_filename;
  Format.fprintf ocf "(set-info :status unknown)@,";
  List.iter
    (fun (x, tys) ->
       Format.fprintf
         ocf
         "(declare-fun %a (%a) Bool)@,"
         String.pr x
         (List.pr String.pr " ") tys)
    pvs;
  List.iter
    (fun hc ->
       let vs =
         hc
         |> HornClause.fvs_ty
         |> List.map
           (Pair.fold
              (fun x t -> "(" ^ Idnt.string_of x ^ string_of_ty t ^ ")"))
       in
       hc
       |> (if_ HornClause.is_goal
             (HornClause.formula_of
              >> Formula.bnot
              >> CunFormula.sexp_of
              >> (if vs = [] then
                    Format.fprintf ocf
                    "(assert (not %a))@,"
                    String.pr
                  else
                    Format.fprintf ocf
                    "(assert (not (exists (%a) %a)))@,"
                    (List.pr String.pr "") vs
                    String.pr))
             (HornClause.formula_of
              >> (CunFormula.sexp_of ~smt2:true)
              >> Format.fprintf ocf
                "(assert (forall (%a) %a))@,"
                (List.pr String.pr "") vs
                String.pr)))
    hcs;
  Format.fprintf ocf "(check-sat)@,";
  Format.fprintf ocf "(get-model)@,";
  Format.fprintf ocf "(exit)@,@]@?";
  close_out oc
let save_smtlib2 = Logger.log_block2 "HCCS.save_smtlib2" save_smtlib2

let int_to_real = List.map HornClause.int_to_real
let elim_ufuns = List.map HornClause.elim_ufuns



(** transform "?- P(x). P(x) :- phi1. P(x):- phi2." into "?- phi1. ?- phi2."*)
let goal_flattening hccs =
  let mpvs = mpvs hccs in
  let goals =
    goals_of hccs
    |> List.filter (HornClause.pvs >> List.length >> (=) 1)
    (* of the form ?- P(x) /\ phi. *)
    |> List.filter (HornClause.pvs >> Set_.inter mpvs >> (=) [])
    (* P occurs just once in the body of hccs
       P is therefore not recursive predicate variable *)
  in
  let target_pvs = pvs goals in
  Format.printf "target goals: %a@." pr goals;
  let target_hcs = (* rec.-free *)
    hccs
    |> List.filter
      (fun hc ->
         match HornClause.pvsH hc with
         | [x] -> List.mem x target_pvs
         | _ -> false)
  in
  Format.printf "target hccs: %a@." pr target_hcs;
  (* make psub for each target_hcs and apply *)
  let aux hc =
    let [target_pv] = HornClause.pvsH hc in
    let hc = HornClause.fresh hc in
    goals
    |> List.filter (HornClause.pvs >> List.mem target_pv)
    |> resolve [hc]
    |> (fun x -> Format.printf "[aux] psub-goals: %a@." pr x; x)
  in
  let goals' = List.concat_map aux target_hcs in
  hccs
  |> List.filter (flip List.mem (goals @ target_hcs) >> not)
  |> (fun x -> Format.printf "non-related HCCS: %a@." pr x; x)
  |> (@) goals'
  |> (fun x -> Format.printf "new HCCS: %a@." pr x; x)
