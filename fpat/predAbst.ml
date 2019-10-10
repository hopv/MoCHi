open Util
open Combinator

(** Predicate abstraction *)

let use_cfp = ref false
let wp_max_num = ref 3
let use_neg_pred = ref false
let incomplete_opt = ref true

let imply env pbs phi =
  let ps, _ = List.split pbs in
  SMTProver.implies_dyn (List.rev_append env ps) [phi]

let abst_conj_of pbs =
  List.fold_left
    (fun phi (_, b) -> Formula.band [phi; b])
    Formula.mk_true
    pbs
let abst_dnf_of pbss =
  List.fold_left
    (fun phi pbs -> Formula.bor [phi; abst_conj_of pbs])
    Formula.mk_false
    pbss

let rec meaningful w =
  match w with
  | [] -> true
  | a :: b -> not (List.mem (-a) b) && meaningful b

let of_pbs ds =
  let nds = List.map (Pair.lift Formula.bnot) ds in
  List.map
    (fun i ->
       if i > 0 then List.nth ds (i - 1)
       else if i < 0 then List.nth nds (-i - 1)
       else assert false)


(** assumes that [pbss1'] and [pbss2'] are disjoint *)
let rec weakest env phi pbss1' pbss2' pbss3' pbss of_pbs =
  let pbss1, pbss2, pbss3 =
    List.partition3_map
      (fun pbs ->
         let phis = of_pbs pbs in
         if !incomplete_opt &&
            Set_.disjoint (List.concat_rev_map Formula.fvs (phi :: env))
              (phis |> List.concat_map (fst >> Formula.fvs)) then
           (** @require env /\ phis is sat and phi is neither tautology nor contradiction *)
           `C(pbs)
         else if imply env phis phi then `L(pbs)
         else if imply env phis (Formula.bnot phi) then `R(pbs)
         else `C(pbs))
      pbss
    |> Triple.map
         ((@) pbss1' >> List.unique)
         ((@) pbss2' >> List.unique)
         ((@) pbss3' >> List.unique)
  in
  List.concat_map
    (fun pbs1 ->
       List.map (fun pbs2 -> List.sort compare (List.unique (pbs1 @ pbs2))) pbss2)
    pbss2
  |> List.unique
  |> List.filter
    (if_ (List.length >> (<) !wp_max_num) (const false) meaningful)
  |> if_ (const false)
    (flip Set_.diff pbss2)
    (List.filter (fun pbs -> not (List.exists (Set_.subset pbs) pbss2)))
  |> List.filter
    (fun pbs ->
       not (List.exists (flip Set_.subset pbs) pbss1) &&
       not (List.exists (flip Set_.subset pbs) pbss3))
  |> Set_.cover
  |> if_ ((=) []) (const (pbss1, pbss3))
    (flip (weakest env phi pbss1 pbss2 pbss3) of_pbs)
(** compute the weakest (psi1, psi2) in the boolean closure of ds
    such that env |= psi1 => phi1 and env |= psi2 => phi2
    ds is a list of pairs of formulas and corresponding boolean variables *)
let weakest env ds phi =
  if !incomplete_opt && imply env [] phi then
    Formula.mk_true, Formula.mk_false(* @todo may not be the weakest *)
  else if !incomplete_opt && imply env [] (Formula.bnot phi) then
    Formula.mk_false(* @todo may not be the weakest *), Formula.mk_true
  else
    let ds =
      ds
      |> (if !incomplete_opt then
            let fvs =
              let fvss =
                List.map fst ds
                |> List.rev_append env
                |> List.map Formula.fvs
              in
              let rec fixp xs =
                let xs' =
                  fvss
                  |> List.concat_map
                    (fun fvs -> if Set_.inter fvs xs = [] then [] else fvs)
                  |> (@) xs
                  |> List.unique
                in
                if List.eq_length xs xs' then xs else fixp xs'
              in
              fixp (Formula.fvs phi)
            in
            List.filter (fst >> Formula.fvs >> flip Set_.subset fvs)
          else id)
    in
    let of_pbs = of_pbs ds in
    weakest
      env
      phi
      [] [] []
      ([] :: List.mapi (fun i _ -> [i+1]) ds @
       if !use_neg_pred then List.mapi (fun i _ -> [-i-1]) ds else [])
      of_pbs
    |> Pair.lift (List.map of_pbs)
    |> Pair.lift (List.filter (flip (imply env) Formula.mk_false >> not))
    |> Pair.lift abst_dnf_of

let rec min_unsat_cores of_pbs env pbss1' pbss2' pbss =
  let pbss1, pbss2 =
    List.partition
      (fun pbs ->
         let phis = of_pbs pbs in
         imply env phis Formula.mk_false)
      pbss
    |> Pair.map ((@) pbss1' >> List.unique) ((@) pbss2' >> List.unique)
  in
  List.concat_map
    (fun pbs1 ->
       List.map (fun pbs2 -> List.sort compare (List.unique (pbs1 @ pbs2))) pbss)
    pbss2
  |> List.unique
  |> List.filter
    (if_ (List.length >> (<) !wp_max_num) (const false) meaningful)
  |> List.filter (fun pbs -> not (List.exists (Set_.subset pbs) pbss2))
  |> List.filter (fun pbs -> not (List.exists (flip Set_.subset pbs) pbss1))
  |> Set_.cover
  |> if_ ((=) []) (const pbss1) (min_unsat_cores of_pbs env pbss1 pbss2)
let min_unsat_cores env ds =
  let of_pbs = of_pbs ds in
  min_unsat_cores
    of_pbs
    env
    []
    []
    ([] :: List.mapi (fun i _ -> [i+1]) ds)
  |> List.map of_pbs
  |> abst_dnf_of


let test () =
  let x = Term.mk_var (Idnt.make "x") in
  let x1 = Term.mk_var (Idnt.make "x1") in
  let x2 = Term.mk_var (Idnt.make "x2") in
  let i = Term.mk_var (Idnt.make "i") in
  let m = Term.mk_var (Idnt.make "m") in
  let cond1 = Formula.mk_brel (Const.Gt Type.mk_int) x2 m in
  let cond2 = Formula.mk_brel (Const.Lt Type.mk_int) i x in
  let p1 =
    Formula.mk_brel
      (Const.Leq Type.mk_int)
      x1
      (Term.mk_const @@ Const.Int 0) in
  let p2 = Formula.mk_brel (Const.Geq Type.mk_int) x2 x in
  let p3 =
    Formula.mk_brel
      (Const.Leq Type.mk_int)
      i
      (Term.mk_const @@ Const.Int 0) in
  let env = [cond1; cond2] in
  let ds = [p1, Formula.of_term x1;
            p2, Formula.of_term x2;
            p3, Formula.of_term m] in
  let p =
    Formula.mk_brel
      (Const.Leq Type.mk_int)
      x1
      (Term.mk_const @@ Const.Int 0) in
  Format.printf "weakest: %a@,"
    (Pair.pr Formula.pr Formula.pr) (weakest env ds p);
  Format.printf "min unsat cores: %a@," Formula.pr (min_unsat_cores env ds)
