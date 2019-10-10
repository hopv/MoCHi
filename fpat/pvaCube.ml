open Util
open Combinator

let disable_pred_sharing1 = ref false
let enable_pred_sharing2 = ref false

(** {6 Simplification of formulas with predicate symbols} *)

let ignored_vars vs pvas =
  let xs =
    pvas
    |> List.classify Pva.eq_idnt
    |> List.concat_map
      (List.map (Pva.args_of >> List.map fst)
       >> Matrix.transpose)
    |> List.concat_map
      (List.concat_map (Term.fvs >> List.unique)
       >> Bag.get_dup_elems
       (*Bag.get_dup_elems >> List.concat_map Formula.fvs*))
    |> List.unique
    |> flip Set_.diff vs
    |> Logger.pprintf "xs: %a@," Idnt.pr_list
  in
  let ys =
    pvas
    |> List.concat_map
      (Pva.args_of
       >> List.maplr
         (fun ttys1 (t, _) ttys2 ->
            let zs = List.unique (Term.fvs t) in
            if List.length zs > 1 then
              Set_.diff
                zs
                (xs
                 @ (List.concat_map
                      (fun (t, _) -> Term.fvs t)
                      (ttys1 @ ttys2)(*@todo*)))
            else
              [])
       >> List.flatten)
    |> List.unique
    |> Logger.pprintf "ys: %a@," Idnt.pr_list
  in
  xs @ ys
let ignored_vars = Logger.log_block2 "PvaCube.ignored_vars" ignored_vars

let changing_vars vs pvas =
  pvas
  |> List.classify Pva.eq_idnt
  |> List.concat_map
    (List.map (fun p -> List.map fst (Pva.args_of p)) >> Matrix.transpose)
  |> List.concat_map
    (fun ts ->
       let ts = List.unique ts in
       match ts with
       | [_] -> []
       | _ -> List.concat_map Term.fvs ts)
  |> List.unique
  |> flip Set_.diff vs

let fvs_body =
  List.concat_map (function `L(p) -> Pva.fvs p |`R(phi) -> Formula.fvs phi)
  >> List.unique
let pvs_body bd = List.concat_map (function `L(p, _) -> [p] | `R(_) -> []) bd
let atoms_of_body = List.filter_map (function `L(p) -> Some(p) | `R(_) -> None)
let terms_of_body =
  List.filter_map (function `L(_) -> None | `R(phi) -> Some(phi))
let body_of_atoms pvas = List.map (fun p -> `L(p)) pvas
let body_of_terms phis = List.map (fun phi -> `R(phi)) phis

(** @return whether bd1 and bd2 share a variable which is not in vs *)
let share_variable vs bd1 bd2 =
  Set_.intersects
    (Set_.diff (fvs_body bd1) vs)
    (Set_.diff (fvs_body bd2) vs)

let canonize_tsp env (ts1, ts2) = Set_.diff ts1 (env @ ts2), ts2

let canonize_pxs =
  List.sort
    (fun (_, _, _, ttyss1) (_, _, _, ttyss2) ->
        List.length ttyss1 - List.length ttyss2)
  >> List.filter (fun (_, ttys, _, ttyss) -> List.for_all ((<>) ttys) ttyss)

let rec is_covered_aux simplify tenv env tsp pxs =
  if List.for_all (fun (_, _, xs, _) -> xs = []) pxs then
    (SMTProver.implies_dyn ~tenv (env @ snd tsp) (fst tsp)
     && List.for_all
       (fun (p, ttys1, [], ttyss2) ->
          List.exists
            (fun ttys2 ->
               Pva.equiv
                 (SMTProver.implies_dyn ~tenv)
                 simplify
                 env
                 (Pva.make p ttys1)
                 (Pva.make p ttys2))
            ttyss2)
       pxs)
    |> (fun b ->
        if b then
          Logger.printf0 "succeeded@,"
        else
          begin
            Logger.printf "ts: %a@," Formula.pr_list (fst tsp);
            List.iter
              (fun (_, ttys, _, _) ->
                 Logger.printf "ttys: %a@," TypTerm.pr_list ttys)
              pxs;
            Logger.printf0 "failed:@,"
          end;
        b)
  else
    let (p, ttys1, xs, ttyss2) = List.hd pxs in
    let ttsubs =
      List.filter_map
        (fun ttys2 ->
           List.concat_map2
             (fun tty1 tty2 ->
                try
                  Unifier.match_tt
                    ~valid:(fun t -> SMTProver.implies_dyn ~tenv env [t])
                    xs
                    tty2
                    tty1
                with
                | Unifier.MayNotMatch ->
                  []
                | Unifier.NeverMatch ->
                  assert false)
             ttys1 ttys2
           |> (fun ttsub ->
               Logger.log
                 (fun () ->
                    if Formula.non_dup_ttsub
                        ~is_valid:(List.return
                                   >> SMTProver.implies_dyn ~tenv env)
                        ttsub
                       |> not then
                      begin
                        (*Format.printf "env: %a@," Term.pr (Formula.band env);
                          Format.printf "ttsub: %a@," TypTermSubst.pr ttsub;*)
                        (** this point is reachable even if Horn clauses are solvable
                            since env may not be complete (some fact from other predicate variables may be missing) *)
                        ()
                      end);
               ttsub)
           |> Option.of_list)
        ttyss2
    in
    List.exists
      (fun ttsub ->
         Logger.printf "ttsub: %a@," TypTermSubst.pr ttsub;
         let b =
           let tsp' =
             tsp
             |> (fun (ts1, ts2) ->
                 List.map
                   (Formula.subst (TypTermSubst.tsub_of ttsub) >>
                    simplify)
                   ts1,
                 ts2)
             |> canonize_tsp env
           in
           let pxs' =
             let update (p, ttys1, xs, ttyss2) =
               let xs' = Set_.diff xs (TypTermSubst.dom ttsub) in
               if List.eq_length xs' xs then
                 p, ttys1, xs, ttyss2
               else
                 begin
                   Logger.printf "p: %a@," Idnt.pr p;
                   let p', ttys1' =
                     Pva.make p ttys1
                     |> Pva.subst (TypTermSubst.tsub_of ttsub)
                     |> Pva.simplify
                     |> Pair.unfold Pva.idnt_of Pva.args_of
                   in
                   let ttyss2' =
                     List.filter
                       (fun ttys2 ->
                          Pva.matches
                            (SMTProver.implies_dyn ~tenv)
                            simplify
                            (fun x -> List.mem x xs')
                            env
                            (Pva.make p' ttys2)
                            (Pva.make p' ttys1'))
                       ttyss2
                   in
                   p', ttys1', xs', ttyss2'
                 end
             in
             pxs |> (List.map update) |> canonize_pxs
           in
           is_covered_aux simplify tenv env tsp' pxs'
         in
         if not b then Logger.printf0 "backtracked@,";
         b)
      ttsubs

(** @return whether bd1 is covered by bd2 under env
            for some substitution for variables not in vs *)
let is_covered simplify tenv env vs bd1 bd2 =
  let ts1 = terms_of_body bd1 in
  let ts2 = terms_of_body bd2 in
  let pvas1 = atoms_of_body bd1 in
  let pvas2 = atoms_of_body bd2 in

  let tsp = ts1, ts2 in
  let pxs =
    List.map
      (fun atm1 ->
         let xs = Set_.diff (Pva.fvs atm1) vs in
         let ttyss =
           List.filter_map
             (fun atm2 ->
                if Pva.matches
                    (SMTProver.implies_dyn ~tenv)
                    simplify
                    (fun x -> List.mem x xs)
                    env
                    atm2
                    atm1 then
                  Some(Pva.args_of atm2)
                else
                  None)
             pvas2
         in
         Pva.idnt_of atm1,
         Pva.args_of atm1,
         xs,
         ttyss)
      pvas1
  in
  is_covered_aux simplify tenv env (canonize_tsp env tsp) (canonize_pxs pxs)
let is_covered = Logger.log_block5 "PvaCube.is_covered" is_covered

(** @param vs are not eliminated *)
let prepare_bds simplify tenv vs0 vs (pvas, phis) =
  let phis0, phis1 =
    phis |> List.partition (fun phi -> Set_.subset (Formula.fvs phi) vs)
  in
  let pvas0, pvas1 =
    pvas
    |> List.partition (fun p -> Set_.subset (Pva.fvs p) vs)
    |> Pair.map_fst
      (List.classify Pva.eq_idnt
       >> List.concat_map
         (Set_.representatives
            (Pva.equiv
               (SMTProver.implies_dyn ~tenv)
               simplify
               phis0)))
  in
  let bds =
    (if pvas0 = [] then [] else [body_of_atoms pvas0])
    @ ((body_of_atoms pvas1(* ??redundant *)
        @ body_of_terms phis1)
       |> Set_.equiv_classes
         (fun b1 b2 -> share_variable vs [b1] [b2]))
  in
  let zs =
    pvas0
    |> List.concat_map Pva.fvs
    |> List.unique
    |> flip Set_.diff vs0
    |> List.filter
      (fun x ->
         match List.filter (fun bd -> List.mem x (fvs_body bd)) bds with
         | [_] -> true
         | _ -> false)
  in
  bds, phis0, zs
let prepare_bds = Logger.log_block4 "PvaCube.prepare_bds" prepare_bds

(** @param vs are not eliminated *)
let h simplify tenv vs0 cvs vs (bds, phis0, zs) =
  let rec aux bds1 bds2 =
    match bds1 with
    | [] -> bds2
    | ec :: bds1 ->
      let b =
        match cvs with
        | Some(xs) when not (Set_.intersects xs (fvs_body ec)) ->
          false
        | _ ->
          Logger.printf "checking: %a@," (List.pr Pva.pr ",") (atoms_of_body ec);
          is_covered simplify tenv phis0 vs ec (List.flatten (bds1 @ bds2))
      in
      aux bds1 (if b then bds2 else ec :: bds2)
  in
  let bds = aux (List.sort compare bds) [] in
  let pvas, phis = List.partition_map id (List.flatten bds) in
  pvas, Formula.band (phis @ phis0), zs
let h = Logger.log_block5 "PvaCube.h" h

(** @ensure vs are not eliminated *)
let simplify_psym_aux simplify qelim tenv vs0 cvs vs (pvas, phi) =
  (pvas, phi |> Formula.conjuncts_of)
  |> prepare_bds simplify tenv vs0 vs
  |> Triple.map_fst (qelim vs)
  |> h simplify tenv vs0 cvs vs
let simplify_psym_aux =
  Logger.log_block5 "PvaCube.simplify_psym_aux" simplify_psym_aux

let i simplify qelim tenv vs0 (pvas, phi) =
  let rec loop cvs vs (pvas, phi) =
    if vs <> [] then Logger.printf "vs: %a@," Idnt.pr_list vs;
    let pvas', phi', zs =
      simplify_psym_aux simplify qelim tenv vs0 cvs (vs0 @ vs) (pvas, phi)
    in
    if not (List.eq_length pvas pvas') && Pva.num_dup pvas' > 0 then
      let vs' = ignored_vars vs0 pvas' in
      let cvs' = Set_.diff vs vs' in
      if cvs' = [](*Set.equiv vs vs'*) then vs', (pvas', phi'), zs
      else loop (Some(cvs')) vs' (pvas', phi')
    else vs, (pvas', phi'), zs
  in
  loop None (ignored_vars vs0 pvas) (pvas, phi)
let i = Logger.log_block3 "PvaCube.i" i

let j simplify qelim tenv vs0 (vs, (pvas, phi), zs) =
  if not !enable_pred_sharing2 && !disable_pred_sharing1 then
    pvas, phi
  else if not !enable_pred_sharing2 then
    (*a-maxÇ™rsn 0Ç≈Ç»Ç¢Ç∆ê¨å˜ÇµÇ»Ç≠Ç»ÇÈ intro3ÇÕrsn0Ç≈OKÇ…Ç»ÇÈ*)
    try
      if zs <> [] then
        Logger.printf "zs: %a@," Idnt.pr_list zs;
      Set_.subsets_of_size 1 zs
      |> List.find_map
        (fun xs ->
           let vs1 = Set_.diff vs xs in
           if List.eq_length vs1 vs then
             None
           else
             let pvas', phi', _ =
               simplify_psym_aux simplify qelim
                 tenv vs0 (Some(xs)) (vs0 @ vs1) (pvas, phi)
             in
             if not (List.eq_length pvas pvas') then Some(pvas', phi')
             else  None)
    with Not_found -> pvas, phi
  else
    begin
      let zs = Set_.inter vs (changing_vars vs0 pvas) in
      if zs <> [] then Logger.printf "zs: %a@," Idnt.pr_list zs;
      if List.length zs > 7(*??*) then pvas, phi
      else
        try
          List.find_map
            (fun xs ->
               let vs1 = Set_.diff vs xs in
               if List.eq_length vs1 vs then None
               else
                 let pvas', phi', _ =
                   simplify_psym_aux simplify qelim
                     tenv vs0 (Some(xs)) (vs0 @ vs1) (pvas, phi)
                 in
                 if not (List.eq_length pvas pvas') then Some(pvas', phi')
                 else None)
            (Set_.subsets_of_size 1 zs @ Set_.subsets_of_size 2 zs)
        with Not_found -> pvas, phi
    end
let j = Logger.log_block2 "PvaCube.j" j

let simplify_psym simplify qelim tenv vs (pvas, phi) =
  let phi = simplify phi in
  if Pva.num_dup pvas = 0 || Formula.coeffs phi <> [] then pvas, phi
  else (pvas, phi) |> i simplify qelim tenv vs |> j simplify qelim tenv vs
let simplify_psym simplify qelim ?(tenv=[]) =
  Logger.log_block2 "PvaCube.simplify_psym" (simplify_psym simplify qelim tenv)
