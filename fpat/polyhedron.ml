open Util
open Combinator

(** Polyhedrons (polytopes) *)

type optmodel =
  | Point of SMTProver.model
  | ExPoint of SMTProver.model * Term.t
  | Ray of SMTProver.model * SMTProver.model
  | Polytope of Formula.t * SMTProver.model
  | ExPolytope of Formula.t * SMTProver.model
let disable_ray = ref false
let enable_pol = ref false

let ext_convex_hull = ref (fun _ -> assert false : Formula.t -> Formula.t)
let convex_hull_dyn phi = !ext_convex_hull phi
let ext_widen_list = ref (fun _ -> assert false : Formula.t list -> Formula.t)
let widen_list_dyn phis = !ext_widen_list phis

(*@todo*)
let infinity =
  float_of_int max_int
  (*max_float /. 2.0*)
  (*1000.0*)

(** distance of the point [xs] from the hyperplane [cxs, c0] *)
let distance_from_hyperplane xs cxs c0 =
  if cxs = [] then
    begin
      if c0 <= 0.0 then
        (* true case *)
        assert false
        (*RealTerm.make (-.infinity)*)
      else
        (* false case *)
        assert false
        (*RealTerm.make infinity*)
    end
  else
    let normal =
      List.map
        (fun x ->
           (try List.find (snd >> (=) x) cxs |> fst
            with Not_found -> Coeff.CoeffReal.zero),
           x)
        xs
    in
    let unormal =
      let norm =
        List.map2 (fun (c1, _) (c2, _) -> c1 *. c2) normal normal
        |> Float.sum_list
        |> sqrt
      in
      List.map (fun (c, x) -> c /. norm) normal
    in
    (** point = (0, ..., 0, -c0 / normal.y, 0, ..., 0) is a point
        on the hyperplane *)
    let point =
      let y =
        List.fold_left
          (fun (c, x) (c', x') ->
             if abs_float c >= abs_float c' then (c,x) else (c', x'))
          (0.0, Idnt.make "error") cxs
        |> snd
      in
      List.map
        (fun (c, x) -> if x = y then -.c0 /. c else 0.0)
        normal
    in
    (** compute unormal . (xs - point) *)
    List.map3
      (fun cu cp x ->
         RealTerm.mul
           (RealTerm.make cu)
           (RealTerm.add (Term.mk_var x) (RealTerm.make (-.cp))))
      unormal point xs
    |> RealTerm.sum

let distance_from_lit xs lit =
  Literal.fold
    (CunAtom.fold
       (object
         method fvar x [] = assert false
         method feq _ t1 t2 = assert false
         method fneq _ t1 t2 = assert false
         method flt ty t1 t2 =
           let cxs, c0 =
             if Type.is_real ty then
               let Const.Lt(_), (cxs, c0) =
                 LinRealRel.of_formula (RealFormula.lt t1 t2)
               in
               cxs, c0
             else
               let Const.Lt(_), (cxs, c0) =
                 LinIntRel.of_formula (IntFormula.lt t1 t2)
               in
               List.map (Pair.map_fst Coeff.int_to_real) cxs,
               Coeff.int_to_real c0
           in
           distance_from_hyperplane xs cxs c0
         method fgt _ t1 t2 = assert false
         method fleq ty t1 t2 =
           let cxs, c0 =
             if Type.is_real ty then
               let Const.Leq(_), (cxs, c0) =
                 LinRealRel.of_formula (RealFormula.leq t1 t2)
               in
               cxs, c0
             else
               let Const.Leq(_), (cxs, c0) =
                 LinIntRel.of_formula (IntFormula.leq t1 t2)
               in
               List.map (Pair.map_fst Coeff.int_to_real) cxs,
               Coeff.int_to_real c0
           in
           distance_from_hyperplane xs cxs c0
         method fgeq _ t1 t2 = assert false
         method fdivides n t = assert false
         method frecognizer ty id r = assert false
         method fsmem _ t1 t2 = assert false
         method fssubset _ t1 t2 = assert false
         method fterm _ _ = assert false
       end))
    (fun _ -> assert false)
    lit
let distance_from_lit =
  Logger.log_block2
    "Polyhedron.distance_from_lit"
    ~before:(fun ids lit->
        Logger.printf2 "ids: %a@,lit: %a@," Idnt.pr_list ids Literal.pr lit)
    ~after:(Logger.printf "output: %a" Term.pr)
    distance_from_lit

let assign_max x =
  List.maplr
    (fun xs1 x0 xs2 ->
       Formula.imply
         (List.map
            (Term.mk_var >> RealFormula.geq (Term.mk_var x0))
            (xs1 @ xs2)
          |> Formula.band)
         (RealFormula.eq (Term.mk_var x) (Term.mk_var x0)))
  >> Formula.band

let assign_min x =
  List.maplr
    (fun xs1 x0 xs2 ->
       Formula.imply
         (List.map
            (Term.mk_var >> RealFormula.leq (Term.mk_var x0))
            (xs1 @ xs2)
          |> Formula.band)
         (RealFormula.eq (Term.mk_var x) (Term.mk_var x0)))
  >> Formula.band

let distance_from_formula xs phi =
  let ds =
    phi
    |> DNF.of_formula
    |> DNF.map_literal
      (Literal.fold
         (CunAtom.elim_geq >> CunAtom.elim_lt_gt >> Literal.of_atom)
         (CunAtom.negate >> Literal.atom_of >>
          CunAtom.elim_geq >> CunAtom.elim_lt_gt >> Literal.of_atom))
    |> Logger.pprintf "elim: %a@," DNF.pr
    |> DNF.cubes_of
    |> List.map @@ List.map @@
    (fun lit -> Idnt.new_var (), distance_from_lit xs lit)
    |> Logger.pprintf "ds:@, [%a]@,"
      (List.pr (List.pr (Pair.pr Idnt.pr Term.pr) ",") "@,")
  in
  let es =
    ds
    |> List.map
      (fun d ->
         let x = Idnt.new_var () in
         x, assign_max x (List.map fst d))
  in
  let d = Idnt.make "distance" in
  let constr =
    Formula.band
      ([RealFormula.gt (Term.mk_var d) RealTerm.zero;
        (*RealFormula.leq (Term.mk_var d) (RealTerm.make infinity)*)]
       (* to avoid bigint*)
       @ (ds
          |> List.flatten
          |> List.map (fun (d, dexp) -> RealFormula.eq (Term.mk_var d) dexp))
       @ (es |> List.map snd)
       @ [assign_min d (List.map fst es)])
  in
  Logger.printf "distance constr:@, %a@," Formula.pr constr;
  d, constr

let find_extremal_int phi1 phi2 =
  let xs = Formula.fvs phi1 @ Formula.fvs phi2 |> List.unique in
  let tsub =
    List.map
      (fun x ->
         x,
         CunTerm.mk_coerce
           (Type.mk_fun [Type.mk_int; Type.mk_real])
           (Term.mk_var x))
      xs
  in
  if SMTProver.is_valid_dyn phi2 ||
     SMTProver.is_valid_dyn (Formula.bnot phi2) then
    let phi1 = Formula.subst tsub phi1 in
    (* @todo Should we find some generator of [phi1] instead? *)
    let m =
      SMTProver.solve_dyn
        ~tenv:(List.map (flip Pair.make Type.mk_int) xs)
        phi1
      |> flip Map_.restrict xs
    in
    Point m
  else
    let d, constr = distance_from_formula xs phi2 in
    let phi1 = Formula.subst tsub phi1 in
    let constr = Formula.subst tsub constr in
    try
      let m, dist =
        SMTProver.solve_opt
          ~tenv:((d, Type.mk_real) :: List.map (flip Pair.make Type.mk_int) xs)
          (Formula.mk_and phi1 constr)
          (SMTProver.Max (Term.mk_var d))
      in
      let m = m |> flip Map_.restrict xs in
      ExPoint(m, dist)
    with
    | SMTProver.Unbounded(d, o) ->
      if !enable_pol || !disable_ray then
        let o = o |> flip Map_.restrict xs in
        Point o
      else
        let d = d |> flip Map_.restrict xs in
        let o = o |> flip Map_.restrict xs in
        Ray(d, o)
    | SMTProver.Unsat | SMTProver.Unknown ->
      Format.printf
        "extremal counterexamle sampling failed!@.  phi1: %a@.  phi2: %a@."
        Formula.pr phi1 Formula.pr phi2;
      let m =
        SMTProver.solve_dyn
          ~tenv:(List.map (flip Pair.make Type.mk_int) xs)
          phi1
        |> flip Map_.restrict xs
      in
      Point m

let cast_to_int m =
  if List.for_all
      (fun (_, t) ->
         try
           let f = t |> RealTerm.float_of in
           f = float_of_int (Float.round f)
         with Not_found -> false)
      m
  then
    Some
      (List.map
         (fun (x, t) ->
            try
              x, t |> RealTerm.float_of |> Float.round |> IntTerm.make
            with Not_found -> assert false)
         m)
  else None

let find_extremal retint phi1 phi2 =
  let xs = Formula.fvs phi1 @ Formula.fvs phi2 |> List.unique in
  if SMTProver.is_valid_dyn phi2 ||
     SMTProver.is_valid_dyn (Formula.bnot phi2) then
    (* @todo Should we find some generator of [phi1] instead? *)
    let m =
      SMTProver.solve_dyn
        ~tenv:(List.map (flip Pair.make Type.mk_real) xs)
        phi1
      |> flip Map_.restrict xs
    in
    if retint then
      match cast_to_int m with
      | Some(m) -> Point m
      | None ->
        Format.printf "non-integer point found:@.  %a@." TermSubst.pr m;
        Format.printf "resorting to mixed integer optimization@.";
        find_extremal_int phi1 phi2
    else Point m
  else
    let d, constr = distance_from_formula xs phi2 in
    try
      let m, dist =
        SMTProver.solve_opt
          ~tenv:((d, Type.mk_real)::List.map (flip Pair.make Type.mk_real) xs)
          (Formula.mk_and phi1 constr)
          (SMTProver.Max (Term.mk_var d))
      in
      let m = m |> flip Map_.restrict xs in
      if retint then
        match cast_to_int m with
        | Some(m) -> ExPoint(m, dist)
        | None ->
          Format.printf "non-integer extremal point found:@.  %a@." TermSubst.pr m;
          Format.printf "resorting to mixed integer optimization@.";
          find_extremal_int phi1 phi2
      else ExPoint(m, dist)
    with
    | SMTProver.Unbounded(d, o) ->
      if !enable_pol || !disable_ray then
        let o = o |> flip Map_.restrict xs in
        if retint then
          match cast_to_int o with
          | Some(o) -> Point o
          | None ->
            Format.printf "non-integer point found:@.  %a@." TermSubst.pr o;
            Format.printf "resorting to mixed integer optimization@.";
            find_extremal_int phi1 phi2
        else Point o
      else
        let d = d |> flip Map_.restrict xs in
        let o = o |> flip Map_.restrict xs in
        if retint then
          match cast_to_int d, cast_to_int o with
          | Some(d), Some(o) -> Ray(d, o)
          | _, _ ->
            Format.printf
              "non-integer ray found:@.  %a@."
              (Pair.pr TermSubst.pr TermSubst.pr) (d, o);
            Format.printf "resorting to mixed integer optimization@.";
            find_extremal_int phi1 phi2
        else Ray(d, o)
    | SMTProver.Unsat | SMTProver.Unknown ->
      Format.printf
        "extremal counterexamle sampling failed!@.  phi1: %a@.  phi2: %a@."
        Formula.pr phi1 Formula.pr phi2;
      try
        let m =
          SMTProver.solve_dyn
            ~tenv:(List.map (flip Pair.make Type.mk_real) xs)
            phi1
          |> flip Map_.restrict xs
        in
        if retint then
          match cast_to_int m with
          | Some(m) -> Point m
          | None ->
            Format.printf "non-integer point found:@.  %a@." TermSubst.pr m;
            Format.printf "resorting to mixed integer optimization@.";
            find_extremal_int phi1 phi2
        else Point m
      with SMTProver.Unsat | SMTProver.Unknown -> assert false
(** find a point generator of [phi1] whose distance from the surface
    of [phi2] is maximal
    @todo if no such point exists, find a ray generator of [phi1]
    @note a line generator can be represented by a pair of opposite
    ray generators *)
let find_extremal ?(retint=false) =
  Logger.log_block2
    "Polyhedron.find_extremal"
    ~before:(fun phi1 phi2 ->
        Logger.printf2 "phi1: %a@,phi2: %a@," Formula.pr phi1 Formula.pr phi2)
    (*~after:(Logger.printf "output: %a" TermSubst.pr)*)
    (find_extremal retint)

let map_model f = function
  | Point(o) -> Point(f o)
  | ExPoint(o, dist) -> ExPoint(f o, dist)
  | Ray(d, o) -> Ray(f d, f o)
  | Polytope(phi, m) -> Polytope(phi, f m)
  | ExPolytope(phi, m) -> ExPolytope(phi, f m)
