open Util
open Combinator

(** Polynomial constraint solvers *)

(** {6 Exceptions} *)

exception NoSolution
exception Unknown

type t = Formula.t -> (Idnt.t * Term.t) list

(** {6 Options} *)

let mask_coeffs = ref true
let cqp_mode = ref 0
let enable_lang_restrict = ref false
let lang_restrict_use_inequality = ref false
let lang_restrict_threshold = ref 3

(** {6 Printers} *)

let pr_elem ppf (c, t) = Format.fprintf ppf "%a = %a" Idnt.pr c Term.pr t
let pr ppf sol = List.pr pr_elem "@," ppf sol
 
(** {6 ?} *)

let check phi sol = phi |> Formula.subst sol |> SMTProver.is_valid_dyn

let gen_coeff_constr pos linear = Farkas.farkas ~pos ~linear
let gen_coeff_constr ?(pos = false) ?(linear = false) =
  Logger.log_block1
    ~after:(Logger.printf "new constraint on coefficients:@,  %a@," Formula.pr)
    "PolyConstrSolver.gen_coeff_constr"
    (gen_coeff_constr pos linear)

let solve_quick solver phi =
  if Formula.is_true phi then []
  else if Formula.is_false phi then raise NoSolution
  else solver phi

let solve_coeffs solver = solver >> List.filter (fst >> Idnt.is_coeff)
let solve_coeffs solver hcs =
  Logger.log_block2 "PolyConstrSolver.solve_coeffs"
    ~after:(Logger.printf "solution:@,  %a@," pr)
    solve_coeffs solver hcs

(** try to find a solution with as many coeffs in [zcs] be 0 as possible *)
let solve_with_zcs zcs solver phi =
  try
    if not !mask_coeffs then raise Unknown
    else
      let masked_coeffs = Set_.inter zcs (Formula.coeffs phi) in
      if masked_coeffs = [] then raise Unknown
      else
        let coeffs =
          masked_coeffs
          |> Logger.pprintf "masked_coeffs: %a@," Idnt.pr_list
          |> List.map (flip Pair.make IntTerm.zero(*@todo*))
        in
        phi
        |> Formula.subst coeffs
        |> FormulaSimplifier.simplify
        |> solver
        |> (@) coeffs
  with Unknown -> solver phi

(** [cand_sol] represents a candidate solution (default: []) *)
let solve_with_cand_sol cand_sol solver phi0 =
  let cand_sol_non_zero =
    List.filter_map
      (fun (x, n) -> if IntTerm.is_zero n then None else Some(x, n))
      cand_sol
  in
  let phi' = Formula.subst cand_sol_non_zero phi0 in
  phi'
  |> FormulaSimplifier.simplify
  |> Logger.pprintf2
    "solving constraints on coefficients%a:@,  %a@,"
    String.pr (if phi0 <> phi' then " (using the candidate solution)" else "")
    Formula.pr
  |> try_
    (solver >> (fun sol -> cand_sol_non_zero @ sol))
    (function
      | Unknown | NoSolution as e ->
        fun _ ->
          if phi0 = phi' then raise e
          else
            (** solve the constraint without using the candidate solution *)
            phi0
            |> (Logger.pprintf
                  "solving constraints on coefficients:@,  %a@,"
                  Formula.pr)
            |> solver
      | e -> fun _ -> raise e)
let solve_with_cand_sol =
  Logger.log_block3 "PolyConstrSolver.solve_with_cand_sol" solve_with_cand_sol

(** the coefficients in [phi] are of the int type
    the variables in [phi] are non-negative *)
let solve_int_by_nat natsolver phi =
  let sub =
    phi
    |> Formula.coeffs
    |> List.unique
    |> List.map
      (fun x ->
         x,
         IntTerm.sub
           (x |> Idnt.rename_base (fun id -> id ^ "_pos") |> Term.mk_var)
           (x |> Idnt.rename_base (fun id -> id ^ "_neg") |> Term.mk_var))
  in
  phi
  |> Formula.subst sub
  |> natsolver
  |> List.partition3_map
    (fun (x, n) ->
       let s = Idnt.base x in
       if String.ends_with s "_pos" then
         `L(Idnt.rename_base
              (fun _ -> String.sub s 0 (String.length s - 4)) x, n)
       else if String.ends_with s "_neg" then
         `C(Idnt.rename_base
              (fun _ -> String.sub s 0 (String.length s - 4)) x, n)
       else `R(x, n))
  |> (fun (pxs, nxs, xs) ->
      Logger.debug_assert (fun () -> List.eq_length pxs nxs);
      pxs
      |> List.map (fun (x, n) -> x, IntTerm.sub n (List.assoc_fail x nxs))
      |> flip (@) xs)

let solve_bounded solver phi =
  phi
  |> Formula.coeffs
  |> List.concat_map
    (fun c ->
       [IntFormula.leq (IntTerm.make (-1)) (Term.mk_var c);
        IntFormula.leq (Term.mk_var c) IntTerm.one])
  |> List.cons phi
  |> Formula.band
  |> solver

(* use inequalities *)
let lang_restriction_inequality real i =
  if real then
    List.map (fun v ->
        RealFormula.within
          (RealTerm.of_int (-i)) (Term.mk_var v) (RealTerm.of_int i))
    >> Formula.band
  else
    List.map (fun v ->
        IntFormula.within (IntTerm.make (-i)) (Term.mk_var v) (IntTerm.make i))
    >> Formula.band

(* use disjuctions of equalities *)
let lang_restriction_eq real i =
  if real then
    List.map
      (fun v ->
         List.from_to (-i) i
         |> List.map (fun n ->
             RealFormula.eq (RealTerm.of_int n) (Term.mk_var v))
         |> Formula.bor)
    >> Formula.band
  else
    List.map
      (fun v ->
         List.from_to (-i) i
         |> List.map (fun n ->
             IntFormula.eq (IntTerm.make n) (Term.mk_var v))
         |> Formula.bor)
    >> Formula.band

let solve_lang_restrict solver real phi =
  let rec aux i =
    if i > !lang_restrict_threshold then phi |> solver
    else
      try
        let cs = Formula.coeffs phi in
        (* @todo fvs restrict option *)
        let lang_restriction =
          if !lang_restrict_use_inequality
          then lang_restriction_inequality real i cs
          else lang_restriction_eq real i cs
        in
        Formula.mk_and phi lang_restriction
        |> solver
      with
      | Not_found -> assert false
      | Unknown | NoSolution -> aux (i + 1)
  in
  try aux 1 with Not_found -> assert false

let nat_constrs_of =
  List.unique >> List.map (Term.mk_var >> flip IntFormula.geq IntTerm.zero)

let solve_nat_fvs solver phi =
  Formula.fvs phi
  |> nat_constrs_of
  |> List.cons phi
  |> Formula.band
  |> solver
let solve_nat_fvs solver phi =
  Logger.log_block2 "PolyConstrSolver.solve_nat_fvs" solve_nat_fvs solver phi

let solve_nat solver phi =
  Formula.fvs phi @ Formula.coeffs phi
  |> nat_constrs_of
  |> List.cons phi
  |> Formula.band
  |> solver
let solve_nat solver phi =
  Logger.log_block2 "PolyConstrSolver.solve_nat" solve_nat solver phi

(** [integer] means if all the variables (not including the
    coefficients) are integer
    always find integer solution for the coefficients *)
let solve_coeffs_opt solver integer linear phi =
  let solver real =
    if !enable_lang_restrict
    then solve_lang_restrict solver real
    else solver
  in
  if integer then
    try
      phi
      |> Formula.map_atom (CunAtom.int_to_real >> Formula.of_atom)
      |> solve_coeffs (solver true)
      |> Polyhedron.cast_to_int
      |> function Some m -> m | None -> raise Unknown
    with NoSolution | Unknown ->
      phi |> solve_coeffs (solver false)
  else
    try
      phi
      |> solve_coeffs (solver true)
      |> Polyhedron.cast_to_int
      |> function Some m -> m | None -> raise Unknown
    with
    | (NoSolution as e) | (Unknown as e) ->
      try
        (* Z3 does not seem to support mixed integer non-linear
           constraint solving problems: Z3 immediately answers Unknown *)
        if linear then
          let tsub =
            phi
            |> Formula.coeffs
            |> List.map
              (fun x -> x, CunTerm.mk_coerce Type.mk_ir (Term.mk_var x))
          in
          phi
          |> Formula.subst tsub
          |> solve_coeffs (solver false)
        else raise e
      with
      | NoSolution | Unknown ->
        phi
        |> Formula.map_atom (CunAtom.real_to_int >> Formula.of_atom)
        |> solve_coeffs (solver false)


let ext_solve = ref (fun _ -> assert false : t)
let solve_dyn phi = !ext_solve phi
  (*if !enable_lang_restrict
  then solve_lang_restrict !ext_solve real phi
  else !ext_solve phi*)
let ext_solve_cvc3 = ref (fun _ -> assert false : t)
let solve_cvc3 phi = !ext_solve_cvc3 phi
let ext_solve_z3 = ref (fun _ -> assert false : t)
let solve_z3 phi = !ext_solve_z3 phi
let ext_solve_z3_unsatcore = ref (fun _ -> assert false : t)
let solve_z3_unsatcore phi = !ext_solve_z3_unsatcore phi
let ext_solve_glpk = ref (fun _ -> assert false : t)
let solve_glpk phi = !ext_solve_glpk phi
let ext_solve_gsl = ref (fun _ -> assert false : t)
let solve_gsl phi = !ext_solve_gsl phi
let ext_solve_nat_bv = ref (fun _ _ -> assert false : int -> t)
let solve_nat_bv rbit phi = !ext_solve_nat_bv rbit phi
let solve_nat_bv =
  Logger.log_block2 "PolyConstrSolver.solve_nat_bv" solve_nat_bv
let solve_bv rbit phi = solve_int_by_nat (solve_nat_bv rbit) phi
(** find integer solution using bit-vector modeling and SAT *)
let solve_bv = Logger.log_block2 "PolyConstrSolver.solve_bv" solve_bv
