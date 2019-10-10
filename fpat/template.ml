open Util
open Combinator

(** Formulas with unknown coefficients *)

let nonzero_const = ref []
let num_conj = ref 1
let num_disj = ref 1
let degree = ref 1
let linear_farkas = ref false

(* [etenv] represents if each variable in [tenv] is existentially quantified *)
let mk_linexp ?(etenv=[]) tenv =
  let real = List.exists (snd >> Type.is_real) tenv in
  let bound_coeff = ref [] in
  let unbound_coeff = ref [] in
  let etenv = if etenv = [] then List.map (fun _ -> false) tenv else etenv in
  let c = Term.new_coeff () in
  unbound_coeff := c :: !unbound_coeff;
  let templ =
    c ::
    List.filter_map2
      (fun (x, ty) b ->
         if Type.is_int ty || Type.is_var ty(*@todo*) then
           begin
             let c = Term.new_coeff () in
             if b then bound_coeff := c :: !bound_coeff
             else unbound_coeff := c :: !unbound_coeff;
             IntTerm.mul c (Term.mk_var x) |> Option.return
           end
         else if Type.is_real ty then
           begin
             let c = Term.new_coeff () in
             if b then bound_coeff := c :: !bound_coeff
             else unbound_coeff := c :: !unbound_coeff;
             RealTerm.mul c (Term.mk_var x) |> Option.return
           end
         else None (*@todo*))
      tenv etenv
    |> (if real then RealTerm.sum else (*@todo*)IntTerm.sum)
  in
  if !bound_coeff <> [] then
    begin
      let eq = if real then RealFormula.eq else IntFormula.eq in
      let zero = if real then RealTerm.zero else IntTerm.zero in
      nonzero_const :=
        Formula.imply
          (!bound_coeff |> List.map (flip eq zero) |> Formula.band)
          (!unbound_coeff |> List.map (flip eq zero) |> Formula.band)
        :: !nonzero_const;
    end;
  templ

let rec of_tenv tenv degree =
  if degree >= 1 then
    (List.map (Pair.map_fst Term.mk_var) tenv
    |> flip List.duplicate degree
    |> Vector.product id
    |> List.map (List.sort compare)
    |> List.unique
    |> List.map (fun ttys ->
        if List.exists (snd >> Type.is_real) ttys then
          List.map fst ttys |> RealTerm.prod, Type.mk_real
        else
          List.map fst ttys |> IntTerm.prod, Type.mk_int))
    @ of_tenv tenv (degree - 1)
  else
    []
let mk_polyexp tenv degree =
  let real = List.exists (snd >> Type.is_real) tenv in
  Term.new_coeff () ::
  List.filter_map
    (fun (t, ty) ->
       if Type.is_int ty || Type.is_var ty(*@todo*) then
         begin
           let c = Term.new_coeff () in
           IntTerm.mul c t |> Option.return
         end
       else if Type.is_real ty then
         begin
           let c = Term.new_coeff () in
           RealTerm.mul c t |> Option.return
         end
       else None (*@todo*))
    (of_tenv tenv degree)
  |> (if real then RealTerm.sum else (*@todo*)IntTerm.sum)


let mk_atom ?(etenv=[]) tenv degree =
  let real = List.exists (snd >> Type.is_real) tenv in
  let exp =
    if degree = 1 then mk_linexp ~etenv tenv
    else begin
      assert (etenv = []);
      mk_polyexp tenv degree
    end
  in
  if real
  then RealFormula.geq exp RealTerm.zero
  else IntFormula.geq exp IntTerm.zero

let make ?(etenv=[]) num_of_conjuncts num_of_disjuncts degree tenv =
  List.unfold
    (fun j ->
       if j < num_of_disjuncts then
         List.unfold
           (fun i ->
              if i < num_of_conjuncts
              then Some(mk_atom ~etenv tenv degree, i + 1)
              else None)
           0
         |> Formula.band
         |> flip Pair.make (j + 1) |> Option.return
       else None)
    0
  |> Formula.bor

(** make bounds of the last variable in [tenv] *)
let make_bounds ?(use_init=true) tenv =
  let c = Term.new_coeff () in
  let init, last = List.initial tenv, List.last tenv in
  let templ =
    if use_init then
      begin
        c :: List.filter_map
          (fun (x, ty) ->
             if Type.is_int ty then
               let c = Term.new_coeff () in
               IntTerm.mul c (Term.mk_var x) |> Option.return
             else
               None (*@todo*))
          init
        |> IntTerm.sum
      end
    else c
  in
  Formula.mk_and
    (IntFormula.leq IntTerm.zero (Term.mk_var (fst last)))
    (IntFormula.leq (Term.mk_var (fst last)) templ)

let mk_psub ?(psub=[]) =
  List.filter (fst >> flip List.mem_assoc psub >> not)
  >> List.map
    (fun (pid, ty) ->
       PredVar.of_type pid ty
       |> PredVar.args_of
       |> Pair.unfold id (make !num_conj !num_disj !degree)
       |> Pair.make pid)
  >> (@) psub
