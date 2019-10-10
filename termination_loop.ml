open Util
open Mochi_util
open BRA_types
open BRA_transform

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let (|>) = BRA_util.(|>)

let mapOption (f : 'a -> 'b option) (lst : 'a list) =
  let rec go = function
    | [] -> []
    | x::xs ->
      match f x with
	| Some y -> y :: go xs
	| None -> go xs
  in go lst
let flip f x y = f y x

(***** information *****)

let lrf = ref []
let max_threshold = 15

let preprocessForTerminationVerification = ref (fun (x : Syntax.term) -> x)

exception FailedToFindLLRF
exception InferenceFailure

let counter = ref 0
let get_now () = (counter := !counter + 1; !counter - 1)
let reset_counter () = counter := 0

let cycle_counter = ref 0
let incr_cycle () = cycle_counter := !cycle_counter + 1
let reset_cycle () = cycle_counter := 0

let rec remove_coeff_defs coeffs t =
  let open Syntax in
  match t.desc with
  | Local(Decl_let[x, t1], t2) when Id.mem x coeffs ->
      let n = Term_util.int_of_term t1 in
      let sol,t2' = remove_coeff_defs coeffs t2 in
      (x,n)::sol, t2'
  | _ -> [], t

let set_to_coeff exparam t = Trans.map_id (fun x -> if Id.mem x exparam then Id.add_attr Id.Coefficient x else x) t

let save_counter = ref 0
let save_to_file t =
  incr save_counter;
  let ext = string_of_int !save_counter ^ ".ml" in
  let filename = Filename.change_extension !!Flag.Input.main ext in
  let cout = open_out filename in
  let fm = Format.formatter_of_out_channel cout in
  Format.fprintf fm "%a@." Print.as_ocaml_typ t;
  close_out cout

let verify_with holed exparam_sol pred =
  (* combine holed program and predicate *)
  let transformed = pluging holed pred in
  let coeffs = List.filter (List.mem Id.Coefficient -| Id.attr) @@ Term_util.get_top_funs holed.program in
  Verbose.printf "[%d]@.%a@." (get_now ()) Print.term transformed;
  let orig, transformed = retyping transformed @@ BRA_state.type_of_state holed in
  let exparam_sol',transformed = remove_coeff_defs coeffs transformed in
  let exparams = List.map fst exparam_sol' in
  let transformed = set_to_coeff exparams transformed in
  let exparam_sol'' =
    exparams
    |> List.filter_out (Id.mem_assoc -$- exparam_sol)
    |> List.map (Pair.add_right @@ Fun.const 0)
    |> (@) exparam_sol
  in
  if !!Debug.check then
    transformed
    |> List.fold_right (fun (x,n) -> Term_util.subst x @@ Term_util.make_int n) exparam_sol''
    |> save_to_file;
  Main_loop.run ~exparam_sol:exparam_sol'' ~orig @@ Problem.safety transformed

let inferCoeffs argumentVariables linear_templates constraints =
  (* reduce to linear constraint solving *)
  let generate = Fpat.PolyConstrSolver.gen_coeff_constr ~pos:false ~linear:true in
  (** solve constraint and obtain coefficients **)
  let correspondenceVars = constraints |> generate |> Fpat.PolyConstrSolver.solve_dyn in
  begin
    if correspondenceVars = [] then (Format.eprintf "Invalid ordered.@."; raise Fpat.PolyConstrSolver.Unknown);
    Verbose.printf "Inferred coefficients:@.  %a@." Fpat.PolyConstrSolver.pr correspondenceVars;

    List.map (fun linTemp ->
      (* EXAMPLE: ([v1 -> 1][v2 -> 0][v3 -> 1]..., v0=2) *)
      let ((correspondenceCoeffs, const_part) as ranking_function) =
        Fpat.LinTermIntExp.of_term @@ Fpat.Term.subst correspondenceVars linTemp
      in
      (** extract coefficients **)
      let coefficients =
	let formatter (n, v) = (v, Fpat.IntTerm.int_of n) in
        let dict = List.map formatter correspondenceCoeffs in
	let cor x = List.assoc_default 0 x dict in
	List.map cor argumentVariables
      in
      {coeffs = coefficients; constant = Fpat.IntTerm.int_of const_part}
    ) linear_templates
  end

let inferCoeffsAndExparams argumentVariables linear_templates constraints =
  let generate = Fpat.PolyConstrSolver.gen_coeff_constr ~pos:false ~linear:false in
  (** solve constraint and obtain coefficients **)
  let correspondenceVars = constraints |> generate |> Fpat.PolyConstrSolver.solve_dyn in
  begin
    if correspondenceVars = [] then (Format.eprintf "Invalid ordered.@."; raise Fpat.PolyConstrSolver.Unknown);
    Verbose.printf "Inferred coefficients:@.  %a@." Fpat.PolyConstrSolver.pr correspondenceVars;

    (List.map (fun linTemp ->
      (* EXAMPLE: ([v1 -> 1][v2 -> 0][v3 -> 1]...[vn -> 0], v0=2) *)
      let correspondenceCoeffs, const_part =
        Fpat.LinTermIntExp.of_term
          (Fpat.Term.subst correspondenceVars linTemp)
      in
      (** extract coefficients **)
      let coefficients =
	let formatter (n, v) = (v, Fpat.IntTerm.int_of n) in
        let dict = List.map formatter correspondenceCoeffs in
	let cor x = List.assoc_default 0 x dict in
	List.map cor argumentVariables
      in
      {coeffs = coefficients; constant = Fpat.IntTerm.int_of const_part}
     ) linear_templates,
     let correspondenceExparams =
       List.map (fun (v, t) ->
                 let n = Fpat.IntTerm.int_of t in
                 (v |> Fpat.Idnt.string_of |> (flip Id.from_string) Type.Ty.int, n))
                (List.filter (fun (v, _) -> v |> Fpat.Idnt.is_coeff) correspondenceVars)
     in
     correspondenceExparams
    )
  end

let makeLexicographicConstraints variables linearTemplates prevLinearTemplates failedSpc =
  (** make a constraint:
         [spc1 => R1(x_prev) > R1(x) /\ R1(x) >= 0]
      /\ [spc2 => R1(x_prev) >= R1(x)
               /\ R2(x_prev) > R2(x) /\ R2(x) >= 0]
      /\ [spc3 => R1(x_prev) >= R1(x)
               /\ R2(x_prev) >= R2(x)
               /\ R3(x_prev) > R3(x) /\ R3(x) >= 0]
      ...
  **)
  let lenSpcSequence = List.length failedSpc in
  let subst_ith i =
    Fpat.Formula.subst
      (List.map
        (fun v -> (v, Fpat.Term.mk_var (Fpat.Idnt.rename_base (fun v -> v ^ "_IN_" ^ string_of_int i ^ "TH_ERRORPATH") v)))
        variables)
  in
  let nth_constraints n =
    let rec go i =
      let ith_ltp, ith_lt = List.nth prevLinearTemplates i, List.nth linearTemplates i in
      if i < n then
        (Fpat.NumAtom.geq Fpat.Type.mk_int ith_ltp ith_lt |> Fpat.Formula.of_atom) :: go (i+1)
      else
        [Fpat.NumAtom.gt Fpat.Type.mk_int ith_ltp ith_lt |> Fpat.Formula.of_atom;
         Fpat.NumAtom.geq Fpat.Type.mk_int ith_lt (Fpat.IntTerm.make 0) |> Fpat.Formula.of_atom]
    in
    subst_ith n (Fpat.Formula.band [List.nth failedSpc n; Fpat.Formula.bnot (Fpat.Formula.band (go 0))])
  in
  Fpat.Formula.bor (Fpat.Util.List.unfold (fun i -> if i < lenSpcSequence then Some (nth_constraints i, i+1) else None) 0)

let rec enqueueNextPredicateInfo que =
  if Queue.is_empty que then None
  else
    let nextGen = Queue.pop que in
    try Some (nextGen ()) with _ -> enqueueNextPredicateInfo que

let rec run predicate_que holed =
  let _ =
    begin
      incr_cycle ();
      if !cycle_counter > max_threshold then (raise FailedToFindLLRF)
    end
  in
  match enqueueNextPredicateInfo predicate_que with
    | None -> (raise FailedToFindLLRF)
    | Some predicate_info ->
      (* result log update here *)
      lrf := BRA_util.update_assoc (Id.to_string holed.verified.id, !cycle_counter, predicate_info) !lrf;

      try
	let result = if !Flag.Termination.separate_pred then
	    let predicates = separate_to_CNF (construct_LLRF predicate_info) in
            List.for_all (verify_with holed predicate_info.coeffsMap) predicates
	  else if !Flag.Termination.split_callsite then
	    let predicate = construct_LLRF predicate_info in
	    let splited = callsite_split holed in
	    reset_counter ();
	    List.for_all (fun h -> verify_with h predicate_info.coeffsMap predicate) splited
	  else
	    let predicate = construct_LLRF predicate_info in
	    verify_with holed predicate_info.coeffsMap predicate
	in
	if result then
	  (Verbose.printf "%s is terminating.@." holed.verified.id.Id.name ; result)
	else
	  (Verbose.printf "%s is possibly non-terminating.@." holed.verified.id.Id.name ; result)
      with Refine.PostCondition (env, spc, spcWithExparam) ->
	let unwrap_template = function (Fpat.Term.App (Fpat.Term.App (_, t), _)) -> t | _ -> assert false in
	let unwrap_template t = unwrap_template (Fpat.Formula.term_of t) in
	let arg_vars =
	  List.map (fun v -> Fpat.Idnt.make (Id.to_string (extract_id v)))
	    (BRA_state.get_argvars holed.state holed.verified) in
	let prev_vars =
	  List.map (fun v -> Fpat.Idnt.make (Id.to_string (extract_id v)))
	    (BRA_state.get_prev_statevars holed.state holed.verified) in
	let prev_var_terms = List.map Fpat.Term.mk_var prev_vars in
	let arg_env = List.map (fun a -> (a, Fpat.Type.mk_int)) arg_vars in

	if !Flag.Termination.disjunctive then
	  (* make templates *)
	  let linear_template = unwrap_template (Fpat.Template.mk_atom arg_env 1) in
	  let linear_template_prev = Fpat.Term.subst (List.combine arg_vars prev_var_terms) linear_template in
	  Verbose.printf "Linear template:@.  %a@." Fpat.Term.pr linear_template;

	  (* make a constraint: spc => R(x_prev) > R(x) && R(x) >= 0 *)
	  let constraints =
	    Fpat.Formula.band [spc; Fpat.Formula.bnot
	      (Fpat.Formula.band [ Fpat.NumAtom.gt Fpat.Type.mk_int linear_template_prev linear_template |> Fpat.Formula.of_atom
			    ; Fpat.NumAtom.geq Fpat.Type.mk_int linear_template (Fpat.IntTerm.make 0) |> Fpat.Formula.of_atom])]
	  in
	  Verbose.printf "Constraint:@.  %a@." Fpat.Formula.pr constraints;

          (* solve constraints and obtain coefficients of a ranking function *)
	  let newPredicateInfo _ =
	    try
	      let coefficientInfos = inferCoeffs arg_vars [linear_template] constraints in
	      (* return updated predicate *)
	      { predicate_info with coefficients = coefficientInfos @ predicate_info.coefficients; errorPaths = spc :: predicate_info.errorPaths }
            with Fpat.PolyConstrSolver.Unknown ->
	      Verbose.printf "Failed to solve the constraints...@.@.";

	      (* Failed to infer a new ranking predicate -> Update extra parameters *)
	      (** UPDATE [not implemented] **)

              raise FailedToFindLLRF (* failed to solve the constraints *)
	  in
	  let _ = Queue.push newPredicateInfo predicate_que in
	  run predicate_que holed
	else
	  (* all order constructed by <spc_1, spc_2, ..., spc_n> and newly obtained spc *)
	  let allSpcSequences =
	    let rec go l = function
	      | [] -> [l@[spc]]
	      | x::xs as r -> (l@[spc]@r) :: go (l@[x]) xs
	    in go [] predicate_info.errorPaths
	  in
	  let allSpcSequencesWithExparam =
	    let rec go l = function
	      | [] -> [l@[spcWithExparam]]
	      | x::xs as r -> (l@[spcWithExparam]@r) :: go (l@[x]) xs
	    in go [] predicate_info.errorPathsWithExparam
	  in
	  let numberOfSpcSequences = List.length allSpcSequences in
	  let allVars = List.map fst env in

	  let successes = (flip List.map) (List.combine allSpcSequences allSpcSequencesWithExparam) (fun (spcSequence, spcSequenceWithExparam) -> fun _ ->
	    (* make templates (for arguments and previous arguments) *)
	    let linearTemplates = Fpat.Util.List.unfold (fun i -> if i < numberOfSpcSequences then Some (unwrap_template (Fpat.Template.mk_atom arg_env 1), i+1) else None) 0 in
	    let prevLinearTemplates = List.map (Fpat.Term.subst (List.combine arg_vars prev_var_terms)) linearTemplates in
	    Fpat.Util.List.iteri (fun i lt -> Verbose.printf "Linear template(%d):@.  %a@." i Fpat.Term.pr lt) linearTemplates;
            try
	      (* make a constraint *)
	      let constraints = makeLexicographicConstraints allVars linearTemplates prevLinearTemplates spcSequence in
	      Verbose.printf "Constraint:@.  %a@." Fpat.Formula.pr constraints;

	      (* solve constraint and obtain coefficients *)
	      let coefficientInfos = inferCoeffs arg_vars linearTemplates constraints in

              (* return new predicate information (coeffcients + error paths) *)
	      let newPredicateInfo = { predicate_info with coefficients = coefficientInfos; errorPaths = spcSequence; errorPathsWithExparam = spcSequenceWithExparam} in
	      Verbose.printf "Found ranking function: %a@." pr_ranking_function newPredicateInfo;
	      newPredicateInfo
	    with
            | Fpat.PolyConstrSolver.NoSolution
            | Fpat.PolyConstrSolver.Unknown ->
	      Verbose.printf "Try to update extra parameters...@.@.";

	      try
		(* make a constraint *)
		let constraints = makeLexicographicConstraints allVars linearTemplates prevLinearTemplates spcSequenceWithExparam in
		Verbose.printf "Constraint:@.  %a@." Fpat.Formula.pr constraints;

		(* solve constraint and obtain coefficients *)
		let coefficientInfos, exparamInfo = inferCoeffsAndExparams arg_vars linearTemplates constraints in

		(* return new predicate information (coeffcients + error paths) *)
		let newPredicateInfo = { predicate_info with coefficients = coefficientInfos; coeffsMap = exparamInfo; errorPaths = spcSequence; errorPathsWithExparam = spcSequenceWithExparam } in
		Verbose.printf "Found ranking function: %a@." pr_ranking_function newPredicateInfo;
		newPredicateInfo
              with
		| Fpat.PolyConstrSolver.NoSolution ->
		  Verbose.printf "Failed to find LLRF...@.";
		  raise InferenceFailure (* failed to solve the constraints *)
		| e ->
		  Verbose.printf "error: %s@." (Printexc.to_string e);
		  raise InferenceFailure (* failed to solve the constraints *)
	  )
	  in
	  let _ = List.iter (fun pred -> Queue.push pred predicate_que) successes in
	  run predicate_que holed
