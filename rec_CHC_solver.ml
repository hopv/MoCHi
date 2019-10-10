open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

module F = Fpat

exception TimeOut
exception SolverAborted

let solve_file filename =
  let cmd =
    let open Flag.Refine in
    match !solver with
    | Hoice -> !hoice
    | Z3 -> !z3
    | Z3_spacer -> !z3_spacer
  in
  let sol = Filename.change_extension filename "sol" in
  let cmd' = Format.sprintf "(ulimit -t %d; %s %s > %s)" !Flag.Refine.solver_timelimit cmd filename sol in
  let r = Sys.command cmd' in
  if r = 128+9 then raise TimeOut;
  let s = IO.input_file sol in
  if r <> 0 || s = "" then raise SolverAborted;
  Smtlib2_interface.parse_sexp s
  |@> Debug.printf "PARSED: %a@." (List.print Sexp.print)

let print_sol = Print.(list (string * (list (string * CEGAR_print.typ) * CEGAR_print.term)))

let preprocess_rec_hccs ?(for_debug=false) hcs =
  let map =
    let rename x =
      x
      |> (if for_debug then Fun.id else F.Idnt.reset_uid)
      |> Format.asprintf "|%a|" F.Idnt.pr
      |> F.Idnt.make
    in
    F.HCCS.tenv hcs
    |> List.map fst
    |> List.map (Pair.add_right rename)
  in
  let rev_map = List.map (fun (x,y) -> F.Idnt.string_of y, x) map in
  let filename =
    let ext =
      let ext = "smt2" in
      let ext = if for_debug then "orig." ^ ext else ext in
      let ext = if !!Debug.check then string_of_int !Flag.Log.cegar_loop ^ "." ^ ext else ext in
      ext
    in
    Filename.change_extension !!Flag.Input.main ext in
  hcs
  |> F.HCCS.rename map
  |@> Debug.printf "HCCS: %a@." F.HCCS.pr
  |> F.HCCS.save_smtlib2 filename;
  rev_map, filename

let rec subst_map' map t =
  let open CEGAR_syntax in
  match t with
  | Const c -> Const c
  | Var x when List.mem_assoc x map -> List.assoc x map
  | Var x -> Var x
  | App _ ->
      let t1,ts = CEGAR_syntax.decomp_app t in
      let map' =
        match t1,ts with
        | CEGAR_syntax.Var ("exists"|"forall"), [args; _] ->
            let xs =
              match CEGAR_syntax.decomp_app args with
              | Var "args", xs -> List.map (Option.get -| CEGAR_syntax.decomp_var) xs
              | _ -> assert false
            in
            let map' =
              if List.Set.disjoint xs (List.flatten_map (get_fv -| snd) map) then
                []
              else
                List.map (fun x -> let x' = rename_id x in x, Var x') xs
            in
            map' @ List.filter_out (fst |- List.mem -$- xs) map
        | _ -> map
      in
      make_app (subst_map' map' t1) (List.map (subst_map' map') ts)
  | Let _ -> assert false
  | Fun _ -> assert false

let unfold sol =
  let sol' = Hashtbl.create @@ List.length sol in
  List.iter (Fun.uncurry @@ Hashtbl.add sol') sol;
  let rec aux t =
    match CEGAR_syntax.decomp_app t with
    | _, [] -> t
    | CEGAR_syntax.Var ("exists"|"forall" as s), [args; t] -> CEGAR_syntax.make_app (CEGAR_syntax.Var s) [args; aux t]
    | CEGAR_syntax.Var f, ts ->
        let args,t' = Hashtbl.find sol' f in
        let xs = List.map fst args in
        let ts' = List.map aux ts in
        let t'' = update f args t' in
        subst_map' (List.combine xs ts') t''
    | t1, ts -> CEGAR_syntax.make_app t1 (List.map aux ts)
  and update f args t =
    let t' = aux t in
    Hashtbl.replace sol' f (args,t');
    t'
  in
  Hashtbl.iter (fun f (args,t) -> ignore @@ update f args t) sol';
  Hashtbl.fold (fun f (xs,t) acc -> (f,(xs,t))::acc) sol' []

let approximate (args, t) =
  let rest = List.Set.diff (CEGAR_syntax.get_fv t) (List.map fst args) in
  let t' =
    if rest <> [] then
      let open CEGAR_syntax in
      let rec approx t =
        match decomp_app t with
        | Const And, _ ->
            decomp_ands t
            |> List.map approx
            |> List.filter (get_fv |- List.Set.disjoint rest)
            |> make_ands
        | Const Or, _ ->
            decomp_ors t
            |> List.map approx
            |> List.filter (get_fv |- List.Set.disjoint rest)
            |> make_ors
        | _ -> t
      in
      let t' = approx t in
      warning "QE fails. Some approximation is used.";
      Debug.printf "[approx.] t: %a@." CEGAR_print.term t;
      Debug.printf "[approx.] fv: %a@." Print.(list string) (CEGAR_syntax.get_fv t);
      Debug.printf "[approx.] args: %a@." Print.(list string) (List.map fst args);
      Debug.printf "[approx.] t': %a@." CEGAR_print.term t';
      t'
    else
      t
  in
  args, t'

let solve hcs =
  let to_pred = Pair.map (List.map (Pair.map F.Idnt.make FpatInterface.conv_typ)) FpatInterface.conv_formula in
  let rev_map,filename = preprocess_rec_hccs hcs in
  if !!Debug.check then ignore (preprocess_rec_hccs ~for_debug:true hcs);
  solve_file filename
  |> Smtlib2_interface.parse_model
  |@> Debug.printf "Sol: %a@." print_sol
  |> unfold
  |@> Debug.printf "Unfold: %a@." print_sol
  |> List.map (Pair.map_snd @@ Pair.map_snd QE.eliminate)
  |@> Debug.printf "QEed: %a@." print_sol
  |> List.map (Pair.map_snd approximate)
  |@> Debug.printf "Approximated: %a@." print_sol
  |> List.map (Pair.map (fun f -> List.assoc f rev_map) to_pred)

let check_sat hcs =
  let _,filename = preprocess_rec_hccs hcs in
  match solve_file filename with
  | [Sexp.A "sat"; _] -> true
  | _ -> false
