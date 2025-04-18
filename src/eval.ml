open! Util
open! Type
open! Syntax
open! Type_util
open! Term_util

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

(* MEMO
   - `rand[ty] ()` is treated as `make_rand_unit ty`
   - `dummy[ty]` is treated as `make_default_term ty`
   - Argument `gen` returns a generated value of counterexample (input of `trans`).
     For `gen ty b`, `ty` is the type of the generated value (used for eval_dummy),
     `b` represents whether it records the value or not
     (i.e., whether it calls record or not)
   - Argument `record` records the generated values of counterexample,
     (the result of `trans`)
*)

exception RaiseExcep of term
exception EventFail
exception ReachLimit
exception ReachBottom
exception StopTrans
exception CoerceAbstraction
exception ViolateSpec of string

type env = (id * term) list

let pp_env fm env = Format.fprintf fm "%a" Print.(list (id * __)) env

type attr_info += Env of env ref
type attr_info += FunInfo of string * id list

let () =
  update_pp_attr_info (fun fm info ->
      match info with
      | Env env ->
          Format.fprintf fm "Env %a" pp_env !env;
          true
      | FunInfo (name, xs) ->
          Format.fprintf fm "Fun(%s, %a)" name Print.(list id) xs;
          true
      | _ -> false)

let remove_ainfo t = Trans.map_attr (List.filter (function AInfo _ -> false | _ -> true)) t

let decomp_env t =
  let infos, t' = decomp_label ~label:"Env" t in
  let infos' = List.filter_map (function Env env -> Some env | _ -> None) infos in
  match infos' with [] -> (None, t') | [ env ] -> (Some env, t') | _ -> assert false

let assoc_env_opt = decomp_env |- fst
let assoc_env t = match assoc_env_opt t with None -> [] | Some env -> !env

let make_closure env t =
  match t.desc with
  | Fun _ ->
      let _, t' = decomp_env t in
      make_label ~label:"Env" (Env env) t'
  | _ -> t

(** Add information of function definition to its body for printing redexes *)
let add_fun_info f v =
  match decomp_funs v with
  | [], t -> t
  | xs, t ->
      let name = Id.name f in
      let t' = t |> make_label ~label:"fun_info" (FunInfo (name, xs)) in
      Term.(funs xs t') |> add_attrs v.attr

let decomp_fun_info t =
  match decomp_label ~label:"fun_info" t with
  | [ FunInfo (name, xs) ], t' -> Some (name, xs, t')
  | _ :: _, _ -> assert false
  | _ -> None

let has_fun_info t = Option.is_some @@ decomp_fun_info t
let make_violate_spec s = make_label ~label:"Violate" (String s) Term.unit

let assoc_violate_spec_opt t =
  t |> assoc_label ~label:"Violate" |> List.find_map_opt (function String s -> Some s | _ -> None)

let assoc_violate_spec = Option.get -| assoc_violate_spec_opt
let is_violate_spec t = assoc_violate_spec_opt t <> None

let rec eval_symbolic_gen rand env t =
  let ev = eval_symbolic_gen rand env in
  match t.desc with
  | Var (LId x) -> Id.List.assoc x env
  | Const _ -> t
  | _ when is_rand_unit t -> rand t.typ
  | If _ -> [%unsupported]
  | BinOp (And, _t1, _t2) -> [%unsupported]
  | BinOp (Or, _t1, _t2) -> [%unsupported]
  | BinOp (op, t1, t2) -> make_binop op (ev t1) (ev t2)
  | Local _ -> [%unsupported]
  | Fun _ -> t
  | _ -> [%unsupported]

let need_paren t =
  match t.desc with
  | Const (Int n) when n < 0 -> true
  | Constr (_, _, _ :: _) -> true
  | Tuple _ -> true
  | _ -> false

let rec print_value fm t =
  let b = need_paren t in
  if b then Format.fprintf fm "(";
  (match t.desc with
  | Const (Int n) when n < 0 -> Format.fprintf fm "(%d)" n (* ??? *)
  | Fun _ -> (
      let xs, t' = decomp_funs t in
      match decomp_fun_info t' with
      | None -> Format.pp_print_string fm "<fun>"
      | Some (name, ys, _) ->
          let env = assoc_env t in
          let l_xs = List.length xs in
          let l_ys = List.length ys in
          if l_xs = l_ys then Format.fprintf fm "%s" name
          else
            let vs = ys |> List.take (l_ys - l_xs) |> List.map (Id.List.assoc -$- env) in
            Format.fprintf fm "(%s %a)" name (print_list print_value " ") vs)
  | Cons _ -> Format.fprintf fm "%a" (List.print print_value) @@ list_of_term t
  | Tuple [ t_1; t_2 ] -> Format.fprintf fm "@[@[%a@],@ @[%a@]@]" print_value t_1 print_value t_2
  | _ -> Print.term fm t);
  if b then Format.fprintf fm ")"

and eval_bindings ev env bindings : env =
  let bindings' =
    bindings |> List.map (Pair.map_snd ev) |> List.map (fun (f, v) -> (f, add_fun_info f v))
  in
  let env' = bindings' @ env in
  List.iter (fun (_, v) -> assoc_env_opt v |> Option.iter (fun env -> env := env')) bindings';
  env'

and eval_dummy limit record env t =
  let gen ty _ = make_default_term ty |@> record in
  eval_print None limit gen record env t

and check_match ev v p =
  let open Option in
  let ch = check_match ev in
  let init = Some Fun.id in
  match (v.desc, p.pat_desc) with
  | _, PAny -> init
  | _, PVar x -> Some (subst x v)
  | _, PConst v' -> if v = v' then init else None
  | _, PAlias (p, x) ->
      let* f = ch v p in
      Some (f -| subst x v)
  | Constr (b, s, vs), PConstr (b', s', ps) ->
      if s <> s' || b <> b' then None
      else
        List.L.fold_left2 vs ps ~init ~f:(fun bnd v p ->
            let* f = bnd in
            let* f' = ch v p in
            Some (f -| f'))
  | Nil, PNil -> init
  | Cons (v1, v2), PCons (p1, p2) ->
      let* f1 = ch v1 p1 in
      let* f2 = ch v2 p2 in
      Some (f1 -| f2)
  | Nil, PCons _ -> None
  | Cons _, PNil -> None
  | Tuple vs, PTuple ps ->
      List.map2 ch vs ps
      |> List.L.fold_right ~init ~f:(fun r1 r2 ->
             let* f1 = r1 in
             let* f2 = r2 in
             Some (f1 -| f2))
  | Record _, PRecord _ -> [%unsupported]
  | _, POr (p1, p2) -> ( match ch v p1 with None -> ch v p2 | Some f -> Some f)
  | _, PWhen (p, cond) ->
      let* f = ch v p in
      let v = ev @@ f cond in
      if bool_of_term v then Some f else None
  | _ ->
      Format.eprintf "@.v: %a@." Print.term v;
      Format.eprintf "p: %a@." Print.pattern p;
      assert false

and process_replaced limit env record t' v =
  if is_base_typ v.typ then (
    let acc_rev = ref [] in
    let rand ty _ =
      let x = Id.new_var ~name:"r" ty in
      acc_rev := x :: !acc_rev;
      make_var x
    in
    let t'' = eval_print None limit rand ignore env t' in
    let xs = List.rev !acc_rev in
    Dbg.printf "  [trans] t'': %a@." Print.term t';
    Dbg.printf "  [trans] v: %a@." Print.term v;
    Dbg.printf "  [trans] constr: %a@." Print.term Term.(t'' = v);
    let sol = SMT.get_solution ~fv:xs Term.(t'' = v) in
    Dbg.printf "  [trans] sol: %a@." Print.(list (id * term)) sol;
    List.iter (fun x -> Id.List.assoc x sol |> record) xs)
  else record v

and eval_print fm limit gen record ?hook env t : term =
  (* Debug information *)
  let b =
    !!Dbg.check
    && ((not (is_value t)) || Is._Var t)
    &&
    match t.desc with
    | Local (Decl_let defs, _) -> List.exists (not -| is_value -| snd) defs
    | _ -> true
  in
  if b then (
    Dbg.printf "  [eval] t: %a@." Print.term t;
    Dbg.printf "  [eval] Dom(env): %a@.@." Print.(list id) (List.map fst env));

  (* Misc *)
  (match limit with
  | None -> ()
  | Some (n, cnt) ->
      incr cnt;
      if !cnt > n then raise ReachLimit);
  let info = assoc_info t in
  Option.iter (fun f -> f t) hook;

  (* Update [env] for removed bindings *)
  let env =
    if fm = None then
      List.L.fold_left info ~init:env ~f:(fun env info ->
          match info with
          | Trans.Removed bindings -> eval_bindings (eval_dummy limit record env) env bindings
          | _ -> env)
    else env
  in

  (* Update [gen] for counterexample translation *)
  let inserted = List.filter_map (function Trans.Inserted s -> Some s | _ -> None) info in
  let replaced = List.filter_map (function Trans.Replaced t -> Some t | _ -> None) info in
  let gen =
    if replaced <> [] || inserted <> [] then
      (* If the target is a replaced term, we do not record the generated terms,
         i.e., the argument of [gen] is false, for translating counterexample *)
      let gen ty _ = gen ty false in
      gen
    else gen
  in

  (* MAIN *)
  let ev ?(env = env) t = eval_print fm limit gen record ?hook env t in
  let run () =
    match t.desc with
    | _ when is_rand_unit t -> gen t.typ true
    | Const (Rand (Type.TBase Type.TInt, true)) -> assert false
    | Const (Rand (_typ, _)) ->
        Format.eprintf "%a@." Print.term t;
        [%unsupported]
    | Const _ -> t
    | End_of_definitions -> t
    | Var y when is_length_var y -> t
    | Var (LId x) -> (
        match Id.List.assoc_opt x env with
        | None -> unsupported "error trace with external funcitons (%a)" Print.term t
        | Some term -> term
        | exception _ -> assert false)
    | Fun _ -> make_closure (ref env) t
    | App (t1, ts) ->
        List.fold_right (fun t acc -> ev t :: acc) (t1 :: ts) []
        |> List.reduce_left (fun hd arg ->
               match hd.desc with
               | Var len when is_length_var len ->
                   make_int @@ List.length @@ Option.get @@ decomp_list arg
               | Fun (x, t2) ->
                   let env = (x, arg) :: assoc_env hd in
                   ev ~env t2
               | _ -> assert false)
    | If (t1, t2, t3) ->
        let v = ev t1 in
        let b = bool_of_term v in
        Option.iter (fun fm -> Format.fprintf fm "@\nif %b then ... -->" b) fm;
        ev (if b then t2 else t3)
    | Local (Decl_type _, t2) -> ev t2
    | Local (Decl_let bindings, t2) ->
        let env = eval_bindings ev env bindings in
        ev ~env t2
    | BinOp (And, t1, t2) ->
        let v1 = ev t1 in
        if bool_of_term v1 then ev t2 else false_term
    | BinOp (Or, t1, t2) ->
        let v1 = ev t1 in
        if bool_of_term v1 then true_term else ev t2
    | BinOp (Eq, t1, t2) when t1.typ = Ty.bool ->
        let v1 = ev t1 in
        let v2 = ev t2 in
        Term.bool (v1.desc = v2.desc)
    | BinOp (op, t1, t2) -> (
        let v2 = ev t2 in
        let v1 = ev t1 in
        match (int_of_term v1, int_of_term v2) with
        | n1, n2 -> (
            match op with
            | Eq -> make_bool (n1 = n2)
            | Lt -> make_bool (n1 < n2)
            | Gt -> make_bool (n1 > n2)
            | Leq -> make_bool (n1 <= n2)
            | Geq -> make_bool (n1 >= n2)
            | Add -> make_int (n1 + n2)
            | Sub -> make_int (n1 - n2)
            | Mult -> make_int (n1 * n2)
            | Div -> make_int (n1 / n2)
            | _ -> assert false)
        | exception Invalid_argument _
        (* for symbolic execution in process_replaced;
           v1 and v2 may be arithmetic expressions with variables *) ->
            if has_fun v1 || has_fun v2 then [%unsupported] else Term.(v1 <| op |> v2))
    | Not t1 ->
        let v1 = ev t1 in
        make_bool @@ not @@ bool_of_term v1
    | Event ("fail", false) -> raise EventFail
    | Event _ -> assert false
    | Record _fields -> failwith "Not implemented: eval_print Record"
    | Field _ -> failwith "Not implemented: eval_print Record"
    | SetField _ -> failwith "Not implemented: eval_print Record"
    | Nil -> t
    | Cons (t1, t2) ->
        let v2 = ev t2 in
        let v1 = ev t1 in
        make_cons v1 v2
    | Constr (b, s, ts) ->
        let vs = List.fold_right (fun t acc -> ev t :: acc) ts [] in
        make (Constr (b, s, vs)) t.typ
    | Match (t1, pats) ->
        let v = ev t1 in
        pats |> List.find_map (fun (p, t) -> check_match ev v p |> Option.map (fun f -> ev @@ f t))
    | Raise t ->
        let v = ev t in
        Option.iter (fun fm -> Format.fprintf fm "@\nraise %a" print_value v) fm;
        raise (RaiseExcep v)
    | TryWith (t1, t2) -> ( try ev t1 with RaiseExcep e -> ev @@ make_app t2 [ e ])
    | Tuple ts -> ts |> List.fold_right (fun t acc -> ev t :: acc) -$- [] |> Term.tuple
    | Proj (i, t) ->
        let v = ev t in
        List.nth (tuple_of_term v) i
    | Bottom -> raise ReachBottom
    | _ -> unsupported "Eval (%a)" Print.desc_constr t.desc
  in
  match decomp_fun_info t with
  | Some (name, xs, t') -> (
      let args = List.map (Id.List.assoc -$- env) xs in
      Option.iter
        (fun fm -> Format.fprintf fm "@\n@[<v 2>%s %a -->" name (print_list print_value " ") args)
        fm;
      match ev t' with
      | v ->
          Option.iter (fun fm -> Format.fprintf fm "@\n%a@]" print_value v) fm;
          v
      | exception e ->
          Option.iter (fun fm -> Format.fprintf fm "@]") fm;
          raise e)
  | None -> (
      match run () with
      | exception EventFail when inserted <> [] ->
          let s =
            match inserted with [ s ] -> s | _ :: _ -> [%unsupported] | [] -> assert false
          in
          record (make_violate_spec s);
          raise StopTrans
      | v ->
          if b then Dbg.printf "  [eval] v: %a@." print_value v;
          (if fm = None then
             match replaced with
             | [ t' ] ->
                 Dbg.printf "  [trans] @[@[%a@] -->*@ @[%a@] |->@ @[%a@." Print.term t Print.term v
                   Print.term t';
                 process_replaced limit env record t' v
             | _ :: _ -> [%unsupported]
             | [] -> ());
          v)

let eval_print ?fm ?limit gen record ?hook t =
  let limit' = Option.map (fun x -> (x, ref 0)) limit in
  ignore @@ eval_print fm limit' gen record ?hook [] t

let make_gen ?(record = ignore) ce : term list ref * (typ -> bool -> term) =
  let r = ref ce in
  ( r,
    fun _ acc ->
      match !r with
      | [] when !!Dbg.check -> assert false
      | [] -> [%unsupported]
      | [ t ] when is_violate_spec t -> raise (ViolateSpec (assoc_violate_spec t))
      | n :: ce' ->
          Dbg.printf "  GEN: %a@." Print.term n;
          r := ce';
          if acc then record n;
          n )

let print fm (ce, { Problem.term }) =
  let _, gen = make_gen ce in
  Dbg.printf "  CE: %a@." Print.(list term) ce;
  try
    eval_print ~fm gen ignore term;
    if !Flag.Abstract.over_approx <> [] then raise CoerceAbstraction;
    [%unsupported]
  with
  | RaiseExcep _ -> Format.fprintf fm "@\nUNCAUGHT EXCEPTION OCCUR!@\n"
  | EventFail -> Format.fprintf fm "@\nFAIL!@\n"
  | CoerceAbstraction ->
      Format.fprintf fm "@\nThis is not a counterexample@\nDisable abstraction options@\n"
  | Unsupported s -> Format.fprintf !Flag.Print.target "@\nUnsupported: %s@\n" s
  | ViolateSpec s -> Format.fprintf fm "@\nViolation of spec.: %s@\n" s

let trans ce { Problem.term } =
  Dbg.printf "##TRANS@.";
  Dbg.printf "  [trans] ce: %a@." Print.(list term) ce;
  Dbg.printf "  [trans] term: %a@." Print.term term;
  let acc_rev = ref [] in
  let record (r : term) =
    Dbg.printf "  ADD: %a@." Print.term r;
    acc_rev := r :: !acc_rev
  in
  let r, gen = make_gen ~record ce in
  Dbg.printf "  CE: %a@." Print.(list term) ce;
  (try
     eval_print gen record term;
     if !Flag.Abstract.over_approx <> [] then raise CoerceAbstraction;
     assert false
   with RaiseExcep _ | EventFail | StopTrans -> assert (!r = []));
  List.rev !acc_rev |@> Dbg.printf "  [trans] ce': %a@." Print.(list term)

let eval ce ?hook { Problem.term } =
  Dbg.printf "##EVAL@.";
  Dbg.printf "  [eval] term: %a@." Print.term term;
  Dbg.printf "  [eval] ce: %a@." Print.(list term) ce;
  let r, gen = make_gen ce in
  try
    eval_print gen ignore ?hook term;
    if !Flag.Abstract.over_approx <> [] then raise CoerceAbstraction;
    Dbg.printf "  [eval] r: %a@." Print.(list term) !r;
    [%unsupported]
  with
  | RaiseExcep _ -> ()
  | EventFail -> ()
  | CoerceAbstraction -> [%unsupported]
  | Unsupported _ -> [%unsupported]
  | ViolateSpec _ -> ()
