open Util
open Mochi_util
open BRA_util
open Type
open Syntax
open Term_util
open BRA_types
open BRA_state

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

(***** Constants *****)

let hole_term = make_var (Id.new_var ~name:"__HOLE__" Ty.bool)
let stateType = ref []

(***** Functions *****)

(* apply a transformation throughout an AST in bottom-up manner *)
let rec everywhere_expr f {desc = desc; typ = typ} =
  let ev = everywhere_expr f in
  let expr =
    begin
      match desc with
	| App (func, args) -> App (ev func, List.map ev args)
	| If (cond_expr, then_expr, else_expr) -> If (ev cond_expr, ev then_expr, ev else_expr)
	| Local(Decl_let bindings, e) ->
	  let fmap (ident, body) = (ident, ev body) in
	  Local(Decl_let (List.map fmap bindings), ev e)
	| BinOp (op, e1, e2) -> BinOp (op, ev e1, ev e2)
	| Not e -> Not (ev e)
	| Fun (f, body) -> Fun (f, ev body)
	| Match (e, mclauses) -> Match (ev e, List.map (fun (p, t2) -> (p, ev t2)) mclauses)
	| e -> e
    end
  in f { desc = expr
       ; typ = typ
       ; attr = []}

(* conversion to parse-able string *)
let parens s = "(" ^ s ^ ")"
let rec show_typ t =
  let rec aux = function
    | TBase TUnit -> ["unit"]
    | TBase TBool -> ["bool"]
    | TBase TInt -> ["int"]
    | TFun ({Id.typ = t1}, t2) -> !stateType @ [show_typ t1] @ aux t2
    | _ -> []
  in
  let rec aux2 = function
    | [] -> ""
    | [x] -> x
    | x::xs -> x ^ " -> " ^ aux2 xs
  in
  parens (aux2 (aux t))

let place_signature = function
  | "" -> ""
  | signature -> " : " ^ signature

let modify_id v = if v.Id.name = "_" then "_" else Id.to_string ~plain:true v
let modify_id_typ v = if v.Id.name = "_" then "_" else parens (Id.to_string ~plain:true v ^ place_signature (show_typ (Id.typ v)))
let rec show_term ?(top=false) t = show_desc top t.desc
and show_desc top = function
  | End_of_definitions -> "()"
  | Const Unit -> "()"
  | Const True -> "true"
  | Const False -> "false"
  | Const (Int n) -> parens (string_of_int n)
  | App ({desc=Const(Rand(TBase TInt,_))}, _) -> "Random.int 0"
  | App ({desc=Var {Id.name = div}}, [n; m]) when div = "Pervasives./" -> parens (show_term n ^ " / " ^ show_term m)
  | Var v -> modify_id_typ v
  | Fun (f, body) -> "fun " ^ modify_id f ^ " -> " ^ show_term body
  | App ({desc=Event("fail", _)}, _) -> "assert false"
  | App (f, args) -> show_term f ^ List.fold_left (fun acc a -> acc ^ " " ^ parens (show_term a)) "" args
  | If (t1, t2, t3) -> "if " ^ show_term t1 ^ " then " ^ show_term t2 ^ " else " ^ show_term t3
  | Local(Decl_let [], _) -> assert false
  | Local(Decl_let (b::bs), t) ->
    let show_bind (x, body) =
      let args,body = decomp_funs body in
      modify_id x
      ^ (List.fold_left (fun acc a -> acc ^ " " ^ modify_id_typ a) "" args)
      ^ "="
      ^ show_term body in
    "let rec "
    ^ show_bind b
    ^ List.fold_left (fun acc x -> acc ^ " and " ^ show_bind x) "" bs
    ^ (if top then ";; " else " in ")
    ^ show_term ~top t
  | BinOp (binop, t1, t2) -> parens (show_term t1) ^ show_binop binop ^ parens (show_term t2)
  | Not t -> "not " ^ parens (show_term t)
  | t ->
      Format.eprintf "t: %a@." Print.desc t;
      raise (Invalid_argument "show_term")
and show_binop = function
  | Eq -> "="
  | Lt -> "<"
  | Gt -> ">"
  | Leq -> "<="
  | Geq -> ">="
  | And -> "&&"
  | Or -> "||"
  | Add -> "+"
  | Sub -> "-"
  | Mult -> "*"
  | Div -> "/"

let restore_ids =
  let trans_id ({Id.name = name_; Id.typ = typ} as orig) =
    try
      let i = String.rindex name_ '_' in
      let name = String.sub name_ 0 i in
      let id = int_of_string (String.sub name_ (i+1) (String.length name_ - i - 1)) in
      let attr = [] in
      Id.make id name attr typ
    with _ -> orig
  in
  let sub = function
    | {desc = Local(Decl_let bindings, cont); typ = t} ->
      {desc = Local(Decl_let (List.map (fun (f, body) -> (trans_id f, body)) bindings), cont); typ = t; attr=[]}
    | {desc = Fun (f, body); typ = t} -> {desc = Fun (trans_id f, body); typ = t; attr=[]}
    | {desc = Var v; typ = t} -> {desc = Var (trans_id v); typ = t; attr=[]}
    | t -> t
  in everywhere_expr sub

let retyping t type_of_state  =
  stateType := List.map show_typ type_of_state;
  Debug.printf "t: @[%a@." Print.term t;
  (* Format.eprintf "@.%s@." (show_term t); *)
  let lb = t |> show_term ~top:true
             |@> Debug.printf "show_term t: @[%s@."
             |> Lexing.from_string
  in
  let () = lb.Lexing.lex_curr_p <-
    {Lexing.pos_fname = Filename.basename !!Flag.Input.main;
     Lexing.pos_lnum = 1;
     Lexing.pos_cnum = 0;
     Lexing.pos_bol = 0};
  in
  let _,orig,_,decls = Parser_wrapper.parse_lexbuf lb in
  let parsed = List.fold_right Term.local decls Term.eod in
  Debug.printf "parsed from show_term t: @[%a@." Print.term parsed;
  let parsed = restore_ids parsed in
  Verbose.printf "transformed::@. @[%a@.@." Print.term parsed;
  (orig, parsed)

let extract_functions (target_program : term) =
  let ext acc (id, body) =
    let args,body = decomp_funs body in
    if args = [] then acc else {id=id; args=args}::acc
  in
  let rec iter t =
    match t.desc with
      | Local(Decl_let bindings, body) -> List.fold_left ext [] bindings @ iter body
      | t -> []
  in
  let extracted = iter target_program in
  List.filter (fun {id=id} -> Id.name id <> "main") extracted

let rec transform_function_definitions f term =
  let sub ((id, body) as binding) =
    let args,body = decomp_funs body in
    if args <> [] then f binding else binding
  in
  match term with
    | {desc = Local(Decl_let bindings, cont)} as t -> { t with desc = Local(Decl_let (List.map sub bindings), transform_function_definitions f cont) }
    | t -> t

let rec transform_main_expr f term =
  let sub ((id, body) as binding) =
    let args,body = decomp_funs body in
    if args = [] then (id, everywhere_expr f body) else binding
  in
  match term with
    | {desc = Local(Decl_let bindings, body)} as t -> { t with desc = Local(Decl_let (List.map sub bindings), transform_main_expr f body) }
    | t -> everywhere_expr f t

(*
[Example] f : int -> bool -> int
   randomized_application f (int -> bool -> int)
=> aux (f, [], int -> bool -> int)
=> aux (f, [(Random.int 0)], bool -> int)
=> aux (f, [(Random.int 0), (Random.int 0 = 0)], int)
=> f (Random.int 0) (Random.int 0 = 0)
*)
let randomized_application f t =
  let rec aux f args = function
    | t when is_base_typ t -> {desc = App (f, args); typ = t; attr=[]}
    | TFun ({Id.typ = t1}, t2) ->
        let r =
	  match t1 with
	  | TBase TUnit -> unit_term
	  | TBase TBool -> randbool_unit_term
	  | TBase TInt -> randint_unit_term
	  | _ -> assert false
        in
        aux f (args@[r]) t2
    | _ -> assert false
  in aux f [] t

let rec find_main_function = function
  | {desc = Local(Decl_let bindings, body)} ->
    let rec aux = function
      | [] -> find_main_function body
      | ({Id.name = "main"} as main_func , _) :: _ -> Some main_func
      | _ :: bs -> aux bs
    in aux bindings
  | _ -> None

let remove_unit_wraping = function
  | {desc = Local(Decl_let [{Id.name="u"}, t], {desc = Const Unit|End_of_definitions; typ = TBase TUnit})} -> t
  | t -> t

let rec lambda_lift t =
  let lift_binding (id, body) =
    let args,body = decomp_funs body in
    let (sub_bindings, body') , _ = Lift.lift' ~args body in
    List.map (fun (a, (b, c)) -> (a, make_funs b c)) sub_bindings @ [id, make_funs args body']
  in
  match t with
    | {desc = Local(Decl_let bindings, rest)} ->
      let next_bindings = BRA_util.concat_map lift_binding bindings in
      {t with desc = Local(Decl_let next_bindings, lambda_lift rest)}
    | _ -> t

(* regularization of program form *)
let rec regularization e =
  match find_main_function e with
    | Some ({Id.name = "main"} as f) ->
      let main_expr = randomized_application {desc = Var f; typ = Id.typ f; attr=[]} (Id.typ f) in
      let rec aux = function
	| {desc = Local(Decl_let bindings, rest)} as t -> {t with desc = Local(Decl_let bindings, aux rest)}
	| {desc = Const Unit} -> main_expr
	| {desc = End_of_definitions} -> main_expr
	| _ -> assert false
      in
      aux e
    | _ -> e

let extract_id = function
  | {desc = (Var v)} -> v
  | _ -> assert false

let implement_recieving ({program = program; state = state; verified = verified} as holed) =
  let passed = passed_statevars holed in
  let placeholders f = List.map (fun v -> Id.new_var ~name:"x_DO_NOT_CARE" (Id.typ (extract_id v))) (passed f) in (* (expl) placeholders 4 = " _ _ _ _ " *)
  let rec set_state f = function
    | [] -> []
    | [arg] -> (List.map extract_id (passed f))@[arg]
    | arg::args -> (placeholders f)@[arg]@(set_state f) args
  in
  { holed with program = transform_function_definitions (fun (id, body) -> let args,body = decomp_funs body in (id, make_funs (if !Flag.Termination.split_callsite && id = verified.id then args else set_state id args) body)) program }

let implement_transform_initial_application ({program = program; state = state} as holed) =
  let sub = function
    | {desc = App ({desc=Event("fail", _)}, _)}
    | {desc = App ({desc=Const(Rand(TBase TInt,_))}, _)} as t -> t
    | {desc = App (func, args)} as t -> {t with desc = App (func, concat_map (fun arg -> state.BRA_types.initial_state@[arg]) args)}
    | t -> t
  in
  { holed with program = transform_main_expr sub program }

let implement_propagation ({program = program; state = state; verified = verified} as holed) =
  let propagated = propagated_statevars holed in
  let sub = function
    | {desc = App ({desc=Event("fail", _)}, _)}
    | {desc = App ({desc=Const(Rand(TBase TInt,_))}, _)} as t -> t
    | {desc = App (func, args)} as t -> {t with desc = App (func, concat_map (fun arg -> propagated@[arg]) args)}
    | t -> t
  in
  { holed with program = transform_function_definitions (fun (id, body) -> let args,body = decomp_funs body in (id, make_funs args (if !Flag.Termination.split_callsite && id = verified.id then body else everywhere_expr sub body))) program }

let transform_program_by_call holed =
  holed |> implement_recieving
        |> implement_transform_initial_application
        |> implement_propagation

(* restore type *)
let restore_type state = function
  | {desc = Var v; typ = t} as e ->
    let rec restore_type' acc i = function
      | TFun ({Id.typ = t1}, t2) as t ->
	let fresh_id = Id.new_var ~name:("d_"^v.Id.name^(string_of_int i)) t1 in
	{ desc = Fun (fresh_id
			,(restore_type'
			    { desc = App (acc, (state.initial_state@[make_var fresh_id]))
			    ; typ = t
                            ; attr = []}
			    (i+1)
			    t2))
	; typ = t
        ; attr = []}
      | t -> acc
    in restore_type' e 0 t
  | _ -> raise (Invalid_argument "restore_type")

let to_holed_programs (target_program : term) =
  let defined_functions = extract_functions target_program in
  let state_template = build_state defined_functions in
  let no_checking_function = ref None in (** split-callsite **)
  let hole_insert target state typed =
    let sub (id, body) =
      let args,body = decomp_funs body in

      let id' = Id.new_var ~name:(Id.name id ^ "_without_checking") (Id.typ id) in (** split-callsite **)

      let prev_set_flag = get_prev_set_flag state target in
      let set_flag = get_set_flag state target in
      let update_flag = get_update_flag state target in
      let prev_statevars = get_prev_statevars state target in
      let statevars = get_statevars state target in
      let argvars = get_argvars state target in
      let add_update_statement cont prev_statevar statevar argvar =
	if !Flag.Termination.disjunctive then
              (* let s_x = if * then
                 x
                 else
                 s_prev_x *)
	  make_let [extract_id statevar, make_if update_flag (restore_type state argvar) prev_statevar] cont
	else
              (* let s_x = x *)
  	  make_let [extract_id statevar, restore_type state argvar] cont
      in
      let body' =
	if id = target.id then
	  if !Flag.Termination.disjunctive then
            (* let _ = if prev_set_flag then
                         if __HOLE__ then
                           ()
                         else
                           fail
               in *)
            make_let
	      [Id.new_var ~name:"_" Ty.unit, make_if prev_set_flag (make_if hole_term unit_term (make_app fail_term [unit_term])) unit_term]

              (* let update_flag = Random.int 0 = 0 in *)
	      (make_let
		 [(extract_id update_flag, randbool_unit_term)]

		 (* let set_flag = update_flag || prev_set_flag in *)
		 (make_let
		    [(extract_id set_flag, make_or update_flag prev_set_flag)]

		    (* each statevars update *)
		    (fold_left3 add_update_statement
		       body prev_statevars statevars argvars)))
	  else
            (* let _ = if prev_set_flag then
                         if __HOLE__ then
                           ()
                         else
                           fail
               in *)
            make_let
	      [Id.new_var ~name:"_" Ty.unit, make_if prev_set_flag (make_if hole_term unit_term (make_app fail_term [unit_term])) unit_term]

	      (* let set_flag = true in *)
	      (make_let
		 [(extract_id set_flag, true_term)]

		 (* each statevars update *)
		 (fold_left3 add_update_statement
		    body prev_statevars statevars argvars))
	else body
      in if id = target.id && !Flag.Termination.split_callsite then
	  let body_update =
	    (* let set_flag = true in *)
	    make_let
	      [(extract_id set_flag, true_term)]
	      (* each statevars update *)
	      (fold_left3 add_update_statement
		 body prev_statevars statevars argvars)
	  in

	  let placeholders () = List.map (fun v -> Id.new_var ~name:"x_DO_NOT_CARE" (Id.typ (extract_id v))) (prev_set_flag::prev_statevars) in
	  let rec set_state = function
	    | [] -> []
	    | [arg] -> (extract_id prev_set_flag)::(List.map extract_id prev_statevars)@[arg]
	    | arg::args -> (placeholders ())@[arg]@(set_state args)
	  in
	  let args' = set_state args
	  in

	  let app_assert =
	    make_let
	      [Id.new_var ~name:"_" Ty.unit, make_if prev_set_flag (make_if hole_term unit_term (make_app fail_term [unit_term])) unit_term]
	      {desc = App (make_var id', List.map make_var args'); typ = Id.typ id'; attr=[]}
	  in
	  (no_checking_function := Some ({id = id'; args = args} : function_info);
	   [(id, make_funs args' app_assert); (id', make_funs args body_update)])
	else
	  [(id, make_funs args body')]
    in

    { typed with desc = match typed.desc with
      | Local(Decl_let bindings, body) ->
	let bindings' = BRA_util.concat_map sub bindings in
	Local(Decl_let bindings', body)
      | t -> t
    }
  in
  let hole_inserted_programs =
    List.map (fun f ->
      let f_state = state_template f in
      { program = everywhere_expr (hole_insert f f_state) target_program
      ; verified = f
      ; verified_no_checking_ver = !no_checking_function
      ; state = f_state}) defined_functions
  in
  let state_inserted_programs =
    List.map transform_program_by_call hole_inserted_programs
  in state_inserted_programs

let callsite_split ({program = t; verified = {id = f}; verified_no_checking_ver = f_no_} as holed) =
  let f_no = match f_no_ with Some {id = x} -> x | None -> assert false in
  let counter = ref 0 in
  let replace_index = ref (-1) in
  let is_update = ref true in
  let aux_subst_each = function
    | {desc = Var v} as e when Id.(v = f) ->
      let v' = if !counter = !replace_index then (is_update := true; f) else f_no in
      begin
	counter := !counter + 1;
	{e with desc = Var v'}
      end
    | t -> t
  in
  let rec subst_each t =
      begin
	is_update := false;
	counter := 0;
	replace_index := !replace_index + 1;
	let holed' = {holed with program = everywhere_expr aux_subst_each t} in
	Verbose.printf "HOLED[%a -> %a]:%a@." Id.print f Id.print f_no Print.term holed'.program;
	Verbose.printf "is_update: %s@." (string_of_bool !is_update);
	Verbose.printf "counter: %s@." (string_of_int !counter);
	Verbose.printf "replace_index: %s@." (string_of_int !replace_index);
	if !is_update then
	  holed' :: subst_each t
	else
	  []
      end
  in subst_each t

let construct_LLRF {variables = variables_; prev_variables = prev_variables_; coefficients = coefficients_} =
  let variables = (make_int 1) :: (List.map make_var variables_) in
  let prev_variables = (make_int 1) :: (List.map make_var prev_variables_) in
  let coefficients = List.map (fun {coeffs = cs; constant = c} -> List.map make_int (c::cs)) coefficients_ in
  let rec rank cs vs = try List.fold_left2
			     (fun rk t1 t2 -> make_add rk (make_mul t1 t2))
			     (make_mul (List.hd cs) (List.hd vs))
			     (List.tl cs)
			     (List.tl vs)
    with Invalid_argument _ -> raise (Invalid_argument "construct_LLRF")
  in
  let rec iter aux = function
    | [r] ->
      (* r(prev_x) > r(x) && r(x) >= 0 *)
      aux (make_and (make_gt (r prev_variables) (r variables))
	     (make_geq (r variables) (make_int 0)))
    | r::rs ->
      let aux_next cond =
	if !Flag.Termination.disjunctive then
	  cond
	else
	  make_and (make_geq (r prev_variables) (r variables)) (aux cond)
      in
      (* r(prev_x) > r(x) && r(x) >= 0 || ... *)
      make_or
        (aux (make_and (make_gt (r prev_variables) (r variables))
		(make_geq (r variables) (make_int 0))))
	(iter aux_next rs)
    | [] -> false_term
  in
  iter (fun x -> x) (List.map rank coefficients)

let rec separate_to_CNF = function
  | {desc = BinOp (Or, {desc = BinOp (And, t1, t2)}, t3)} as t ->
    separate_to_CNF {t with desc = BinOp (Or, t1, t3)}
    @ separate_to_CNF {t with desc = BinOp (Or, t2, t3)}
  | {desc = BinOp (Or, t1, {desc = BinOp (And, t2, t3)})} as t ->
    separate_to_CNF {t with desc = BinOp (Or, t1, t2)}
    @ separate_to_CNF {t with desc = BinOp (Or, t1, t3)}
  | {desc = BinOp (And, t1, t2)} -> [t1; t2]
  | t -> [t]

(* plug holed program with predicate *)
let pluging (holed_program : holed_program) (predicate : term) =
  let hole2pred = function
    | {desc = Var {Id.name = "__HOLE__"}} -> predicate
    | t -> t
  in everywhere_expr hole2pred holed_program.program
