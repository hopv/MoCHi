open! Util
open! Type
open! Syntax
open! Type_util
open! Term_util
module SMTLIB = Smtlib_utils.V_2_6
module Ast = SMTLIB.Ast

type formula = Syntax.term
and literal = FPred of var * term list | Exp of term
and term = Ast.term
and var = string
and chc = { body : body; head : head }
and body = literal list
and head = Bottom | HPred of var * term list
and cnf = term list list
and prog = def list * main list
and def = var * var list * literal list list
and main = literal list

let pp_var = Format.pp_print_string

let pp_literal fm lit =
  match lit with FPred (p, ts) -> Ast.pp_term fm (Ast.App (p, ts)) | Exp t -> Ast.pp_term fm t

let of_ty (ty : Ast.ty) =
  match ty with
  | Ty_bool -> Ty.bool
  | Ty_app ("Int", []) -> Ty.int
  | _ -> unsupported "%s(%a)" __FUNCTION__ Ast.pp_ty ty

let of_var x ty = Id.make x (of_ty ty)
let of_env env = List.map (Fun.uncurry of_var) env

let of_arith_op (op : Ast.arith_op) : Syntax.binop =
  match op with
  | Leq -> Leq
  | Lt -> Lt
  | Geq -> Geq
  | Gt -> Gt
  | Add -> Add
  | Minus -> Sub
  | Mult -> Mult
  | Div -> Div

let add_decl ({ fun_name; fun_args; fun_ret; fun_ty_vars } : Ast.ty Ast.fun_decl) env =
  assert (fun_ty_vars = []);
  (fun_name, Ty.funs (List.map of_ty fun_args) (of_ty fun_ret)) :: env

let add_binds binds env = List.map (Pair.map_snd of_ty) binds @@@ env

let rec of_term env (t : Ast.term) : Syntax.term =
  let of_terms = List.map (of_term env) in
  match t with
  | True -> [%term true]
  | False -> [%term false]
  | Const x -> (
      try Term.var (Id.make x (List.assoc x env))
      with Not_found -> (
        try Term.int (int_of_string x)
        with Invalid_argument _ ->
          Format.eprintf "x: %s@." x;
          assert false))
  | Arith (op, ts) -> (
      match (of_arith_op op, of_terms ts) with
      | op, [ t1; t2 ] -> Term.(t1 <| op |> t2)
      | Sub, [ t1 ] -> Term.(int 0 - t1)
      | _ -> unsupported "%s(%a)" __FUNCTION__ Ast.pp_term t)
  | App (f, ts) ->
      let f = Id.make f (List.assoc f env) in
      let ts = of_terms ts in
      [%term f @ `ts]
  | Eq (t1, t2) -> Term.(of_term env t1 = of_term env t2)
  | Imply (t1, t2) -> Term.(of_term env t1 => of_term env t2)
  | And ts -> Term.ands (of_terms ts)
  | Or ts -> Term.ors (of_terms ts)
  | Not t -> Term.not (of_term env t)
  | Forall (binds, t) ->
      let env' = add_binds binds env in
      Term.forall (of_env binds) (of_term env' t)
  | Exists (binds, t) ->
      let env' = add_binds binds env in
      Term.exists (of_env binds) (of_term env' t)
  | _ -> unsupported "%s(%a)" __FUNCTION__ Ast.pp_term t

let formula_of_statements (stmts : Ast.statement list) : Syntax.term =
  let init = (`Init, []) in
  let r, _ =
    List.L.fold_left stmts ~init ~f:(fun (acc, env) { Ast.stmt; _ } ->
        match (stmt, acc) with
        | Ast.Stmt_set_logic "HORN", _ -> (acc, env)
        | Ast.Stmt_set_logic s, _ -> unsupported "Logic: %s" s
        | Ast.Stmt_set_info (_, _), _ -> (acc, env)
        | Ast.Stmt_set_option _, _ -> (acc, env)
        | Ast.Stmt_decl_sort (_, _), _ -> (acc, env)
        | Ast.Stmt_decl decl, _ -> (acc, add_decl decl env)
        | Ast.Stmt_fun_def _, _ -> (acc, env)
        | Ast.Stmt_fun_rec _, _ -> (acc, env)
        | Ast.Stmt_funs_rec _, _ -> (acc, env)
        | Ast.Stmt_data _, _ -> (acc, env)
        | Ast.Stmt_assert t, `Assert t' -> (`Assert Term.(of_term env t && t'), env)
        | Ast.Stmt_assert t, `Init -> (`Assert (of_term env t), env)
        | Ast.Stmt_assert _, _ -> unsupported "%s" __FUNCTION__
        | Ast.Stmt_get_assertions, _ -> (acc, env)
        | Ast.Stmt_get_assignment, _ -> (acc, env)
        | Ast.Stmt_get_info _, _ -> (acc, env)
        | Ast.Stmt_get_model, _ -> (acc, env)
        | Ast.Stmt_get_option _, _ -> (acc, env)
        | Ast.Stmt_get_proof, _ -> (acc, env)
        | Ast.Stmt_get_unsat_assumptions, _ -> (acc, env)
        | Ast.Stmt_get_unsat_core, _ -> (acc, env)
        | Ast.Stmt_get_value _, _ -> unsupported "%s" __FUNCTION__
        | Ast.Stmt_check_sat, `Assert t -> (`Check_sat t, env)
        | Ast.Stmt_check_sat, _ -> unsupported "%s" __FUNCTION__
        | Ast.Stmt_check_sat_assuming _, _ -> unsupported "%s" __FUNCTION__
        | Ast.Stmt_pop _, _ -> (acc, env)
        | Ast.Stmt_push _, _ -> (acc, env)
        | Ast.Stmt_reset, _ -> unsupported "%s" __FUNCTION__
        | Ast.Stmt_reset_assertions, _ -> unsupported "%s" __FUNCTION__
        | Ast.Stmt_exit, `Check_sat fs -> (`Exit fs, env)
        | Ast.Stmt_exit, _ -> unsupported "%s" __FUNCTION__)
  in
  match r with
  | `Check_sat t | `Exit t -> t
  | `Init -> unsupported "%s" __FUNCTION__
  | `Assert _ -> unsupported "%s" __FUNCTION__

let read filename =
  let@ cin = IO.CPS.open_in filename in
  cin |> SMTLIB.parse_chan_exn |> formula_of_statements
