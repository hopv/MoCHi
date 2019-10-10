open Util
open FpatInterface
open CEGAR_syntax
open CEGAR_util

module F = Fpat

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let rec conv_formula' t =
  match t with
  | App(App(Var ("exists"|"forall" as q), args), t1) ->
      let args' =
        try
          match decomp_app args with
          | Var "args", ts -> List.map (fun t -> F.Idnt.make @@ Option.get @@ decomp_var t, F.Type.mk_int) ts
          | _ -> assert false
        with _ ->
          Format.eprintf "%a@." CEGAR_print.term t;
          invalid_arg "QE.conv_formula'"
      in
      let f = match q with "exists" -> F.Formula.exists | "forall" -> F.Formula.forall | _ -> assert false in
      f args' @@ conv_formula' t1
  | Const(c) ->
      F.Formula.of_term @@ F.Term.mk_const (conv_const c)
  | Var(x) ->
      F.Formula.of_term @@ F.Term.mk_var @@ conv_var x
  | App(t1, t2) -> F.Formula.of_term @@ F.Term.mk_app (F.Formula.term_of @@ conv_formula' t1) [F.Formula.term_of @@ conv_formula' t2]
  | Fun _ -> assert false
  | Let _ -> assert false

let rec used_as_bool x t =
  match decomp_app t with
  | Const (Or|And), [Var y; _]
  | Const (Or|And), [_; Var y] when x = y -> true
  | Const Not, [Var y] -> x = y
  | _, ts -> List.exists (used_as_bool x) ts

let rec alpha_rename t =
  match t with
  | App(App(Var ("exists"|"forall" as q), args), t1) ->
      let xs =
        try
          match decomp_app args with
          | Var "args", ts -> List.map (Option.get -| decomp_var) ts
          | _ -> assert false
        with _ ->
          Format.eprintf "%a@." CEGAR_print.term t;
          invalid_arg "QE.conv_formula'"
      in
      let xs' = List.map rename_id xs in
      let t1' = List.fold_right2 (fun x x' t -> Term.(x |-> var x') t) xs xs' @@ alpha_rename t1 in
      Term.(var q @ [var "args" @ vars xs'; t1'])
  | Const c -> Const c
  | Var x -> Var x
  | App(t1, t2) -> App(alpha_rename t1, alpha_rename t2)
  | Fun _ -> assert false
  | Let _ -> assert false

let rec eliminate_bool t =
  match t with
  | App(App(Var ("exists"|"forall" as q), args), t1) ->
      let xs =
        try
          match decomp_app args with
          | Var "args", ts -> List.map (Option.get -| decomp_var) ts
          | _ -> assert false
        with _ ->
          Format.eprintf "%a@." CEGAR_print.term t;
          invalid_arg "QE.conv_formula'"
      in
      let t1' = eliminate_bool t1 in
      let xs1,xs2 = List.partition (used_as_bool -$- t1') xs in
      let (|&) = if q = "exists" then Term.(||) else Term.(&&) in
      let aux x t = Term.((x |-> true_) t |& (x |-> false_) t) in
      let t1'' = List.fold_right aux xs1 t1' in
      if xs2 = [] then
        t1''
      else
        Term.(var q @ [var "args" @ vars xs; t1'])
  | Const c -> Const c
  | Var x -> Var x
  | App(t1, t2) -> App(eliminate_bool t1, eliminate_bool t2)
  | Fun _ -> assert false
  | Let _ -> assert false

let eliminate t =
  let of_formula phi =
    let open Fpat in
    let open Term in
    let open Z3 in
    let phi =
      phi
      |> CunFormula.elim_unit
      |> Formula.map_atom CunAtom.elim_beq_bneq
    in
    let tenv, phi =
      SimTypInfer.infer_formula [] phi
    in
    F.Z3Interface.of_formula phi tenv []
  in
  let fv = get_fv t in
  let map = List.map (Pair.add_right @@ String.replace_chars (function '!' -> "_bang_" | c -> String.of_char c)) fv in
  Debug.printf "  map: @[%a@." Print.(list (string * string)) map;
  t
  |@> Debug.printf "  BEFORE: @[%a@." CEGAR_print.term
  |> subst_map @@ List.map (fun (x,y) -> x, Var y) map
  |> alpha_rename
  |@> Debug.printf "  alpha_rename: @[%a@." CEGAR_print.term
  |> eliminate_bool
  |@> Debug.printf "  eliminate_bool: @[%a@." CEGAR_print.term
  |> conv_formula'
  |@> Debug.printf "  conv_foromula': @[%a@." F.Formula.pr
  |> of_formula
  |@> Debug.printf "  of_formula: @[%s@." -| Z3.Expr.to_string
  |> F.Z3Interface.qelim
  |@> Debug.printf "  qelim: @[%s@." -| Z3.Expr.to_string
  |> F.Z3Interface.formula_of
  |@> Debug.printf "  formula_of: @[%a@." F.Formula.pr
  |> inv_formula
  |> subst_map @@ List.map (fun (x,y) -> y, Var x) map
  |@> Debug.printf "  AFTER: @[%a@.@." CEGAR_print.term
