open Ppxlib
open Ppx_util

let constrs =
  List.map
    (fun (s1, s2) -> (Lident s1, s2))
    [
      ("()", "unit");
      ("true", "true_");
      ("false", "false_");
      ("[]", "nil");
      (* unused *)
      ("::", "cons");
      (* unused *)
      ("None", "none");
      ("Some", "some");
    ]

let ids = List.map (fun s -> (Lident s, s)) [ "randi"; "randb"; "rand"; "eod"; "bool"; "string" ]

let funs =
  [
    "not";
    "&&";
    "ands";
    "||";
    "ors";
    "=>";
    "+";
    "-";
    "*";
    "/";
    "~-";
    "br";
    "|+|";
    "brs";
    "=";
    "<>";
    "<";
    ">";
    "<=";
    ">=";
    "<|";
    "|>";
    "fst";
    "snd";
    "ignore";
    "!";
    ":=";
    "ref";
    "seqs";
    "length";
  ]

let term_ident ~loc s = make_ident "Term" ~loc s
let _pat_ident ~loc s = make_ident "Pat" ~loc s

let find_typ_in_attr ~loc attr =
  try
    let attr = List.find (fun a -> a.attr_name.txt = "ty") attr in
    match attr.attr_payload with
    | PTyp ty -> Ppx_type.term_of_type ty
    | PStr [ { pstr_desc = Pstr_eval (e_ty, _); _ } ] -> e_ty
    | _ -> [%expr typ]
  with Not_found -> [%expr typ]

let rec term_of_pattern p =
  let loc = p.ppat_loc in
  match p with
  | [%pat? (_ : [%t? ty])] ->
      let ty = Ppx_type.term_of_type ty in
      [%expr Pat.__ [%e ty]]
  | [%pat? _] ->
      let ty = find_typ_in_attr ~loc p.ppat_attributes in
      [%expr Pat.__ [%e ty]]
  | { ppat_desc = Ppat_var x; _ } ->
      let x = id_of x in
      [%expr Pat.var [%e x]]
  | { ppat_desc = Ppat_tuple ps; _ } ->
      let ps = list_of ~loc @@ List.map term_of_pattern ps in
      [%expr Pat.tuple [%e ps]]
  | [%pat? []] ->
      let ty = find_typ_in_attr ~loc p.ppat_attributes in
      [%expr Pat.nil2 ~list_typ:[%e ty]]
  | [%pat? [%p? p1] :: [%p? p2]] ->
      let p1 = term_of_pattern p1 in
      let p2 = term_of_pattern p2 in
      [%expr Pat.cons [%e p1] [%e p2]]
  | [%pat? [%p? p1] | [%p? p2]] ->
      let p1 = term_of_pattern p1 in
      let p2 = term_of_pattern p2 in
      [%expr Pat.por [%e p1] [%e p2]]
  | { ppat_desc = Ppat_constant (Pconst_integer _ as c); _ } ->
      let n = Ast_helper.Exp.constant c in
      [%expr Pat.const (Term.int [%e n])]
  | { ppat_desc = Ppat_alias (p1, x); _ } ->
      let p1 = term_of_pattern p1 in
      let x = id_of x in
      [%expr Pat.alias [%e p1] [%e x]]
  | _ -> Location.raise_errorf ~loc "Unsupported syntax of %%term (pattern)"

class my_mapper =
  object (self)
    inherit Ast_traverse.map as _super

    method! expression e =
      let loc = e.pexp_loc in
      match e.pexp_desc with
      | Pexp_construct (constr, None) when constr.txt = Lident "[]" ->
          let ty = find_typ_in_attr ~loc e.pexp_attributes in
          [%expr Term.nil ~elem_typ:[%e ty]]
      | Pexp_construct (constr, arg) when constr.txt = Lident "::" -> (
          match arg with
          | Some
              { pexp_desc = Pexp_tuple [ e1; { pexp_desc = Pexp_construct (constr, None); _ } ]; _ }
            when constr.txt = Lident "[]" ->
              let e1 = self#expression e1 in
              [%expr Term.list [ [%e e1] ]]
          | Some { pexp_desc = Pexp_tuple [ e1; e2 ]; _ } ->
              let e1 = self#expression e1 in
              let e2 = self#expression e2 in
              [%expr Term.cons [%e e1] [%e e2]]
          | _ -> unsupported_term loc)
      | Pexp_construct (constr, arg) when List.mem_assoc constr.txt constrs -> (
          let constr = term_ident ~loc @@ List.assoc constr.txt constrs in
          match arg with
          | None -> constr
          | Some e ->
              let args =
                match e.pexp_desc with
                | Pexp_tuple es -> List.map (fun e -> (Nolabel, self#expression e)) es
                | _ -> [ (Nolabel, self#expression e) ]
              in
              Ast_helper.Exp.(apply constr args))
      | Pexp_assert { pexp_desc = Pexp_construct (constr, None); _ }
        when constr.txt = Lident "false" ->
          [%expr Term.fail]
      | _ when is_var e "bot" ->
          let ty = find_typ_in_attr ~loc e.pexp_attributes in
          [%expr Term.bot [%e ty]]
      | Pexp_ident id when List.mem_assoc id.txt ids -> term_ident ~loc @@ List.assoc id.txt ids
      | Pexp_constant (Pconst_integer (_, None)) -> [%expr Term.int [%e e]]
      | Pexp_ident _ -> [%expr Term.var [%e e]]
      | Pexp_let (_, [ { pvb_pat = { ppat_desc = Ppat_any; _ }; pvb_expr; _ } ], e2) ->
          let e1 = self#expression pvb_expr in
          let e2 = self#expression e2 in
          [%expr Term.seq [%e e1] [%e e2]]
      | Pexp_let (flag, bindings, e1) ->
          let bindings =
            let tr_pat { pvb_pat; pvb_expr; _ } =
              match pvb_pat.ppat_desc with
              | Ppat_var x -> [%expr [%e id_of x], [%e self#expression pvb_expr]]
              | _ -> unsupported_term loc
            in
            bindings |> List.map tr_pat |> list_of ~loc
          in
          let e1 = self#expression e1 in
          let make_lets =
            let lt = match flag with Nonrecursive -> "lets" | Recursive -> "let_" in
            term_ident ~loc lt
          in
          [%expr [%e make_lets] [%e bindings] [%e e1]]
      | Pexp_apply (e1, [ (Nolabel, e2) ]) when is_var e1 "raise" ->
          let ty = find_typ_in_attr ~loc e.pexp_attributes in
          let e2 = self#expression e2 in
          [%expr Term.raise ~typ:[%e ty] [%e e2]]
      | Pexp_apply (e1, [ (Nolabel, e2); (Nolabel, e3) ]) when is_var e1 "@" || is_var e1 "@@" ->
          let e2 = self#expression e2 in
          let e3 = self#expression e3 in
          [%expr Term.( @@ ) [%e e2] [%e e3]]
      | Pexp_apply (e1, [ (Nolabel, ({ pexp_desc = Pexp_ident _; _ } as e2)) ]) when is_var e1 "lid"
        ->
          [%expr Term.var_lid [%e e2]]
      | Pexp_apply (e1, [ (Nolabel, ({ pexp_desc = Pexp_ident _; _ } as e2)) ]) when is_var e1 "int"
        ->
          [%expr Term.int [%e e2]]
      | Pexp_apply (e1, [ (Nolabel, e2); arg3 ]) when is_var e1 "##" ->
          let arg2 = (Nolabel, self#expression e2) in
          let f = term_ident ~loc "proj" in
          Ast_helper.Exp.(apply f [ arg3; arg2 ])
      | Pexp_apply (e1, args) when List.exists (is_var e1) funs ->
          let args = List.map (fun (l, e) -> (l, self#expression e)) args in
          let s = List.find (is_var e1) funs in
          let f = term_ident ~loc s in
          Ast_helper.Exp.(apply f args)
      | Pexp_apply (e1, args) ->
          let e1 = self#expression e1 in
          let arg = list_of ~loc @@ List.map (fun (_, e) -> self#expression e) args in
          [%expr Term.( @@ ) [%e e1] [%e arg]]
      | Pexp_fun (Nolabel, None, arg, e1) ->
          let x =
            match arg.ppat_desc with
            | Ppat_var x -> Ast_helper.Exp.ident { x with txt = Lident x.txt }
            | _ -> unsupported_term loc
          in
          let e1 = self#expression e1 in
          [%expr Term.fun_ [%e x] [%e e1]]
      | Pexp_extension ({ txt = "e"; _ }, PStr [ { pstr_desc = Pstr_eval (e1, _); _ } ]) -> e1
      | Pexp_ifthenelse (e1, e2, e3) ->
          let e1 = self#expression e1 in
          let e2 = self#expression e2 in
          let e3 = match e3 with None -> [%expr Term.unit] | Some e3 -> self#expression e3 in
          [%expr Term.if_ [%e e1] [%e e2] [%e e3]]
      | Pexp_assert e1 ->
          let e1 = self#expression e1 in
          [%expr Term.assert_ [%e e1]]
      | Pexp_tuple es ->
          let arg = list_of ~loc @@ List.map self#expression es in
          [%expr Term.tuple [%e arg]]
      | Pexp_sequence
          ({ pexp_desc = Pexp_apply ({ pexp_desc = Pexp_ident id; _ }, [ (Nolabel, e1) ]); _ }, e2)
        when id.txt = Lident "assume" ->
          let e1 = self#expression e1 in
          let e2 = self#expression e2 in
          [%expr Term.assume [%e e1] [%e e2]]
      | Pexp_sequence (e1, e2) ->
          let e1 = self#expression e1 in
          let e2 = self#expression e2 in
          [%expr Term.seq [%e e1] [%e e2]]
      | Pexp_lazy e1 ->
          let e1 = self#expression e1 in
          [%expr Term.lazy_ [%e e1]]
      | Pexp_match (e1, cases) ->
          let e1 = self#expression e1 in
          let pats =
            let aux { pc_lhs; pc_guard; pc_rhs } =
              let p = term_of_pattern pc_lhs in
              let t = self#expression pc_rhs in
              let p =
                match pc_guard with
                | None -> p
                | Some cond ->
                    let cond = self#expression cond in
                    [%expr Pat.when_ [%e p] [%e cond]]
              in
              [%expr [%e p], [%e t]]
            in
            list_of ~loc @@ List.map aux cases
          in
          [%expr Term.match_ [%e e1] [%e pats]]
      | Pexp_variant (label, None) -> Ast_helper.Exp.(ident ~loc { txt = Lident label; loc })
      | _ ->
          (* Location.raise_errorf ~loc "e: %a@." Pprintast.expression e *)
          unsupported_term loc
  end

let mapper = new my_mapper

let expand ~ctxt (e : expression) =
  let _loc = Expansion_context.Extension.extension_point_loc ctxt in
  mapper#expression e

let extension =
  Extension.V3.declare "term" Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    expand

let rule = Context_free.Rule.extension extension
