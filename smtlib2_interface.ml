open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

module S = CEGAR_syntax
module U = CEGAR_util

let parse_atom s len i =
  if len <= i then
    i, None
  else if s.[i] = '|' then
    try
      let j = String.index_from s (i+1) '|' in
      j+1, Some (String.sub s i (j-i+1))
    with Not_found -> invalid_arg "Smtlib2_interface.parse_atom"
  else
    let rec aux acc_rev s len i =
      let return () = Some (String.of_list @@ List.rev acc_rev) in
      if len <= i then
        i, !!return
      else
        match s.[i] with
        | c when Char.is_whitespace c -> i, !!return
        | ')' when acc_rev = [] -> i, None
        | ')' -> i, !!return
        | c -> aux (c::acc_rev) s len (i+1)
    in
    aux [] s len i

let parse_sexp s = Sexp.parse ~parse_atom s

let term_of_atom a =
  let open U.Term in
  match a with
  | "true" -> true_
  | "false" -> false_
  | _ ->
      try
        int (int_of_string a)
      with _ -> var a

let binop_of_atom a =
  let open U.Term in
  match a with
  | "=" -> S.make_eq_int
  | "<" -> (<)
  | ">" -> (>)
  | "<=" -> (<=)
  | ">=" -> (>=)
  | "+" -> (+)
  | "-" -> (-)
  | "*" -> ( * )
  | "div" -> ( / )
  | _ -> unsupported ("binop_of_atom "^a)

let rec term_of_sexp s =
  let open Sexp in
  match s with
  | A a -> term_of_atom a
  | S [A "not"; s'] -> S.make_not @@ term_of_sexp s'
  | S [A ("exists"|"forall" as s); S args; s'] ->
      let xs = List.map (function S [A x; _] -> S.Var x | _ -> invalid_arg "term_of_sexp") args in
      S.make_app (S.Var s) [S.make_app (S.Var "args") xs; term_of_sexp s']
  | S (A "and" :: ss) -> S.make_ands @@ List.map term_of_sexp ss
  | S (A "or" :: ss) -> S.make_ors @@ List.map term_of_sexp ss
  | S (A "+" :: s' :: ss) -> List.fold_left S.make_add (term_of_sexp s') @@ List.map term_of_sexp ss
  | S [A "-"; s] -> U.Term.(int 0 - term_of_sexp s)
  | S [A "let"; S defs; s'] ->
      let defs' = List.map (function S [A x; s] -> x, term_of_sexp s | _ -> invalid_arg "term_of_sexp") defs in
      U.subst_map defs' @@ term_of_sexp s'
  | S [A a; s1; s2] when a.[0] <> '|' -> binop_of_atom a (term_of_sexp s1) (term_of_sexp s2)
  | S (A a :: ss) when a.[0] = '|' -> S.make_app (term_of_atom a) @@ List.map term_of_sexp ss
  | _ ->
      Format.eprintf "%a@." print s;
      unsupported "Smtlib2_interface.term_of_sexp"

let type_of_atom a =
  match a with
  | "Int" -> CEGAR_type.typ_int
  | "Bool" -> !!CEGAR_type.typ_bool
  | _ -> unsupported "type_of_atom"

let parse_model str =
  let unsupported () = unsupported "Smtlib2_interface.parse_model" in
  let s = str in
  Debug.printf "[parse_model] INPUT: @[%a@." (List.print Sexp.print) s;
  let open Sexp in
  match s with
  | [A "unsat"; _] -> fatal "Recursive HCCS unsatisfiable?"
  | [A "sat"; S (A "model" :: sol)] ->
      let aux s =
        match s with
        | S (A "define-fun" :: A id :: S args :: A ty :: body :: []) ->
            let args =
              let aux s =
                match s with
                | S (A x::A ty::[]) -> x, type_of_atom ty
                | _ -> !!unsupported
              in
              List.map aux args
            in
            let body = term_of_sexp body in
            id, (args, body)
        | _ -> !!unsupported
      in
      List.map aux sol
  | _ -> !!unsupported
