open Util
open Combinator
open SMTProver

(** Interface to CVC3 *)

(** unit is encoded as 0 *)
(* CVC3 2.2 does not allow forall quantification over boolean variables *)
(* POP does not undefine variables
   e.g., "PUSH; x:INT; POP; x:BOOLEAN" causes an error *)
(* For integer theory, CVC3 partially supports nonlinear expressions and quantifiers
   quantifiers are handled completely?
   on failure, use bitblasting *)
(* bvmult does not seem to support 2's complement negative numbers *)

let cvc3in = ref stdin
let cvc3out = ref stdout
let cvc3err = ref stdin

(** A unique id of next query to CVC3
    This is necessary to avoid a redefinition of a variable when we
    use the interactive mode of CVC3 *)
let cnt = ref 0
let deco s = "cnt" ^ string_of_int !cnt ^ "_" ^ s

(** @todo some version of CVC3 only support "+int" *)
let interactive = "+interactive"

let send_cmd cmd =
  let fm = Format.formatter_of_out_channel !cvc3out in
  Format.fprintf fm "%s\n@?" cmd
(*output_string !cvc3out (cmd ^ "\n");
  flush !cvc3out*)
let send_cmd =
  Logger.log_block1
    "Cvc3Interface.send_cmd"
    ~before:(Logger.printf "CVC3 input: %a@," String.pr)
    send_cmd

let recv_cmd () = input_line !cvc3in
let recv_cmd =
  Logger.log_block1
    "Cvc3Interface.recv_cmd"
    ~after:(Logger.printf "CVC3 output: %a@," String.pr)
    recv_cmd

let open_cvc3 () =
  cnt := 0;
  let cin, cout, cerr =
    Unix.open_process_full (!SMTProver.cvc3_command ^ " " ^ interactive) [||]
  in
  cvc3in := cin;
  cvc3out := cout;
  cvc3err := cerr;
  send_cmd "STRING : TYPE; __string__ : STRING;"

let close_cvc3 () =
  match Unix.close_process_full (!cvc3in, !cvc3out, !cvc3err) with
  | Unix.WEXITED(_) | Unix.WSIGNALED(_) | Unix.WSTOPPED(_) -> ()

let string_of_var = Idnt.serialize >> String.escape

let string_of_type ty =
  if Type.is_ext ty then
    Type.let_ext ty String.uppercase
  else if Type.is_unit ty then "INT"
  else if Type.is_bool ty then "BOOLEAN"
  else if Type.is_int ty then "INT"
  else if Type.is_real ty then "REAL"
  else if Type.is_string ty then "STRING"
  else
    Logger.debug_assert_false
      ~on_failure:(fun () -> Format.printf "%a@." Type.pr ty)
      ()

let string_of_env env =
  env
  |> List.map (fun (x, ty) -> deco (string_of_var x) ^ ":" ^ string_of_type ty)
  |> String.concat "; "

let string_of_env_comma env =
  env
  |> List.map (fun (x, ty) -> deco (string_of_var x) ^ ":" ^ string_of_type ty)
  |> String.concat ", "

let string_of_const c =
  match c with
  | Const.Unit -> "0"(*"UNIT"*)
  | Const.Eq(ty) when Type.is_unit ty -> "="

  | Const.True -> "TRUE"
  | Const.False -> "FALSE"
  | Const.Eq(ty) when Type.is_bool ty -> "<=>"

  | Const.Int(n) -> string_of_int n
  | Const.Eq(ty) when Type.is_int ty -> "="
  | Const.Lt(ty) when Type.is_int ty -> "<"
  | Const.Gt(ty) when Type.is_int ty -> ">"
  | Const.Leq(ty) when Type.is_int ty -> "<="
  | Const.Geq(ty) when Type.is_int ty -> ">="
  | Const.Neg(ty) when Type.is_int ty -> "-"
  | Const.Add(ty) when Type.is_int ty -> "+"
  | Const.Sub(ty) when Type.is_int ty -> "-"
  | Const.Mul(ty) when Type.is_int ty -> "*"

  | Const.Real(f) -> string_of_float f
  | Const.Eq(ty) when Type.is_real ty -> "="

  | Const.String(s) -> "__string__" (* @todo *)
  | Const.Eq(ty) when Type.is_string ty -> "="

  | _ ->
    Logger.debug_assert_false
      ~on_failure:
        (fun () -> Format.printf "%s@." (Const.string_of c))
      ()

let string_of_term =
  CunTerm.fold_op
    (object
      method fvar x [] = deco (string_of_var x)
      method fcon c = string_of_const c
      method fuop c s = "(" ^ string_of_const c ^ " " ^ s ^ ")"
      method fbop c s1 s2 = "(" ^ s1 ^ " " ^ string_of_const c ^ " " ^ s2 ^ ")"
      method ftuple tys ss = assert false
      method fformula phi = assert false
    end)

let string_of_atom =
  CunAtom.fold_brel
    (object
      method fvar x ts = deco (string_of_var x)
      method fbrel c t1 t2 =
        "("
        ^ string_of_term t1 ^ " "
        ^ string_of_const c ^ " "
        ^ string_of_term t2
        ^ ")"
      method fdivides n t = assert false
      method frecognizer ty x t1 = assert false
      method fsmem ty e t = assert false
      method fssubset ty t1 t2 = assert false
      method fterm c ts = assert false
    end)

let rec string_of_formula phi =
  phi
  |> Formula.map_atom CunAtom.elim_neq
  |> Formula.para
    (object
      method fatom t = t |> string_of_atom
      method ftrue () = "TRUE"
      method ffalse () = "FALSE"
      method fnot _ s = "(NOT " ^ s ^ ")"
      method fand _ s1 _ s2 = "(" ^ s1 ^ " AND " ^ s2 ^ ")"
      method for_ _ s1 _ s2 = "(" ^ s1 ^ " OR " ^ s2 ^ ")"
      method fimply _ s1 _ s2 = "(" ^ s1 ^ " => " ^ s2 ^ ")"
      method fiff _ s1 _ s2 = "(" ^ s1 ^ " <=> " ^ s2 ^ ")"
      method fforall (x, ty) phi' _ =
        if Type.is_bool ty then
          Formula.band
            [Formula.subst [x, Formula.term_of Formula.mk_true] phi';
             Formula.subst [x, Formula.term_of Formula.mk_false] phi']
          |> string_of_formula
        else
          "(FORALL ("
          ^ string_of_env_comma [x, ty]
          ^ "): "
          ^ string_of_formula phi'
          ^ ")"
      method fexists _ _ _ = assert false
    end)

let is_valid_cvc3 t =
  cnt := !cnt + 1;

  let env = SimTypJudge.infer (Formula.term_of t) Type.mk_bool in
  let ts = [] in
  let inp =
    "PUSH;"
    ^ string_of_env env ^ ";"
    ^ String.concat
      " "
      (List.map (fun t -> "ASSERT " ^ (string_of_formula t) ^ "; ") ts)
    ^ "QUERY " ^ string_of_formula t ^ ";"
    ^ "POP;"
  in
  send_cmd inp;
  let ret = recv_cmd () in
  if Str.string_match (Str.regexp ".*Valid") ret 0 then
    begin
      Logger.printf0 "output of CVC3: valid@,";
      true
    end
  else if Str.string_match (Str.regexp ".*Invalid") ret 0 then
    begin
      Logger.printf0 "output of CVC3: invalid@,";
      false
    end
  else
    Logger.debug_assert_false
      ~on_failure:
        (fun () -> Format.printf "unknown error of CVC3: %s@," ret)
      ()

let is_valid = is_valid_quick is_valid_cvc3
let is_valid tenv =
  Logger.log_block1
    "Cvc3Interface.is_valid"
    ~before:(Logger.printf "input: %a@," Formula.pr)
    ~after:(Logger.printf "output: %a" Bool.pr)
    is_valid

let is_sat_cvc3 t =
  cnt := !cnt + 1;

  let env = SimTypJudge.infer (Formula.term_of t) Type.mk_bool in
  let ts = [] in
  let inp =
    "PUSH;"
    ^ string_of_env env ^ ";"
    ^ String.concat
      " "
      (List.map (fun t -> "ASSERT " ^ (string_of_formula t) ^ "; ") ts)
    ^ "CHECKSAT " ^ string_of_formula t ^ ";"
    ^ "POP;"
  in
  send_cmd inp;
  let ret = recv_cmd () in
  if Str.string_match (Str.regexp ".*Satisfiable") ret 0 then
    true
  else if Str.string_match (Str.regexp ".*Unsatisfiable") ret 0 then
    false
  else
    Logger.debug_assert_false
      ~on_failure:
        (fun () -> Format.printf "unknown error of CVC3: %s@." ret)
      ()
let is_sat = is_sat_cvc3 |> is_sat_quick
let is_sat tenv =
  Logger.log_block1
    "Cvc3Interface.is_sat"
    ~before:(Logger.printf "input: %a@," Formula.pr)
    ~after:(Logger.printf "output: %a" Bool.pr)
    is_sat

let implies tenv =
  CunFormula.mk_implies FormulaSimplifier.simplify (is_valid tenv)


let cvc3_block1 f x1 =
  let cin, cout, cerr =
    Unix.open_process_full (!SMTProver.cvc3_command ^ " " ^ interactive) [||]
  in
  cnt := !cnt + 1; (*@todo*)
  try
    let ret = f cin cout cerr x1 in
    close_in cin;
    close_out cout;
    close_in cerr;
    (match Unix.close_process_full (cin, cout, cerr) with
     | Unix.WEXITED(_) | Unix.WSIGNALED(_) | Unix.WSTOPPED(_) -> ());
    ret
  with exc ->
    close_in cin;
    close_out cout;
    close_in cerr;
    (match Unix.close_process_full (cin, cout, cerr) with
     | Unix.WEXITED(_) | Unix.WSIGNALED(_) | Unix.WSTOPPED(_) -> ());
    raise exc

let cvc3_block2 f x1 x2 =
  let cin, cout, cerr =
    Unix.open_process_full (!SMTProver.cvc3_command ^ " " ^ interactive) [||]
  in
  cnt := !cnt + 1; (*@todo*)
  try
    let ret = f cin cout cerr x1 x2 in
    close_in cin;
    close_out cout;
    close_in cerr;
    (match Unix.close_process_full (cin, cout, cerr) with
     | Unix.WEXITED(_) | Unix.WSIGNALED(_) | Unix.WSTOPPED(_) -> ());
    ret
  with exc ->
    close_in cin;
    close_out cout;
    close_in cerr;
    (match Unix.close_process_full (cin, cout, cerr) with
     | Unix.WEXITED(_) | Unix.WSIGNALED(_) | Unix.WSTOPPED(_) -> ());
    raise exc

let rec input_asserts cin =
  try
    let s = input_line cin in
    Logger.printf "CVC3 output: %a@," String.pr s;
    if Str.string_match (Str.regexp ".*ASSERT") s 0 then
      let pos_begin = String.index s '(' + 1 in
      let pos_end = String.index s ')' in
      let s' = String.sub s pos_begin (pos_end - pos_begin) in
      if Str.string_match (Str.regexp "cvc3") s' 0 then (* @todo *)
        input_asserts cin
      else
        s' :: input_asserts cin
    else (* @todo *)
      input_asserts cin
  with End_of_file ->
    []

let input_solution cin =
  input_asserts cin
  |> List.map
    (fun s ->
       let _, s = String.split s "_" in
       let x, n = String.split s " = " in
       Logger.printf "%s = %s@," x n;
       Idnt.deserialize x, n)


(* @todo CVC3 supports nonlinear integer inequalities? *)
let solve_cvc3 cin cout cerr t =
  let env = SimTypJudge.infer (Formula.term_of t) Type.mk_bool in
  let inp =
    "PUSH;"
    ^ string_of_env env ^ ";"
    ^ "CHECKSAT " ^ string_of_formula t ^ ";"
    ^ "COUNTERMODEL;"
    ^ "POP;"
  in
  Logger.printf "CVC3 input: %a@," String.pr inp;
  let fm = Format.formatter_of_out_channel cout in
  Format.fprintf fm "%s\n@?" inp;
  close_out cout; (* this is necessary!! *)

  let s = input_line cin in
  Logger.printf "CVC3 output: %a@," String.pr s;
  if Str.string_match (Str.regexp ".*Unsatisfiable.") s 0 then
    raise SMTProver.Unsat
  else if Str.string_match (Str.regexp ".*Satisfiable.") s 0 then
    input_solution cin |>
    List.map (fun (x, n) -> x, IntTerm.make (int_of_string n))
  else if Str.string_match (Str.regexp ".*Unknown.") s 0 then
    raise SMTProver.Unknown
  else
    Logger.debug_assert_false
      ~on_failure:
        (fun () -> Format.printf "error in solve_cvc3: %a@," Formula.pr t)
      ()

(* We must reopen/reclose CVC3 for each query. Otherwise, it will get stuck.
   This is unavoidable unless we read strings until we get End_of_file *)
(** @todo do not reopen CVC3 *)
let solve_int = cvc3_block1 solve_cvc3
let solve_int = Logger.log_block1 "Cvc3Interface.solve" solve_int



let string_of_int_bv n =
  assert (n >= 0);
  let bv = BitVector.of_nat n in
  String.concat "" ("0bin" :: List.map string_of_int bv), List.length bv

let int_of_string_bv s =
  assert (String.starts_with s "0bin");
  let bv =
    List.map
      (fun c -> if c = '0' then 0 else if c = '1' then 1 else assert false)
      (String.explode (String.sub s 4 (String.length s - 4)))
  in
  BitVector.nat_of bv

(* encoding unit as 0 *)
let string_of_type_bv rbit ty =
  if Type.is_unit ty then "BITVECTOR(1)"
  else if Type.is_bool ty then "BOOLEAN"
  else if Type.is_int ty then "BITVECTOR(" ^ string_of_int rbit ^ ")"
  else assert false

let string_of_env_bv rbit env =
  env
  |> List.map
    (fun (x, ty) ->
       deco (string_of_var x) ^ ":" ^ string_of_type_bv rbit ty)
  |> String.concat "; "

let string_of_env_comma_bv rbit env =
  env
  |> List.map
    (fun (x, ty) ->
       deco (string_of_var x) ^ ":" ^ string_of_type_bv rbit ty)
  |> String.concat ", "

let string_of_const_bv c bits =
  match c with
  | Const.Unit ->
    "0bin0"(*"UNIT"*), 1

  | Const.Int(n) ->
    string_of_int_bv n
  | Const.Leq(intty) ->
    let [bit1; bit2] = bits in
    "BVLE", max bit1 bit2
  | Const.Geq(intty) ->
    let [bit1; bit2] = bits in
    "BVGE", max bit1 bit2
  | Const.Lt(intty) ->
    let [bit1; bit2] = bits in
    "BVLT", max bit1 bit2
  | Const.Gt(intty) ->
    let [bit1; bit2] = bits in
    "BVGT", max bit1 bit2
  | Const.Eq(intty) ->
    let [bit1; bit2] = bits in
    "=", max bit1 bit2
  | Const.Neg(intty) ->
    let [bit] = bits in
    "BVUMINUS", bit
  | Const.Add(intty) ->
    let [bit1; bit2] = bits in
    "BVPLUS", max bit1 bit2 + 1
  | Const.Sub(intty) ->
    let [bit1; bit2] = bits in
    "BVSUB", bit1
  | Const.Mul(intty) ->
    let [bit1; bit2] = bits in
    "BVMULT", bit1 + bit2

  | _ ->
    Logger.debug_assert_false
      ~on_failure:
        (fun () ->
           Format.printf "error in string_of_const_bv: %s@," (Const.string_of c))
      ()


let string_of_term_bv rbit =
  CunTerm.fold_op
    (object
      method fvar x [] = deco (string_of_var x), rbit
      method fcon c = string_of_const_bv c []
      method fuop c (s, bit) =
        assert (match c with Const.Neg(_) -> false | _ -> true);
        let cstr, bit = string_of_const_bv c [bit] in
        cstr ^ "(" ^ s ^ ")", bit
      method fbop c (s1, bit1) (s2, bit2) =
        assert (match c with Const.Sub(_) -> false | _ -> true);
        if Const.is_ibop c then
          let cstr, bit = string_of_const_bv c [bit1; bit2] in
          cstr ^ "(" ^ string_of_int bit ^ ", " ^ s1 ^ ", " ^ s2 ^ ")", bit
        else
          assert false
      method ftuple tys rs = assert false
      method fformula phi = assert false
    end)

let string_of_atom_bv rbit =
  CunAtom.fold_brel
    (object
      method fvar x [] =
        deco (string_of_var x), rbit
      method fbrel c t1 t2 =
        let (s1, bit1) = string_of_term_bv rbit t1 in
        let (s2, bit2) = string_of_term_bv rbit t2 in
        if Const.is_ibrel c then
          let cstr, bit = string_of_const_bv c [bit1; bit2] in
          let s1 =
            if bit = bit1 then
              s1
            else
              "BVZEROEXTEND("
              ^ s1 ^ ", "
              ^ string_of_int (bit - bit1)
              ^ ")"
          in
          let s2 =
            if bit = bit2 then
              s2
            else
              "BVZEROEXTEND("
              ^ s2 ^ ", "
              ^ string_of_int (bit - bit2)
              ^ ")"
          in
          if c = Const.Eq(Type.mk_int) then
            "(" ^ s1 ^ " " ^ cstr ^ " " ^ s2 ^ ")", bit
          else
            cstr ^ "(" ^ s1 ^ ", " ^ s2 ^ ")", bit
        else if Const.is_bbrel c then
          let cstr, bit = string_of_const_bv c [bit1; bit2] in
          "(" ^ s1 ^ " " ^ cstr ^ " " ^ s2 ^ ")", bit
        else
          assert false
      method fdivides n t = assert false
      method frecognizer ty x t1 = assert false
      method fsmem ty e t = assert false
      method fssubset ty t1 t2 = assert false
      method fterm c ts = assert false
    end)

let string_of_formula_bv rbit t =
  t
  |> Formula.map_atom CunAtom.elim_neq
  |> Formula.fold
    (object
      method fatom atm = atm |> string_of_atom_bv rbit |> fst
      method ftrue () = "TRUE"
      method ffalse () = "FALSE"
      method fnot s = "(NOT " ^ s ^ ")"
      method fand s1 s2 = "(" ^ s1 ^ " AND " ^ s2 ^ ")"
      method for_ s1 s2 = "(" ^ s1 ^ " OR " ^ s2 ^ ")"
      method fimply s1 s2 = "(" ^ s1 ^ " => " ^ s2 ^ ")"
      method fiff s1 s2 = "(" ^ s1 ^ " <=> " ^ s2 ^ ")"
      method fforall _ _ = assert false
      method fexists _ _ = assert false
    end)

let solve_nat_bv_cvc3 cin cout cerr rbit phi =
  Logger.printf "using %a bit@," Integer.pr rbit;
  let phi = Formula.map_atom CunAtom.elim_neg phi in
  let env = SimTypJudge.infer (Formula.term_of phi) Type.mk_bool in
  let inp =
    "PUSH;"
    ^ string_of_env_bv rbit env ^ ";"
    ^ "CHECKSAT " ^ string_of_formula_bv rbit phi ^ ";"
    ^ "COUNTERMODEL;"
    ^ "POP;"
  in
  Logger.printf "CVC3 input: %a@," String.pr inp;
  let fm = Format.formatter_of_out_channel cout in
  Format.fprintf fm "%s\n@?" inp;
  close_out cout; (* this is necessary!! *)

  let s = input_line cin in
  Logger.printf "CVC3 output: %a@," String.pr s;
  if Str.string_match (Str.regexp ".*Unsatisfiable.") s 0 then
    raise SMTProver.Unsat
  else if Str.string_match (Str.regexp ".*Satisfiable.") s 0 then
    input_solution cin
    |> List.map (fun (x, n) -> x, IntTerm.make (int_of_string_bv n))
  else if Str.string_match (Str.regexp ".*Unknown.") s 0 then
    raise SMTProver.Unknown
  else
    Logger.debug_assert_false
      ~on_failure:
        (fun () ->
           Format.printf "error in solve_nat_bv_cvc3: %a@," Formula.pr phi)
      ()

(* We must reopen/reclose CVC3 for each query. Otherwise, it will get stuck.
   This is unavoidable unless we read strings until we get End_of_file *)
(** find natural number solution using bit-blasting and SAT
    @todo do not reopen CVC3 *)
let solve_nat_bv = cvc3_block2 solve_nat_bv_cvc3
let solve_nat_bv =
  Logger.log_block2 "Cvc3Interface.solve_nat_bv" solve_nat_bv

let solve_int_poly_constr phi =
  try
    phi
    |> solve_int
  (*|> List.map (Pair.map_snd IntTerm.int_of)*)
  with
  | Not_found ->
    assert false
  | SMTProver.Unknown ->
    raise PolyConstrSolver.Unknown
  | SMTProver.Unsat ->
    raise PolyConstrSolver.NoSolution
let solve_int_poly_constr =
  Logger.log_block1 "Cvc3Interface.solve_int_poly_constr" solve_int_poly_constr

let solve_nat_bv_poly_constr rbit phi =
  try
    phi
    |> solve_nat_bv rbit
  (*|> List.map (Pair.map_snd IntTerm.int_of)*)
  with
  | Not_found ->
    assert false
  | SMTProver.Unknown ->
    raise PolyConstrSolver.Unknown
  | SMTProver.Unsat ->
    raise PolyConstrSolver.NoSolution
let solve_nat_bv_poly_constr =
  Logger.log_block2
    "Cvc3Interface.solve_nat_bv_poly_constr"
    solve_nat_bv_poly_constr

let cvc3 =
  object
    method initialize = open_cvc3
    method finalize = close_cvc3
    method is_valid = is_valid
    method is_sat = is_sat
    method implies = implies
    method solve _ _ = assert false
  end

let _ =
  SMTProver.cvc3 := cvc3;
  PolyConstrSolver.ext_solve_cvc3 := solve_int_poly_constr;
  PolyConstrSolver.ext_solve_nat_bv := solve_nat_bv_poly_constr;
