open Util
open Combinator
open Term
open Z3

let set_timeout ctx solver timeout =
  let params = Params.mk_params ctx in
  let r = Symbol.mk_string ctx ":timeout" in
  Params.add_int params r timeout;
  Solver.set_parameters solver params

let set_timeout_opt ctx solver timeout =
  let params = Params.mk_params ctx in
  let r = Symbol.mk_string ctx ":timeout" in
  Params.add_int params r timeout;
  Optimize.set_parameters solver params

let params =
  [(*("MODEL","true");*)
    (*("SOFT_TIMEOUT", string_of_int !Global.timeout_z3);*)
    (*("MBQI", "false")*)
    (*("smtlib2_compliant", "true");*)(*@todo uncommenting this causes a coercion error for mixed integer problems!*)
    ("well_sorted_check", "true")]
let ctx = mk_context params

let push_pop solver f tenv phi =
  Solver.push solver;
  try
    let ret = f solver tenv phi in
    Solver.pop solver 1;
    ret
  with e ->
    (* this is necessary to avoid Z3.Error(_, 2) *)
    Solver.add solver [Boolean.mk_true ctx];
    Solver.pop solver 1;
    raise e

let push_pop_opt solver f tenv phi =
  Optimize.push solver;
  try
    let ret = f solver tenv phi in
    Optimize.pop solver;
    ret
  with e ->
    (* this is necessary to avoid Z3.Error(_, 2) *)
    Optimize.add solver [Boolean.mk_true ctx];
    Optimize.pop solver;
    raise e

(* @todo elim boolean terms *)

(** {6 Formula conversion} *)

let sym_of_var = Idnt.serialize >> String.escape >> Symbol.mk_string ctx
let sym_of_var_nonenc = Idnt.string_of >> Symbol.mk_string ctx

let int_type = Arithmetic.Integer.mk_sort ctx
let bool_type = Boolean.mk_sort ctx
let real_type = Arithmetic.Real.mk_sort ctx

let tuple_sort_of sorts =
  let tuple_num = List.length sorts in
  Tuple.mk_sort ctx
    ("tuple" ^ string_of_int tuple_num |> Symbol.mk_string ctx)
    (List.init tuple_num
       (fun i -> "get_" ^ Ordinal.string_of (Ordinal.make i)
                 |> Symbol.mk_string ctx))
    sorts

let rec of_type ty =
  Type.fold
    (object
      method fvar _ = of_type !SMTProver.var_type
      method fbase = function
        | TypConst.Unit -> of_type !SMTProver.var_type
        | TypConst.Bool -> bool_type
        | TypConst.Int -> int_type
        | TypConst.Real -> real_type
        | TypConst.Top -> of_type !SMTProver.var_type
        | _ ->
          raise (Global.NotImplemented "fbase in Z3Interface.of_type")
      method farrow r1 r2 =
        raise (Global.NotImplemented "farrow in Z3Interface.of_type")
      method fforall p r =
        raise (Global.NotImplemented "fforall in Z3Interface.of_type")
      method fexists p r =
        raise (Global.NotImplemented "fexists in Z3Interface.of_type")
    end)
    ty
let of_type = Logger.log_block1 "Z3Interface.of_type" of_type

let of_formula' = ref (fun _ -> assert false)
let of_term =
  CunTerm.fold
    (object
      method fvar x rs = fun var_tenv bind_tenv ->
        try
          if rs <> [] then raise Not_found;
          let i, (_, ty) = List.findi (fun _ -> fst >> (=) x) bind_tenv in
          Quantifier.mk_bound ctx i ty
        with Not_found ->
          let ty = TypEnv.lookup var_tenv x |> SMTProver.instantiate_type in
          let sym = sym_of_var x in
          if rs <> [] then
            let args, ret = Type.args_ret ty in
            FuncDecl.apply
              (FuncDecl.mk_func_decl ctx
                 sym
                 (List.map of_type args)
                 (of_type ret))
              (List.map (fun r -> r var_tenv bind_tenv) rs)
          else Expr.mk_const ctx sym (ty |> of_type)
      method funit () = fun var_tenv bind_tenv ->
        Arithmetic.Integer.mk_numeral_i ctx 0 (* @todo ad-hoc *)
      method ftrue () = fun var_tenv bind_tenv ->
        Boolean.mk_true ctx
      method ffalse () = fun var_tenv bind_tenv ->
        Boolean.mk_false ctx
      method fint n = fun var_tenv bind_tenv ->
        Arithmetic.Integer.mk_numeral_i ctx n
      method fbigint n = fun var_tenv bind_tenv ->
        Arithmetic.Integer.mk_numeral_s ctx (Big_int_Z.string_of_big_int n)
      method frational n d = fun var_tenv bind_tenv ->
        Arithmetic.Real.mk_numeral_nd ctx n d
      method freal f = fun var_tenv bind_tenv ->
        Q.of_float f
        |> Q.to_string (* need this? *) (* @todo check if nan *)
        |> Arithmetic.Real.mk_numeral_s ctx
      method fstring _ = fun var_tenv bind_tenv ->
        raise (Global.NotImplemented "fstring in Z3Interface.of_term")
      method fneg _ r = fun var_tenv bind_tenv ->
        Arithmetic.mk_unary_minus ctx (r var_tenv bind_tenv)
      method fadd _ r1 r2 = fun var_tenv bind_tenv ->
        Arithmetic.mk_add ctx
          [ r1 var_tenv bind_tenv;
            r2 var_tenv bind_tenv ]
      method fsub _ r1 r2 = fun var_tenv bind_tenv ->
        Arithmetic.mk_sub ctx
          [ r1 var_tenv bind_tenv;
            r2 var_tenv bind_tenv ]
      method fmul _ r1 r2 = fun var_tenv bind_tenv ->
        Arithmetic.mk_mul ctx
          [ r1 var_tenv bind_tenv;
            r2 var_tenv bind_tenv ]
      method fdiv _ r1 r2 = fun var_tenv bind_tenv ->
        Arithmetic.mk_div ctx
          (r1 var_tenv bind_tenv)
          (r2 var_tenv bind_tenv)
      method fmax _ r1 r2 = fun var_tenv bind_tenv ->
        raise (Global.NotImplemented "fmax in Z3Interface.of_term")
      method fmin _ r1 r2 = fun var_tenv bind_tenv ->
        raise (Global.NotImplemented "fmin in Z3Interface.of_term")
      method fmod r1 r2 = fun var_tenv bind_tenv ->
        Arithmetic.Integer.mk_mod ctx
          (r1 var_tenv bind_tenv)
          (r2 var_tenv bind_tenv)
      method fufun ty x rs = fun var_tenv bind_tenv ->
        raise (Global.NotImplemented "fufun in Z3Interface.of_term")
      method fcoerce _ r = fun var_tenv bind_tenv ->
        Z3.Arithmetic.Integer.mk_int2real ctx (r var_tenv bind_tenv)
      method fformula = !of_formula'
    end)
let of_term = Logger.log_block3 "Z3Interface.of_term" of_term

let of_atom =
  CunAtom.fold
    (object
      method fvar x ts = fun var_tenv bind_tenv ->
        if ts <> [] then
          let args, _ = TypEnv.lookup var_tenv x |> Type.args_ret in
          FuncDecl.apply
            (FuncDecl.mk_func_decl ctx
               (sym_of_var x)
               (List.map of_type args)
               bool_type)
            (List.map (fun t -> of_term t var_tenv bind_tenv) ts)
        else
          let sym = sym_of_var x in
          Boolean.mk_eq ctx
            (Expr.mk_const ctx sym bool_type)
            (Boolean.mk_true ctx)
      method feq _ t1 t2 = fun var_tenv bind_tenv ->
        Boolean.mk_eq ctx
          (of_term t1 var_tenv bind_tenv)
          (of_term t2 var_tenv bind_tenv)
      method fneq _ t1 t2 = fun var_tenv bind_tenv ->
        Boolean.mk_not ctx
          (Boolean.mk_eq ctx
             (of_term t1 var_tenv bind_tenv)
             (of_term t2 var_tenv bind_tenv))
      method flt _ t1 t2 = fun var_tenv bind_tenv ->
        Arithmetic.mk_lt ctx
          (of_term t1 var_tenv bind_tenv)
          (of_term t2 var_tenv bind_tenv)
      method fgt _ t1 t2 = fun var_tenv bind_tenv ->
        Arithmetic.mk_gt ctx
          (of_term t1 var_tenv bind_tenv)
          (of_term t2 var_tenv bind_tenv)
      method fleq _ t1 t2 = fun var_tenv bind_tenv ->
        Arithmetic.mk_le ctx
          (of_term t1 var_tenv bind_tenv)
          (of_term t2 var_tenv bind_tenv)
      method fgeq _ t1 t2 = fun var_tenv bind_tenv ->
        Arithmetic.mk_ge ctx
          (of_term t1 var_tenv bind_tenv)
          (of_term t2 var_tenv bind_tenv)
      method fdivides n t = fun var_tenv bind_tenv ->
        raise (Global.NotImplemented "fdivides in Z3Interface.of_atom")
      method fterm c ts = fun var_tenv bind_tenv ->
        Boolean.mk_eq ctx
          (of_term
             (Term.mk_app (Term.mk_const c) ts)
             var_tenv bind_tenv)
          (Boolean.mk_true ctx)
    end)
let of_atom = Logger.log_block3 "Z3Interface.of_atom" of_atom

let of_formula =
  Formula.fold
    (object
      method fatom atm = fun var_tenv bind_tenv ->
        of_atom atm var_tenv bind_tenv
      method ftrue () = fun var_tenv bind_tenv ->
        Boolean.mk_true ctx
      method ffalse () = fun var_tenv bind_tenv ->
        Boolean.mk_false ctx
      method fnot s = fun var_tenv bind_tenv ->
        Boolean.mk_not ctx (s var_tenv bind_tenv)
      method fand s1 s2 = fun var_tenv bind_tenv ->
        Boolean.mk_and ctx
          [ s1 var_tenv bind_tenv;
            s2 var_tenv bind_tenv ]
      method for_ s1 s2 = fun var_tenv bind_tenv ->
        Boolean.mk_or ctx
          [ s1 var_tenv bind_tenv;
            s2 var_tenv bind_tenv ]
      method fimply s1 s2 = fun var_tenv bind_tenv ->
        Boolean.mk_implies ctx
          (s1 var_tenv bind_tenv)
          (s2 var_tenv bind_tenv)
      method fiff s1 s2 = fun var_tenv bind_tenv ->
        Boolean.mk_iff ctx
          (s1 var_tenv bind_tenv)
          (s2 var_tenv bind_tenv)
      method fforall (x, ty) s1 = fun var_tenv bind_tenv ->
        let ty = SMTProver.instantiate_type ty in
        let sym = sym_of_var x in
        let ty' = of_type ty in
        (*let bv = Quantifier.mk_bound ctx 0 ty' in*)
        Quantifier.mk_forall ctx [ ty' ] [ sym ]
          (s1 var_tenv ((x, ty') :: bind_tenv))
          None [] [] None None
        |> Quantifier.expr_of_quantifier
      method fexists (x, ty) s1 = fun var_tenv bind_tenv ->
        let ty = SMTProver.instantiate_type ty in
        let sym = sym_of_var x in
        let ty' = of_type ty in
        (*let bv = Quantifier.mk_bound ctx 0 ty' in*)
        Quantifier.mk_exists ctx [ ty' ] [ sym ]
          (s1 var_tenv ((x, ty') :: bind_tenv))
          None [] [] None None
        |> Quantifier.expr_of_quantifier
    end)
let of_formula =
  Logger.log_block3 "Z3Interface.of_formula"
    ~before:(fun p _ _ -> Logger.printf "input: %a@," Formula.pr p)
    of_formula
let () = of_formula' := of_formula

let of_sort s =
  match s |> Sort.get_sort_kind with
  | Z3enums.REAL_SORT -> Type.mk_real
  | Z3enums.INT_SORT -> Type.mk_int
  | Z3enums.BOOL_SORT -> Type.mk_bool
  | _ -> Type.mk_unknown (*todo*)

let rec term_of expr =
  try
    if Arithmetic.is_int_numeral expr then
      Arithmetic.Integer.get_int expr |> IntTerm.make
    else if Expr.is_const expr then
      Expr.to_string expr
      |> Idnt.deserialize
      |> Term.mk_var
    else if expr |> Expr.ast_of_expr |> AST.is_var then
      Expr.to_string expr
      |> (fun x -> try Idnt.deserialize x with Not_found -> Idnt.make x)
      |> Term.mk_var
    else if Arithmetic.is_add expr then
      Expr.get_args expr
      |> (fun (zt :: zts) ->
          List.fold_left
            (fun x y ->
               let t = term_of y in
               let ty = Expr.get_sort y |> of_sort in
               NumTerm.add ty x t)
            (term_of zt)
            zts)
    else if Arithmetic.is_sub expr then
      Expr.get_args expr
      |> (fun (zt :: zts) ->
          List.fold_left
            (fun x y ->
               let t = term_of y in
               let ty = Expr.get_sort y |> of_sort in
               NumTerm.sub ty x t)
            (term_of zt)
            zts)
    else if Arithmetic.is_mul expr then
      Expr.get_args expr
      |> (fun (zt :: zts) ->
          List.fold_left
            (fun x y ->
               let t = term_of y in
               let ty = Expr.get_sort y |> of_sort in
               NumTerm.mul ty x t)
            (term_of zt)
            zts)
    else if Arithmetic.is_div expr then
      Expr.get_args expr
      |> (fun (zt :: zts) ->
          List.fold_left
            (fun x y ->
               let t = term_of y in
               let ty = Expr.get_sort y |> of_sort in
               NumTerm.div ty x t)
            (term_of zt)
            zts)
    else if Arithmetic.is_idiv expr then
      Expr.get_args expr
      |> (fun (zt :: zts) ->
          List.fold_left
            (fun x y ->
               let t = term_of y in
               let ty = Expr.get_sort y |> of_sort in
               NumTerm.div ty x t)
            (term_of zt)
            zts)
    else if Arithmetic.is_modulus expr then
      Expr.get_args expr
      |> (fun (zt :: zts) ->
          List.fold_left
            (fun x y ->
               let t = term_of y in
               let ty = Expr.get_sort y |> of_sort in
               NumTerm.mod_ ty x t)
            (term_of zt)
            zts)
    else begin(*@todo*)
      Format.printf "error: %s@," (Expr.to_string expr);
      assert false
      (*Term.var_of_string (Expr.to_string expr)*)
    end
  with
  | Match_failure(_) as e ->
    Format.printf "%s@," (Printexc.to_string e);
    Format.printf "pattern matching error: %s@," (Expr.to_string expr);
    assert false

let bool_of_lbool = function
  | Z3enums.L_TRUE -> true
  | Z3enums.L_FALSE -> false
  | Z3enums.L_UNDEF -> assert false

let term_of_model model expr =
  let value =
    match Model.eval model expr true with
    | None -> assert false
    | Some x -> x
  in
  match Expr.get_sort expr |> Sort.get_sort_kind with
  | Z3enums.REAL_SORT ->
    value
    |> Arithmetic.Real.numeral_to_string
    |> Q.of_string
    |> Float.of_q
    |> RealTerm.make
  | Z3enums.INT_SORT ->
    let n =
      value
      |> Arithmetic.Integer.get_big_int
      |> Big_int.string_of_big_int
      |> Big_int_Z.big_int_of_string
    in
    begin
      try n |> Big_int_Z.int_of_big_int |> IntTerm.make
      with Failure "int_of_big_int"  -> n |> IntTerm.of_big_int
    end
  | Z3enums.BOOL_SORT ->
    value
    |> Boolean.get_bool_value
    |> bool_of_lbool
    |> BoolTerm.make
  | Z3enums.DATATYPE_SORT ->
    value
    |> Expr.to_string
    |> Idnt.make
    |> Term.mk_var (*@todo*)
  | _ -> assert false

let rec formula_of p =
  if Boolean.is_true p then Formula.mk_true
  else if Boolean.is_false p then Formula.mk_false
  else if Boolean.is_eq p then
    Expr.get_args p
    |> (fun [zt1; zt2] ->
        let sort = Expr.get_sort zt1 in
        match sort |> Sort.get_sort_kind with
        | Z3enums.INT_SORT ->
            let t1 = term_of zt1 in
            let t2 = term_of zt2 in
            let ty = Type.mk_int in
            Formula.eq ty t1 t2
        | Z3enums.BOOL_SORT ->
            let t1 = formula_of zt1 in
            let t2 = formula_of zt2 in
            let ty = of_sort sort in
            Formula.mk_iff t1 t2
        | _ -> raise (Global.NotImplemented "eq in Z3Interface.formula_of"))
  else if Arithmetic.is_le p then
    Expr.get_args p
    |> (fun [zt1; zt2] ->
        let t1 = term_of zt1 in
        let t2 = term_of zt2 in
        let ty = Expr.get_sort zt1 |> of_sort in
        NumFormula.leq ty t1 t2)
  else if Arithmetic.is_ge p then
    Expr.get_args p
    |> (fun [zt1; zt2] ->
        let t1 = term_of zt1 in
        let t2 = term_of zt2 in
        let ty = Expr.get_sort zt1 |> of_sort in
        NumFormula.geq ty t1 t2)
  else if Arithmetic.is_lt p then
    Expr.get_args p
    |> (fun [zt1; zt2] ->
        let t1 = term_of zt1 in
        let t2 = term_of zt2 in
        let ty = Expr.get_sort zt1 |> of_sort in
        NumFormula.lt ty t1 t2)
  else if Arithmetic.is_gt p then
    Expr.get_args p
    |> (fun [zt1; zt2] ->
        let t1 = term_of zt1 in
        let t2 = term_of zt2 in
        let ty = Expr.get_sort zt1 |> of_sort in
        NumFormula.gt ty t1 t2)
  else if Boolean.is_and p then
    Expr.get_args p
    |> List.map formula_of
    |> Formula.band
  else if Boolean.is_or p then
    Expr.get_args p
    |> List.map formula_of
    |> Formula.bor
  else if Boolean.is_iff p then
    Expr.get_args p
    |> List.map formula_of
    |> fun [phi1; phi2] -> Formula.mk_iff phi1 phi2
  else if Boolean.is_implies p then
    Expr.get_args p
    |> List.map formula_of
    |> fun [phi1; phi2] -> Formula.imply phi1 phi2
  else if Boolean.is_not p then
    Expr.get_args p
    |> List.map formula_of
    |> fun [phi] -> Formula.bnot phi
  else if Expr.is_const p then
    Expr.to_string p
    |> Idnt.deserialize
    |> flip Formula.mk_var []
  else if Expr.ast_of_expr p |> AST.is_quantifier then begin
                                                      let q = Quantifier.quantifier_of_expr p in
                                                      if !SMTProver.print_z3 then
                                                        Format.printf "quantifier: %a@." String.pr (Quantifier.to_string q);
                                                      if Quantifier.is_universal q then
                                                        Quantifier.get_body q |> formula_of
                                                      else
                                                        let env =
                                                          List.zip
                                                            (Quantifier.get_bound_variable_names q
                                                             |> List.map (Symbol.to_string >> Idnt.make))
                                                            (Quantifier.get_bound_variable_sorts q
                                                             |> List.map of_sort)
                                                        in
                                                        Quantifier.get_body q
                                                        |> formula_of
                                                        |> (fun x ->
                                                            if !SMTProver.print_z3 then
                                                              Format.printf "exist: %a@.env: %a@." Formula.pr x TypEnv.pr env; x)
                                                        |> Formula.exists env
                                                    end
  else begin
      let to_string p =
        match p |> Expr.ast_of_expr |> AST.get_ast_kind with
        | Z3enums.APP_AST -> "APP_AST"
        | Z3enums.NUMERAL_AST -> "NUMERAL_AST"
        | Z3enums.FUNC_DECL_AST -> "FUNC_DECL_AST"
        | Z3enums.SORT_AST -> "SORT_AST"
        | Z3enums.QUANTIFIER_AST -> "QUANTIFIER_AST"
        | Z3enums.VAR_AST -> "VAR_AST"
        | Z3enums.UNKNOWN_AST -> "UNKNOWN_AST"
        | _ -> "Not matched: to_string"
      in
      let to_typterm sorts args =
        assert (List.length sorts = List.length args);
        List.map2
          (fun sort arg ->
           let ty = of_sort sort in
           let term_of =
             if Type.is_bool ty then formula_of >> Formula.term_of
             else term_of
           in
           term_of arg, ty)
          sorts args
      in
      try
        let decl = Expr.get_func_decl p in
        let args = Expr.get_args p |> to_typterm (FuncDecl.get_domain decl) in
        let id = FuncDecl.get_name decl |> Symbol.to_string |> Idnt.deserialize in
        Pva.make id args
        |> Pva.to_formula
      with e ->
        Format.printf "raise %a@\nAST_kind: %a@\n"
                      String.pr (Printexc.to_string e) String.pr (to_string p);
        Format.printf "error Z3:@,  %a@," String.pr (Expr.to_string p);
        assert false
    end
let formula_of =
  Logger.log_block1 "Z3Interface.formula_of"
    ~before:(fun p -> Logger.printf "input: %a@," String.pr (Expr.to_string p))
    ~after:(Logger.printf "output: %a" Formula.pr)
    formula_of

(** {6 Satisfiability/validity checking} *)

let is_sat solver tenv phi =
  let phi =
    phi
    |> CunFormula.elim_unit
    |> Formula.map_atom CunAtom.elim_beq_bneq
  in
  let tenv, phi =
    SimTypInfer.infer_formula tenv phi
    (*SimTypJudge.infer (Formula.term_of phi) Type.mk_bool*)
  in
  let p = of_formula phi tenv [] in
  if !SMTProver.print_z3 then begin
    Format.printf "tenv: %a@." TypEnv.pr tenv;
    Format.printf "input to Z3:@.  %a@." String.pr (Expr.to_string p)
  end;
  Solver.add solver [p];
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unsat@.";
    false
  | Solver.SATISFIABLE ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  sat@.";
    true
  | Solver.UNKNOWN ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unknown@.";
    raise SMTProver.Unknown
let is_sat tenv phi =
  let solver = Solver.mk_solver ctx None in
  set_timeout ctx solver !Global.timeout_z3;
  try is_sat solver tenv phi
  with Global.NotImplemented _ ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unknown@.";
    raise SMTProver.Unknown
let is_sat =
  Logger.log_block2 "Z3Interface.is_sat"
    ~before:(fun _ -> Logger.printf "input: %a@," Formula.pr)
    ~after:(Logger.printf "output: %a" Bool.pr)
    is_sat

let is_valid tenv = SMTProver.dual_of (is_sat tenv)
let is_valid =
  Logger.log_block2 "Z3Interface.is_valid"
    ~before:(fun _ -> Logger.printf "input: %a@," Formula.pr)
    ~after:(Logger.printf "output: %a" Bool.pr)
    is_valid

let implies tenv =
  CunFormula.mk_implies FormulaSimplifier.simplify (is_valid tenv)

let get_model solver =
  let Some m =
    match solver with
    | `Optimize(solver) -> Optimize.get_model solver
    | `Solver(solver) -> Solver.get_model solver
  in
  if !SMTProver.print_z3 then
    Format.printf "output of Z3:@.  %a@." String.pr (Model.to_string m);
  List.from_to 0 (Model.get_num_consts m - 1)
  |> List.map (fun i ->
      try List.nth (Model.get_const_decls m) i with Not_found -> assert false)
  |> List.filter_map
    (fun fd ->
       let x =
         let sym = FuncDecl.get_name fd in
         match Symbol.kind sym with
         | Z3enums.INT_SYMBOL ->
           string_of_int (Symbol.get_int sym) |> Idnt.make
         | Z3enums.STRING_SYMBOL ->
           try Symbol.get_string sym |> Idnt.deserialize
           with
           | Not_found -> Symbol.get_string sym |> Idnt.make
           | _ -> assert false
       in
       match Model.get_const_interp m fd with
       | None ->
         Logger.printf0 "possibly bug@,";
         Some(x, IntTerm.zero(*@todo*))
       | Some(expr) ->
         try
           let t = term_of_model m expr in
           Logger.printf2 "sol: %a=%a@," Idnt.pr x Term.pr t;
           Some (x, t)
         with
         | Not_found -> assert false
         | Z3.Error("Conversion failed.") ->
           Logger.printf2 "sol: %a=%a@,"
             Idnt.pr x
             String.pr (Expr.to_string expr);
           Logger.printf0 "Conversion failed@,"; None)
let get_model = Logger.log_block1 "Z3Interface.get_model" get_model

let solve solver tenv phi =
  let phi =
    phi |> CunFormula.elim_unit |> Formula.map_atom CunAtom.elim_beq_bneq
  in
  let tenv, phi = SimTypInfer.infer_formula tenv phi in
  let p = of_formula phi tenv [] in
  if !SMTProver.print_z3 then begin
    Format.printf "tenv: %a@." TypEnv.pr tenv;
    Format.printf "input to Z3:@.  %a@." String.pr (Expr.to_string p)
  end;
  Solver.add solver [p];
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unsat@.";
    raise SMTProver.Unsat
  | Solver.SATISFIABLE ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  sat@.";
    get_model (`Solver solver)
  | Solver.UNKNOWN ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unknown@.";
    raise SMTProver.Unknown
let solve tenv phi =
  let solver = Solver.mk_solver ctx None in
  set_timeout ctx solver !Global.timeout_z3;
  try solve solver tenv phi
  with Global.NotImplemented _ ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unknown@.";
    raise SMTProver.Unknown
let solve = Logger.log_block2 "Z3Interface.solve" solve

let subtract_model tenv0 m1 m2 =
  let xs = List.map fst tenv0 in
  let m1 = Map_.restrict m1 xs |> List.sort compare in
  let m2 = Map_.restrict m2 xs |> List.sort compare in
  if List.length m1 <> List.length m2 then begin
    Format.printf "m1: %a@.m2: %a@." TermSubst.pr m1 TermSubst.pr m2;
    assert false
  end;
  List.map2
    (fun (x1, t1) (x2, t2) ->
       assert (x1 = x2);
       if List.assocF x1 tenv0 = Type.mk_real
       then x1, RealTerm.sub t1 t2
       else if List.assocF x1 tenv0 = Type.mk_int
       then x1, IntTerm.sub t1 t2
       else assert false)
    m1 m2

(** optimize a model with the objective [obj] *)
let solve_opt solver tenv0 phi obj =
  let phi =
    phi |> CunFormula.elim_unit |> Formula.map_atom CunAtom.elim_beq_bneq
  in
  let tenv, phi = SimTypInfer.infer_formula tenv0 phi in
  let p = of_formula phi tenv [] in
  let obj_t = match obj with SMTProver.Max(obj_t) | SMTProver.Min(obj_t) -> obj_t in
  let q = of_term obj_t tenv [] in
  if !SMTProver.print_z3 then begin
    Format.printf "tenv: %a@." TypEnv.pr tenv;
    Format.printf
      "input to Z3 opt:@.  %a@.%a@."
      String.pr (Expr.to_string p)
      String.pr (Expr.to_string q)
  end;
  Optimize.add solver [p];
  let handle =
    match obj with
    | SMTProver.Max(_) -> Optimize.maximize solver q
    | SMTProver.Min(_) -> Optimize.minimize solver q
  in
  match Optimize.check solver with
  | Solver.UNSATISFIABLE ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unsat@.";
    raise SMTProver.Unsat
  | Solver.UNKNOWN ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unknown@.";
    raise SMTProver.Unknown
  | Solver.SATISFIABLE ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  sat@.";
    let m =
      get_model (`Optimize solver)
      |> List.map (Pair.map_snd CunTerm.simplify)
    in
    let best = Term.subst m obj_t in
    if Optimize.get_upper handle |> Z3.Expr.to_string |> (=) "oo" then begin
      Optimize.add solver [p];
      let d =
        let step = RealTerm.one in
        match obj with
        | SMTProver.Max(_) -> RealFormula.geq obj_t (RealTerm.add best step)
        | SMTProver.Min(_) -> RealFormula.leq obj_t (RealTerm.sub best step)
      in
      Optimize.add solver [of_formula d tenv []];
      let _ =
        match obj with
        | SMTProver.Max(_) -> Optimize.maximize solver q
        | SMTProver.Min(_) -> Optimize.minimize solver q
      in
      match Optimize.check solver with
      | Solver.SATISFIABLE ->
        let d =
          subtract_model tenv0 (get_model (`Optimize solver)) m
          |> List.map (Pair.map_snd CunTerm.simplify)
        in
        raise (SMTProver.Unbounded(d, m))
      | _ -> assert false
    end else (m, best)
let solve_opt tenv phi obj =
  let solver = Optimize.mk_opt ctx in
  set_timeout_opt ctx solver !Global.timeout_z3;
  try solve_opt solver tenv phi obj
  with Global.NotImplemented _ ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unknown@.";
    raise SMTProver.Unknown

let solve_poly_constr phi =
  try phi |> solve [(*@todo*)]
  with
  | Not_found -> assert false
  | SMTProver.Unknown -> raise PolyConstrSolver.Unknown
  | SMTProver.Unsat -> raise PolyConstrSolver.NoSolution

let find_min_sat phi x =
  let solver = Solver.mk_solver ctx None in
  set_timeout ctx solver !Global.timeout_z3;
  Solver.push solver;
  let tenv =
    phi
    |> Formula.fvs
    |> List.cons x
    |> List.unique
    |> List.map (flip Pair.make Type.mk_int)
  in
  let p = of_formula phi tenv [] in
  if !SMTProver.print_z3 then
    Format.printf "input to Z3:@.  %a@." String.pr (Expr.to_string p);
  Solver.add solver [p];
  let rec loop n =
    Solver.push solver;
    Solver.add solver
      [of_formula (IntFormula.eq (Term.mk_var x) (IntTerm.make n)) tenv []];
    match Solver.check solver [] with
    | Solver.UNSATISFIABLE ->
      Solver.pop solver 1;
      loop (n + 1)
    | Solver.SATISFIABLE ->
      begin
        try
          let res =
            get_model (`Solver solver)
            |> List.map @@ Pair.map_snd
              (fun t ->
                 try IntTerm.int_of t with
                 | Not_found -> Format.printf "%a@." Term.pr t; assert false)
          in
          Solver.pop solver 1;
          res
        with Not_found -> assert false
      end
    | Solver.UNKNOWN -> assert false
  in
  let ret = loop 0 in
  Solver.pop solver 1;
  ret

(** get an unsat core of an unsat conjunction of formulas *)
let solve_labeled tenv lphis =
  let solver = Solver.mk_solver ctx None in
  set_timeout ctx solver !Global.timeout_z3;
  let lphis =
    lphis
    |> List.map (Pair.map_snd (CunFormula.elim_unit
                               >> Formula.map_atom CunAtom.elim_beq_bneq))
  in
  let tenv, lphis =
    SimTypInfer.infer_formulas tenv (List.map snd lphis)
    |> Pair.map_snd (List.zip (List.map fst lphis))
  in
  let ps, ls =
    List.split_mapi
      (fun i (l, phi) ->
         let p = of_formula phi tenv [] in
         if !SMTProver.print_z3 then
           Format.printf "input to Z3:@.  %a@." String.pr (Expr.to_string p);
         p, Expr.mk_const ctx (Symbol.mk_string ctx l) bool_type)
      lphis
  in
  List.iter2 (fun p l -> Solver.add solver [Boolean.mk_iff ctx l p]) ps ls;
  match Solver.check solver ls with
  | Solver.UNSATISFIABLE ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unsat@.";
    let core = Solver.get_unsat_core solver in
    let labels = List.map (Expr.ast_of_expr >> AST.to_string) core in
    raise (SMTProver.UnsatCore labels)
  | Solver.SATISFIABLE ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  sat@.";
    get_model (`Solver solver)
  | Solver.UNKNOWN ->
    if !SMTProver.print_z3 then Format.printf "output of Z3:@.  unknown@.";
    raise SMTProver.Unknown
let solve_labeled =
  Logger.log_block2 "Z3Interface.solve_labeled"
    ~before:(fun _ ->
        Logger.printf
          "input: %a@,"
          (List.pr (Pair.pr String.pr Formula.pr) ","))
    solve_labeled

let interpolate phi1 phi2 =
  let tenv, _ = SimTypInfer.infer_formula [] (Formula.band [phi1; phi2]) in
  let p1 = of_formula phi1 tenv [] in
  let p2 = of_formula phi2 tenv [] in
  let pat = Boolean.mk_and ctx [Interpolation.mk_interpolant ctx p1; p2] in
  match Interpolation.compute_interpolant ctx pat (Params.mk_params ctx) with
  | _, Some(astv), _ -> List.hd astv |> formula_of
  | _ -> raise InterpProver.NoInterpolant

let interpolate_z3 p =
  interpolate
  |> InterpProver.interpolate_quick
  |> (if !InterpProver.interp_simplify
      then InterpProver.interpolate_simplify ~qelim:QelimBody.elim_int_vars_full
      else id)
  |> CheckInterpProver.interpolate
  |> InterpProver.interpolate_log
  |> InterpProver.interpolate_fresh p

let qelim e =
  let goal = Goal.mk_goal ctx true false false in (* models, ucores, proofs *)
  Goal.add goal [e];
  let tactic = Tactic.mk_tactic ctx "qe" in
  let res =
    Tactic.apply tactic goal None
    |> flip Tactic.ApplyResult.get_subgoal 0
    |> Goal.as_expr
    |> flip Expr.simplify None
  in
  if !SMTProver.print_z3 then
    Format.printf "simplified:@.%a@." String.pr (Expr.to_string res);
  res
let qelim =
  Logger.log_block1 "Z3Interface.qelim"
    ~before:(Expr.to_string >> Logger.printf "input:@, %a@," String.pr)
    qelim

(** HornClause *)
let mk_bind_tenv hc =
  let fvs =
    hc
    |> HornClause.fvs_ty
    |> List.map (Pair.fold (fun x t -> x, of_type t))
  in
  let coeff =
    hc
    |> HornClause.coeffs
    |> List.map (fun x -> x, int_type) (* @assume coeffs are integers *)
  in
  fvs @ coeff
let mk_bind_tenv = Logger.log_block1 "mk_bind_tenv" mk_bind_tenv

let make_body tenv bind_tenv body =
  body
  |> HornClause.pvas_of_body
  |> List.map
    (fun pva ->
       of_atom
         (Pva.to_formula pva |> Formula.atom_of)
         tenv bind_tenv)
  |> (fun exprs ->
      (of_formula
         (HornClause.phi_of_body body)
         tenv bind_tenv)::exprs)
  |> Boolean.mk_and ctx
let make_body = Logger.log_block3 "make_body" make_body

let of_def_hc tenv hc =
  let head, body = HornClause.head_of hc, HornClause.body_of hc in
  let bind_tenv = mk_bind_tenv hc in
  let hd =
    match HornClause.pv_of_head head with
    | None -> assert false (* isn't this a goal clause? *)
    | Some(pvar) ->
      pvar
      |> PredVar.to_formula
      |> Formula.atom_of
      |> (fun a -> of_atom a tenv bind_tenv)
  in
  let bd = make_body tenv bind_tenv body in
  Boolean.mk_implies ctx bd hd
let of_def_hc = Logger.log_block2 "Z3Interface.of_def_hc" of_def_hc

let of_goal_hc tenv hc =
  let bind_tenv = mk_bind_tenv hc in
  let body = hc |> HornClause.body_of in
  make_body tenv bind_tenv body
let of_goal_hc = Logger.log_block2 "Z3Interface.of_goal_hc" of_goal_hc

let of_hccs tenv hccs =
  let defs, goals = hccs |> Pair.unfold HCCS.defs_of HCCS.goals_of in
  let def_exprs = defs |> List.map (of_def_hc tenv) in
  let goal_exprs = goals |> List.map (of_goal_hc tenv) in
  def_exprs, goal_exprs
let of_hccs = Logger.log_block2 "Z3Interface.of_hccs" of_hccs

(** fixedpoint *)
let get_answer fixed = Fixedpoint.get_answer fixed

(** make a model from an answered formula *)
let get_model_fixedpoint tenv fixed =
  let expr = get_answer fixed |> Option.elem_of_nf in
  if !SMTProver.print_z3 then
    Format.printf "answer: %a@." String.pr (Expr.to_string expr);
  let aux e =
    let e =
      let q = Quantifier.quantifier_of_expr e in
      if Quantifier.is_universal q then Quantifier.get_body q
      else assert false
    in
    let e = (* quantifier elimination and simplification *)
      let args = Expr.get_args e in
      let [pvar; body] = args in (* assume (= (P(x,y)) (phi)) *)
      qelim body |> Boolean.mk_iff ctx pvar
    in
    match e |> formula_of |> Formula.term_of |> Term.fun_args with
    | Const(Const.Eq(_)), [pvar; body]
    | Const(Const.Iff), [pvar; body] ->
      let pvar, phi =
        pvar
        |> Formula.of_term
        |> Pva.of_formula
        |> Pva.pvar_of
        |> Pair.map_fst
          (fun pv ->
             let pid = PredVar.idnt_of pv in
             let args_ty = TypEnv.lookup tenv pid |> Type.args_of in
             PredVar.make pid
               (List.map2
                  (fun (v,ty1) ty2 -> v, ty2)
                  (PredVar.fvs_ty pv)
                  args_ty))
      in
      let body =
        body
        |> Formula.of_term
        |> Formula.mk_and phi
        |> FormulaSimplifier.simplify
      in
      PredSubst.elem_of_pvar pvar body
    | e -> assert false
  in
  if Boolean.is_true expr then []
  else if expr |> Expr.ast_of_expr |> AST.is_quantifier
  then [aux expr]
  else if Boolean.is_and expr
  then List.map aux (Expr.get_args expr)
  else (Format.printf "expr: %a@." String.pr (Expr.to_string expr);
        assert false)
let get_model_fixedpoint =
  Logger.log_block2 "Z3Interface.get_model_fixedpoint" get_model_fixedpoint

let solve_fixedpoint solver hccs =
  let fixed = Fixedpoint.mk_fixedpoint ctx in
  let tenv = HCCS.tenv hccs in
  let args_ty ty =
    let args, ret = Type.args_ret ty in
    assert(Type.is_bool ret);
    List.map of_type args
  in
  let params = Params.mk_params ctx in
  Params.add_symbol params
    (Symbol.mk_string ctx ":engine") (Symbol.mk_string ctx solver);
  Fixedpoint.set_parameters fixed params;
  (* register pvars *)
  let () =
    let pvs =
      hccs
      |> HCCS.pvs
      |> List.unique
      |> List.map (Pair.unfold sym_of_var (TypEnv.lookup tenv >> args_ty))
    in
    List.iter
      (fun (sym, sorts) ->
         if !SMTProver.print_z3 then
           Format.printf "register pvar: %a(%a)@\n"
             String.pr (Symbol.to_string sym)
             (List.pr String.pr ", ") (List.map Sort.to_string sorts);
         FuncDecl.mk_func_decl ctx sym sorts bool_type
         |> Fixedpoint.register_relation fixed)
      pvs;
  in
  let def_exprs, goal_exprs = of_hccs tenv hccs in
  List.iter
    (fun x -> Fixedpoint.add_rule fixed x None) def_exprs; (* add rules *)
  if !SMTProver.print_z3 then
    (Format.printf "input to Z3:@,  rules: @[<hov2>%a@]@," (List.pr String.pr "@,")
       (List.map Expr.to_string def_exprs);
     Format.printf "  queries: @[<hov2>%a@]@," (List.pr String.pr "@,")
       (List.map Expr.to_string goal_exprs));
  let query goal =
    Format.printf "goal check@.";
    match Fixedpoint.query fixed goal with
    | Solver.UNSATISFIABLE ->
      Format.printf "sat@."; get_model_fixedpoint tenv fixed
    | Solver.SATISFIABLE ->
      Format.printf "unsat@."; raise SMTProver.Unsat
    | Solver.UNKNOWN ->
      Format.printf "Solver.UNKNOWN: %a@." String.pr
        (Fixedpoint.get_reason_unknown fixed);
      raise SMTProver.Unknown
  in
  let goals = Boolean.mk_or ctx goal_exprs in
  query goals
let solve_fixedpoint ?(solver="pdr") =
  Logger.log_block1 "Z3Interface.solve_fixedpoint"
    ~before:(Logger.printf "input: %a@," HCCS.pr)
    (solve_fixedpoint solver)

let z3 =
  object
    method initialize () = ()
    method finalize () = ()
    method is_valid = is_valid
    method is_sat = is_sat
    method implies = implies
    method solve = solve
  end

let _ =
  SMTProver.z3 := z3;
  PolyConstrSolver.ext_solve_z3 := solve_poly_constr;
  SMTProver.ext_solve_labeled := solve_labeled [];
  SMTProver.ext_find_min_sat := find_min_sat;
  SMTProver.ext_solve_opt := solve_opt;
  InterpProver.ext_interpolate_z3 := interpolate_z3;
  HCCSSolver.ext_solve_duality := solve_fixedpoint ~solver:"duality";
  HCCSSolver.ext_solve_pdr := solve_fixedpoint ~solver:"pdr"
