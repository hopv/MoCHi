open Util
open Combinator
open Term

(** @todo elim unit first
    @todo add theories for true, false, nil, cons, len *)

(** {6 Functions for CSIsat formulas} *)

let csisat_unit = CsisatAst.Application("unit", [])
let csisat_true = CsisatAst.Application("true", [])
let csisat_false = CsisatAst.Application("false", [])
let csisat_tuple ts = CsisatAst.Application("tuple", ts)
(* this encoding is not OK
   input1: x = tuple(true(), true(), true())
   input2: x = tuple(y, z, false())
   has an interpolant but cannot be found
*)

let list_conj = function
  | [] -> CsisatAst.True
  | [p] -> p
  | fms -> CsisatAst.And(fms)
let list_disj = function
  | [] -> CsisatAst.False
  | [p] -> p
  | fms -> CsisatAst.Or(fms)

let fv = CsisatAstUtil.get_var >> List.map (fun (CsisatAst.Variable id) -> id)

let simplify_expr expr =
  if !InterpProver.interp_simplify then CsisatAstUtil.simplify_expr expr else expr
let simplify_pred p =
  if !InterpProver.interp_simplify then CsisatAstUtil.simplify p else p
let integer_heuristic p =
  if !InterpProver.csisat_use_integer_heuristic && !InterpProver.interp_simplify
  then CsisatAstUtil.integer_heuristic p
  else p

(** Use this instead of CsisatLIUtils.round_coeff, which
    translates "x = true () && ... 0.5 ..." to
    a formula like "2 * x = true () && ...1..."
    because CSIsat considers "x" an integer variable? *)
let rec round_coeff p =
  match p with
  | CsisatAst.True -> CsisatAst.True
  | CsisatAst.False -> CsisatAst.False
  | CsisatAst.And(ps) -> CsisatAst.And(List.map round_coeff ps)
  | CsisatAst.Or(ps) -> CsisatAst.Or(List.map round_coeff ps)
  | CsisatAst.Not(p) -> CsisatAst.Not(round_coeff p)
  | CsisatAst.Eq(_, _) | CsisatAst.Lt(_, _) | CsisatAst.Leq(_, _) ->
    (* apply this to only atoms *)
    CsisatLIUtils.round_coeff p
  | _ -> assert false

let is_sat_csisat p =
  try
    p
    |> CsisatAstUtil.simplify
    |> case [(=) CsisatAst.True, (fun _ -> true);
             (=) CsisatAst.False, (fun _ -> false);
             CsisatAstUtil.is_conj_only, CsisatNelsonOppen.is_liuif_sat;
             (fun _ -> true), CsisatSatPL.is_sat]
  with
  | CsisatAst.SAT_FORMULA _ -> assert false(*@todo*)
  | _ -> assert false
let imply_csisat p1 p2 =
  CsisatAst.And [p1; CsisatAst.Not p2]
  |> CsisatAstUtil.simplify
  |> is_sat_csisat
  |> not
let dnf_csisat p = if !InterpProver.interp_simplify then CsisatAstUtil.dnf p else p

(* without this
   -6*x2 <= -12 && -1. * x2 <= -2. && 8 * x2 <= 16 may be translated to
   -6*x2 <= -12 && 0 * x2 <= -1 && 8 * x2 <= 16 *)
let interpolate_round_coeff ip p1 p2 = ip p1 p2 |> round_coeff
let interpolate_check ip p1 p2 =
  let interp = ip p1 p2 in
  if not (imply_csisat p1 interp &&
          imply_csisat interp (CsisatAst.Not p2)) then
    begin
      Format.printf
        "wrong interpolant: %a@,"
        String.pr (CsisatAstUtil.print_pred interp);
      assert false
    end;
  interp

let theory =
  [CsisatAst.Not(CsisatAst.Eq(CsisatAst.Application("true", []),
                              CsisatAst.Application("false", [])))]
(*
  forall x, y.
  CsisatAst.Not(CsisatAst.Eq(CsisatAst.Application("nil", []),
                             CsisatAst.Application("cons", [x; y])));
  forall x. len x >= 0
*)

let interpolate_csisat p1 p2 =
  try
    let p1 =
      if !InterpProver.csisat_use_theory
      then CsisatAst.And(p1 :: theory)
      else p1
    in
    CsisatInterpolate.interpolate_with_proof p1 p2
  with
  | CsisatAst.SAT | CsisatAst.SAT_FORMULA(_) -> raise InterpProver.Unknown
  | Failure(msg) ->
    Logger.printf "csisat error: %a@," String.pr msg;
    raise InterpProver.Unknown(*assert false*)
  | exc ->
    Format.printf
      "@[<v>a CSIsat exception raised when interpolating %a and %a:@,  %s@]"
      String.pr (CsisatAstUtil.print_pred p1)
      String.pr (CsisatAstUtil.print_pred p2)
      (Printexc.to_string exc);
    assert false
let interpolate_csisat =
  Logger.log_block2 "CSIsatInterface.interpolate_csisat" interpolate_csisat

let interpolate_log interpolate p1 p2 = interpolate p1 p2
let interpolate_log =
  Logger.log_block3
    ~before:(fun _ p1 p2 ->
        Logger.printf2
          "@[<v>input1: %a@ input2: %a@ @]"
          String.pr (CsisatAstUtil.print_pred p1)
          String.pr (CsisatAstUtil.print_pred p2))
    ~after:(CsisatAstUtil.print_pred >> Logger.printf "output: %a" String.pr)
    "CSIsatInterface.interpolate_log"
    interpolate_log

let interpolate_simplify interpolate p1 p2 =
  interpolate p1 p2
  |> simplify_pred
  |> sef (CsisatAstUtil.print_pred
          >> Logger.printf "after simplification: %a@," String.pr)
  |> dnf_csisat
  (* this may cause a stack overflow error *)
  |> sef (CsisatAstUtil.print_pred
          >> Logger.printf "after dnf conversion: %a@," String.pr)
let interpolate_simplify =
  Logger.log_block3 "CSIsatInterface.interpolate_simplify" interpolate_simplify

(** {6 Functions for formula conversion} *)

let of_term =
  CunTerm.fold
    (object
      method fvar x rs =
        if rs = []
        then CsisatAst.Variable(Idnt.serialize x)
        else CsisatAst.Application(Idnt.serialize x, rs)
      method funit () = csisat_unit
      method ftrue () = csisat_true
      method ffalse () = csisat_false
      method fint n = CsisatAst.Constant(float_of_int n)
      method fbigint n = CsisatAst.Constant(Big_int_Z.float_of_big_int n)
      method frational _ _ = assert false
      method freal f = CsisatAst.Constant(f)
      method fstring _ = assert false
      method fneg _ r = CsisatAst.Coeff(-1.0, r) |> simplify_expr
      method fadd _ r1 r2 = CsisatAst.Sum([r1; r2]) |> simplify_expr
      method fsub _ r1 r2 =
        CsisatAst.Sum([r1; CsisatAst.Coeff(-1.0, r2)]) |> simplify_expr
      method fmul _ r1 r2 =
        match r1, r2 with
        | CsisatAst.Constant(f), r | r, CsisatAst.Constant(f) ->
          CsisatAst.Coeff(f, r) |> simplify_expr
        | _, _ ->
          Format.eprintf
            "@[<v>[CSIsat] nonlinear expression not supported: %a * %a@,@]"
            String.pr (CsisatAstUtil.print_expr r1)
            String.pr (CsisatAstUtil.print_expr r2);
          if false then
            assert false
          else
            CsisatAst.Variable(Idnt.(serialize @@ new_var ()))
      method fdiv _ r1 r2 =
        match r2 with
        | CsisatAst.Constant(f) ->
          CsisatAst.Coeff(1.0 /. f, r1) |> simplify_expr
        | _ ->
          Format.printf
            "@[<v>nonlinear expression not supported: %a / %a@,@]"
            String.pr (CsisatAstUtil.print_expr r1)
            String.pr (CsisatAstUtil.print_expr r2);
          assert false
      method fmax _ r1 r2 = assert false
      method fmin _ r1 r2 = assert false
      method fmod r1 r2 = assert false
      method ftuple _ rs = csisat_tuple rs
      method fproj _ _ _ = assert false
      method fkon _ _ _ = assert false
      method faccessor _ _ _ _ = assert false
      method fufun _ _ _ = assert false
      method fsempty ty = assert false
      method fsadd ty r1 r2 = assert false
      method fsunion ty r1 r2 = assert false
      method fsintersect ty r1 r2 = assert false
      method fsdiff ty r1 r2 = assert false
      method fscomplement ty r = assert false
      method farray n rs = assert false
      method faget a n = assert false
      method faset a n m e = assert false
      method fcoerce ty t = assert false
      method fformula phi = assert false
    end)

let of_atom =
  CunAtom.fold
    (object
      method fvar x [] = (**@todo*)
        CsisatAst.Eq(CsisatAst.Variable(Idnt.serialize x), csisat_true)
      method feq ty t1 t2 = CsisatAst.Eq(of_term t1, of_term t2)
      method fneq ty t1 t2 =
        CsisatAst.Not(CsisatAst.Eq(of_term t1, of_term t2))
      method flt ty t1 t2 = CsisatAst.Lt(of_term t1, of_term t2)
      method fgt ty t1 t2 = CsisatAst.Lt(of_term t2, of_term t1)
      method fleq ty t1 t2 = CsisatAst.Leq(of_term t1, of_term t2)
      method fgeq ty t1 t2 = CsisatAst.Leq(of_term t2, of_term t1)
      method fdivides n t = assert false
      method frecognizer ty x t1 = assert false
      method fsmem ty e s = assert false
      method fssubset ty s1 s2 =  assert false
      method fterm c ts = assert false
    end)

let of_formula =
  Formula.fold
    (object
      method fatom = of_atom
      method ftrue () = CsisatAst.True
      method ffalse () = CsisatAst.False
      method fnot s = CsisatAst.Not(s)
      method fand s1 s2 = simplify_pred (CsisatAst.And([s1; s2]))
      method for_ s1 s2 = simplify_pred (CsisatAst.Or([s1; s2]))
      method fimply s1 s2 =
        simplify_pred (CsisatAst.Or([CsisatAst.Not(s1); s2]))
      method fiff s1 s2 = assert false
      method fforall _ _ = assert false
      method fexists _ _ = assert false
    end)
let of_formula =
  Formula.elim_imply_iff
  >> Formula.map_atom CunAtom.elim_beq_bneq
  >> Formula.map_atom CunAtom.elim_neq
  >> Formula.map_atom (CunAtom.elim_gt >> Formula.of_atom)
  >> Formula.map_atom (CunAtom.elim_geq >> Formula.of_atom)
  >> of_formula
  >> integer_heuristic
let of_formula = Logger.log_block1 "CSIsatInterface.of_formula" of_formula

let rec term_of s =
  match s with
  | CsisatAst.Constant(f) ->
    if !InterpProver.csisat_int_mode
    then IntTerm.make (int_of_float f), Type.mk_int
    else RealTerm.make f, Type.mk_real
  | CsisatAst.Variable(id) ->
    Term.mk_var (Idnt.deserialize id),
    if !InterpProver.csisat_int_mode then Type.mk_int else Type.mk_real
  | CsisatAst.Application(_, _) when s = csisat_unit ->
    UnitTerm.make, Type.mk_unit
  | CsisatAst.Application(_, _) when s = csisat_true ->
    Formula.term_of Formula.mk_true, Type.mk_bool
  | CsisatAst.Application(_, _) when s = csisat_false ->
    Formula.term_of Formula.mk_false, Type.mk_bool
  | CsisatAst.Sum(ss) ->
    let ty' =
      if !InterpProver.csisat_int_mode
      then Type.mk_int
      else Type.mk_real
    in
    ss
    |> List.map (fun s -> let t, ty = term_of s in assert (ty = ty'); t)
    |> IntTerm.sum,
    ty'
  | CsisatAst.Coeff(f, s) ->
    if !InterpProver.csisat_int_mode then
      let t, ty = term_of s in
      assert (ty = Type.mk_int);
      IntTerm.mul (IntTerm.make (int_of_float f)) t, Type.mk_int
    else
      let t, ty = term_of s in
      assert (ty = Type.mk_real);
      RealTerm.mul (RealTerm.make f) t, Type.mk_real
  | _ -> assert false

let rec formula_of = function
  | CsisatAst.True -> Formula.mk_true
  | CsisatAst.False -> Formula.mk_false
  | CsisatAst.And(ps) -> Formula.band (List.map formula_of ps)
  | CsisatAst.Or(ps) -> Formula.bor (List.map formula_of ps)
  | CsisatAst.Not(p) -> Formula.bnot (formula_of p)
  | CsisatAst.Eq(s1, s2) ->
    let t1, ty1 = term_of s1 in
    let t2, ty2 = term_of s2 in
    if Type.is_unit ty1 ||(**@todo why not && *) Type.is_unit ty2 then
      Formula.eq Type.mk_unit t1 t2
    else if Type.is_bool ty1 ||(*@todo why not && *) Type.is_bool ty2 then
      BoolFormula.eq t1 t2
    else if !InterpProver.csisat_int_mode then
      begin
        assert (Type.is_int ty1 && Type.is_int ty2);
        IntFormula.eq t1 t2
      end
    else
      begin
        assert (Type.is_real ty1 && Type.is_real ty2);
        Formula.eq Type.mk_real t1 t2
      end
  | CsisatAst.Lt(s1, s2) ->
    let t1, ty1 = term_of s1 in
    let t2, ty2 = term_of s2 in
    if !InterpProver.csisat_int_mode then
      begin
        assert (ty1 = Type.mk_int && ty2 = Type.mk_int);
        IntFormula.lt t1 t2
      end
    else
      begin
        assert (ty1 = Type.mk_real && ty2 = Type.mk_real);
        NumFormula.lt Type.mk_real t1 t2
      end
  | CsisatAst.Leq(s1, s2) ->
    let t1, ty1 = term_of s1 in
    let t2, ty2 = term_of s2 in
    if !InterpProver.csisat_int_mode then
      begin
        assert (ty1 = Type.mk_int && ty2 = Type.mk_int);
        IntFormula.leq t1 t2
      end
    else
      begin
        assert (ty1 = Type.mk_real && ty2 = Type.mk_real);
        NumFormula.leq Type.mk_real t1 t2
      end
  | _ -> assert false

let interpolate_wrap interpolate phi1 phi2 =
  (phi1, phi2)
  |> Pair.lift ((if !InterpProver.interp_simplify then CunFormula.simplify else id)
                >> of_formula >> simplify_pred)
  |> Pair.fold interpolate
  |> formula_of
let interpolate_wrap =
  Logger.log_block3
    "CSIsatInterface.interpolate_wrap"
    ~after:(Logger.printf "output: %a" Formula.pr)
    interpolate_wrap

(** {6 Functions for FPAT formulas} *)

let imply phi1 phi2 =
  let oldih = !InterpProver.csisat_use_integer_heuristic in
  Formula.band [phi1; Formula.bnot phi2]
  |> sef (fun _ -> InterpProver.csisat_use_integer_heuristic := false(*@todo*))
  |> of_formula
  |> sef (fun _ -> InterpProver.csisat_use_integer_heuristic := oldih)
  |> CsisatAstUtil.simplify
  |> is_sat_csisat
  |> not
let imply = SMTProver.imply_quick imply
let iff t1 t2 = SMTProver.iff imply
let is_sat = of_formula >> is_sat_csisat

let interpolate0 ?(generalize = false) =
  interpolate_csisat
  |> interpolate_log
  |> interpolate_round_coeff
  |> interpolate_simplify
  |> interpolate_wrap
  |> (if generalize then GeneralizingInterpProver.interpolate else id)

let interpolate ?(generalize = false) p =
  interpolate0 ~generalize:generalize
  |> InterpProver.interpolate_quick
  |> (if !InterpProver.interp_simplify
      then InterpProver.interpolate_simplify ~qelim:QelimBody.elim_int_vars_full
      else id)
  |> CheckInterpProver.interpolate
  |> InterpProver.interpolate_log
  |> InterpProver.interpolate_fresh p

let _ =
  InterpProver.ext_interpolate_csisat0 := interpolate0;
  InterpProver.ext_interpolate_csisat := interpolate;
  InterpProver.ext_interpolate_csisat_gen := interpolate ~generalize:true
