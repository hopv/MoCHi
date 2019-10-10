open Util
open Combinator

(** Refinement type judgments *)

let formula_of c ts t =
  match c, ts with
  | Const.Undef, [] ->
     assert false
  | Const.Bot, [] ->
     Formula.mk_true
  | Const.Top, [] ->
     Formula.mk_true

  | Const.BinTrue(ty), [t1; t2] ->
     NumFormula.eq Type.mk_bool t BoolTerm.mk_true
  | Const.BinFalse(ty), [t1; t2] ->
     NumFormula.eq Type.mk_bool t BoolTerm.mk_false
  | c, [t1; t2] when Const.is_brel c ->
     NumFormula.eq Type.mk_bool t (Atom.mk_brel c t1 t2 |> Atom.term_of)

  | Const.Neg(ty), [t0] ->
     NumFormula.eq ty t (NumTerm.neg ty t0)
  | Const.Add(ty), [t1; t2] ->
     NumFormula.eq ty t (NumTerm.add ty t1 t2)
  | Const.Sub(ty), [t1; t2] ->
     NumFormula.eq ty t (NumTerm.sub ty t1 t2)
  | Const.Mul(ty), [t1; t2] ->
     NumFormula.eq ty t (NumTerm.mul ty t1 t2)
  | Const.Div(ty), [t1; t2] ->
     NumFormula.eq ty t (NumTerm.div ty t1 t2)
  | Const.Max(ty), [t1; t2] ->
     NumFormula.eq ty t (NumTerm.max ty t1 t2)
  | Const.Min(ty), [t1; t2] ->
     NumFormula.eq ty t (NumTerm.min ty t1 t2)

  | Const.UFun(ty, id), [] ->
     Formula.mk_true
  | Const.Event(id), [_] ->
     Formula.mk_true

  | Const.Unit, [] ->
     NumFormula.eq Type.mk_unit t UnitTerm.make

  | Const.True, [] ->
     NumFormula.eq Type.mk_bool t BoolTerm.mk_true
  | Const.False, [] ->
     NumFormula.eq Type.mk_bool t BoolTerm.mk_false
  | Const.Not, [t0] ->
     NumFormula.eq Type.mk_bool
                   t
                   (Formula.bnot (Formula.of_term t0) |> Formula.term_of)
  | Const.And, [t1; t2] ->
     NumFormula.eq (Type.mk_bool) t
                   (Formula.band [Formula.of_term t1; Formula.of_term t2]
                    |> Formula.term_of)
  | Const.Or, [t1; t2] ->
     NumFormula.eq (Type.mk_bool) t
                   (Formula.bor [Formula.of_term t1; Formula.of_term t2]
                    |> Formula.term_of)
  | Const.Imply, [t1; t2] ->
     NumFormula.eq (Type.mk_bool) t
                   (Formula.imply (Formula.of_term t1) (Formula.of_term t2)
                    |> Formula.term_of)
  | Const.Iff, [t1; t2] ->
     NumFormula.eq (Type.mk_bool) t
                   (Formula.mk_iff (Formula.of_term t1) (Formula.of_term t2)
                    |> Formula.term_of)

  | Const.Int(n), [] -> IntFormula.eq t (IntTerm.make n)
  | Const.RandBool, [_] -> Formula.mk_true
  | Const.RandInt, [_] -> Formula.mk_true
  | Const.RandReal, [_] -> Formula.mk_true
  | Const.BitNot, [t0] ->
     assert false(*raise (Global.NotImplemented "RefTypJudge.formula_of")*)
  | Const.Mod, [t1; t2]
  | Const.BitShiftLeft, [t1; t2]
  | Const.BitShiftRight, [t1; t2]
  | Const.BitAnd, [t1; t2]
  | Const.BitOr, [t1; t2]
  | Const.BitXor, [t1; t2] ->
     assert false(*raise (Global.NotImplemented "RefTypJudge.formula_of")*)

  | Const.Real(f), [] ->
     NumFormula.eq Type.mk_real t (RealTerm.make f)
  | Const.FRsq, [t0]
  | Const.FRcp, [t0]
  | Const.FLog2, [t0]
  | Const.FExp2, [t0]
  | Const.FClamp, [t0] ->
     assert false(*raise (Global.NotImplemented "RefTypJudge.formula_of")*)
  | Const.FPow, [t1; t2] ->
     assert false(*raise (Global.NotImplemented "RefTypJudge.formula_of")*)

  | Const.String(s), [] ->
     NumFormula.eq Type.mk_string t (StringTerm.make s)

  | Const.Nil(ty), [] ->
     assert false(*raise (Global.NotImplemented "RefTypJudge.formula_of")*)
  | Const.Cons(ty), [t1; t2] ->
     assert false(*raise (Global.NotImplemented "RefTypJudge.formula_of")*)

  | Const.App, _
  | Const.Flip, _
  | Const.Comp, _
  | Const.Tlu, _
  | Const.FShift, _ ->
     assert false(*raise (Global.NotImplemented "RefTypJudge.formula_of")*)
  | _ ->
     Format.printf
       "%s@,%a@,%a@,"
       (Const.string_of c)
       (List.pr Term.pr ",") ts
       Term.pr t;
     assert false(*raise (Global.NotImplemented "RefTypJudge.formula_of")*)


let rty_of_const c =
  match c with
  | Const.Event(id) when id = Const.event_fail ->
     RefType.mk_fun
       [RefType.Base(Idnt.new_var (), TypConst.Unit, Formula.mk_false);
        RefType.answer_type]
  | Const.Bot ->
     RefType.Bot
  | Const.Top ->
     RefType.Top
  | _ ->
     let args, ret = Type.args_ret (Const.type_of c) in
     let args = List.map RefType.of_simple_type args in
     let ts =
       List.map
         (function
           | RefType.Base(x, _, _) -> Term.mk_var x
           | _ -> Term.new_var ()(*@todo*))
         args
     in
     let RefType.Base(x, bty, _) = RefType.of_simple_type ret in
     RefType.mk_fun
       (args @ [RefType.Base(x, bty, formula_of c ts (Term.mk_var x))])

let rec subtype rty1 rty2 =
  match rty1, rty2 with
  | RefType.Bot, _
  | _, RefType.Top ->
     []
  | RefType.Base(x1, bty1, t1), RefType.Base(x2, bty2, t2)
       when bty1 = bty2 ->
     [Formula.imply t1 (Formula.subst [x2, Term.mk_var x1] t2)]
  | RefType.Fun([RefType.Base(x1, bty1, t1), rty1']),
    RefType.Fun([RefType.Base(x2, bty2, t2), rty2'])
       when bty1 = bty2 ->
     [Formula.imply
        t2
        (Formula.band
           (Formula.subst [x1, Term.mk_var x2] t1
            :: subtype (RefType.subst [x1, Term.mk_var x2] rty1') rty2'))]
  | RefType.Fun([rty11, rty12]), RefType.Fun([rty21, rty22]) ->
     subtype rty21 rty11
     @ subtype rty12 rty22
  | _ ->
     Format.printf
       "@[<v>rty1:%a@,rty2:%a@]@,"
       RefType.pr rty1
       RefType.pr rty2;
     assert false

let apptype rty1 rty2 t =
  match rty1 with
  | RefType.Fun([rty11, rty12]) ->
     subtype rty2 rty11,
     (match rty11 with
      | RefType.Base(x, _, _) ->
         (** @todo t must be a base value *)
         RefType.subst [x, t] rty12
      | _ ->
         rty12)
  | _ -> assert false

let constrs_of_term env =
  Term.para
    (object
        method fvar x =
          let Idnt.V(id) = x in
          let rty =
            List.assoc_fail
              ~on_failure:
              (fun () -> Format.printf "%a@,"String.pr id)
              id env
          in
          let rty' =
            match rty with
            | RefType.Base(y, c, _) ->
               RefType.Base
                 (y, c,
                  Formula.eq (Type.mk_const c)
                             (Term.mk_var y)
                             (Term.mk_var x))
            | _ -> rty
          in
          [], rty'
        method fcon c =
          [], rty_of_const c
        method fapp _ (constrs1, rty1) t2 (constrs2, rty2) =
          let constrs, rty = apptype rty1 rty2 t2 in
          constrs1 @ constrs2 @ constrs, rty
        method fbin b x _ r = assert false
      end)

let constrs_of_env env =
  env
  |> List.filter (fun (_, rty) -> RefType.is_base rty)
  |> List.map
       (fun (x, rty) ->
        let y, t = RefType.pred_of_base rty in
        Formula.subst [y, Term.mk_var (Idnt.make x)] t)

let constr_of_fdef env fdef =
  let env', rty =
    RefType.env_ty
      fdef.Fdef.args
      (List.assoc_fail
         ~on_failure:(fun () -> Format.printf "%a@," String.pr fdef.Fdef.name)
         fdef.Fdef.name
         env)
  in
  let env'' = env' @ env in
  let guard = fdef.Fdef.guard in
  let body = fdef.Fdef.body in
  let constrs, rty' = constrs_of_term env'' body in
  Formula.imply
    (Formula.band (guard :: constrs_of_env env''))
    (Formula.band (constrs @ subtype rty' rty))
let mk_temp_env prog =
  List.map
    (fun f ->
     f.Fdef.name,
     RefType.mk_template
       (TypEnv.lookup prog.Prog.types)
       (Idnt.make f.Fdef.name))
    prog.Prog.fdefs

let constr_of_prog prog =
  let env = mk_temp_env prog in
  prog.Prog.fdefs
  |> List.map (constr_of_fdef env)
  |> Formula.band


(*

let init_env =
  (A("arraysize", TypeSchema.type_schema_of_arraysize))::
  (A("sub",       TypeSchema.type_schema_of_sub))::
  (A("update",     TypeSchema.type_schema_of_update))::
  (A("alloc",     TypeSchema.type_schema_of_alloc))::
(**)
  (A("abs", TypeSchema.type_schema_of_abs))::
  (A("mid", TypeSchema.type_schema_of_mid))::
(**)
  (A("type_of_bcopy",   TypeSchema.type_schema_of_bcopy))::
  (A("type_of_dotprod", TypeSchema.type_schema_of_dotprod))::
(*  (A("type_of_bsearch", TypeSchema.type_schema_of_bsearch))::*)
  (A("type_of_queens", TypeSchema.type_schema_of_queens))::
  (A("combine", TypeSchema.type_schema_of_combine))::
  (A("ordered", TypeSchema.type_schema_of_ordered))::
  []

let con_env =
  ("(~-)",  TypeSchema.type_schema_of_unary_minus)::
  ("(+)",   TypeSchema.type_schema_of_binop BinOp.Add)::
  ("(-)",   TypeSchema.type_schema_of_binop BinOp.Sub)::
  ("(*)",   TypeSchema.type_schema_of_binop BinOp.Mul)::
  ("(/)",   TypeSchema.type_schema_of_binop BinOp.Div)::
  ("(mod)", TypeSchema.type_schema_of_binop BinOp.Mod)::
  ("(=)",   TypeSchema.type_schema_of_binrel BinRel.Equal)::
  ("(<)",   TypeSchema.type_schema_of_binrel BinRel.Less)::
  ("(<=)",  TypeSchema.type_schema_of_binrel BinRel.LessEqual)::
  ("(>)",   TypeSchema.type_schema_of_binrel BinRel.Greater)::
  ("(>=)",  TypeSchema.type_schema_of_binrel BinRel.GreaterEqual)::
  ("(<>)",  TypeSchema.type_schema_of_binrel BinRel.NotEqual)::
  []

let kon_env =
  ("Unit",  TypeSchema.type_schema_of_unit)::
  ("True",  TypeSchema.type_schema_of_true)::
  ("False", TypeSchema.type_schema_of_false)::
  ("None",  TypeSchema.type_schema_of_none)::
  ("Some", TypeSchema.type_schema_of_some)::
  ("Nil",   TypeSchema.type_schema_of_nil)::
  ("Cons",  TypeSchema.type_schema_of_cons)::
  ("SNil",   TypeSchema.type_schema_of_snil)::
  ("SCons",  TypeSchema.type_schema_of_scons)::
  ("ONil",   TypeSchema.type_schema_of_onil)::
  ("OCons",  TypeSchema.type_schema_of_ocons)::
  ("QNil",   TypeSchema.type_schema_of_qnil)::
  ("QCons",  TypeSchema.type_schema_of_qcons)::
  ("INil",   TypeSchema.type_schema_of_inil)::
  ("ICons",  TypeSchema.type_schema_of_icons)::
  []

let type_schema_of_con id =
  try
    let n = int_of_string id in
    TypeSchema.type_schema_of_int n
  with Failure _ ->
    (try
      List.assoc id con_env
    with Not_found ->
      raise (Global.Semantic_error ("unbound constant "^id)))

let type_schema_of_kon id =
  try
    List.assoc id kon_env
  with Not_found ->
    raise (Global.Semantic_error ("unbound constructor "^id))

let rec type_schema_of_var id env =
  match env with
    [] ->
      raise (Global.Semantic_error ("unbound variable "^id))
  | (A(id', sigma))::_ when id = id' -> sigma
  | _::env' -> type_schema_of_var id env'

(*let dom env =
  List.rev (List.filter_map (function A(id, _) -> Some(id) | B(_) -> None) env)*)

let dom_wo_fun env =
  List.rev (List.filter_map (function A(id, sigma) when not (TypeSchema.is_fun sigma) -> Some(id) | _ -> None) env)

let assign_pred_var sol env =
  List.map
    (function
      (A(id, sigma)) ->
        A(id, TypeSchema.assign_pred_var sol sigma)
    | (B(phi)) -> B(phi))
    env

*)
