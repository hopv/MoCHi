open Util
open Combinator

(** An integer and boolean HCCS solver via reduction to integer HCCS solving *)

let rec encode_type ty =
  if Type.is_unit ty then Type.mk_unit
  else if Type.is_bool ty then Type.mk_int
  else if Type.is_int ty then Type.mk_int
  else if Type.is_fun ty then
    Type.let_fun ty
      (fun ty1 ty2 -> Type.mk_fun [encode_type ty1; encode_type ty2])
  else begin
    Logger.printf "ty: %a@," Type.pr ty;
    if true then ty (*Type.mk_int*) else assert false
  end
let encode_type = Logger.log_block1 "EncBoolHCCSSolver.encode_type" encode_type

let encode_term true_as_pos =
  CunTerm.fold_op
    (object
      method fvar x ts = Term.mk_app (Term.mk_var x) ts
      method fcon c =
        if c = Const.True then
          if true_as_pos then IntTerm.one(*@todo*) else IntTerm.one
        else if c = Const.False then
          if true_as_pos then IntTerm.zero(*@todo*) else IntTerm.zero
        else Term.mk_const c
      method fuop = NumTerm.mk_uop
      method fbop = NumTerm.mk_bop
      method fformula phi = assert false
    end)

let encode_atom true_as_pos =
  CunAtom.fold_brel
    (object
      method fvar x [] =
        if true_as_pos then IntFormula.gt (Term.mk_var x) IntTerm.zero
        else IntFormula.eq (Term.mk_var x) IntTerm.one
      method fbrel c t1 t2 =
        match c with
        | Const.Eq(ty) when Type.is_unit ty || Type.is_bool ty ->
          assert false
        | Const.Neq(ty) when Type.is_unit ty || Type.is_bool ty ->
          assert false
        | _ ->
          Formula.mk_brel c
            (encode_term true_as_pos t1)
            (encode_term true_as_pos t2)
      method fdivides n t1 = IntFormula.divides n (encode_term true_as_pos t1)
      method fterm c ts =
        if true_as_pos then
          IntFormula.gt
            (Term.mk_app (Term.mk_const c)
               (List.map (encode_term true_as_pos) ts))
            IntTerm.zero
        else
          IntFormula.eq
            (Term.mk_app (Term.mk_const c)
               (List.map (encode_term true_as_pos) ts))
            IntTerm.one
    end)

let encode_formula true_as_pos =
  Formula.map_atom CunAtom.elim_beq_bneq
  >> Formula.map_atom (encode_atom true_as_pos)

let encode_head true_as_pos =
  HornClause.head_map
    id
    (Option.map (PredVar.map_type encode_type))
    (encode_formula true_as_pos)

let encode_atm true_as_pos atm =
  atm
  |> Pva.args_of
  |> List.map (Pair.map (encode_term true_as_pos) encode_type)
  |> Pva.make (Pva.idnt_of atm)

let encode_body true_as_pos =
  HornClause.body_map
    (List.map (encode_atm true_as_pos))
    (encode_formula true_as_pos)

let encode true_as_pos =
  List.map (HornClause.map (encode_head true_as_pos) (encode_body true_as_pos))

let decode_tsub (b, (t, ty)) =
  assert (Type.is_bool ty);
  b,
  ((if t |> Formula.of_term |> Formula.is_true then IntTerm.one
    else if t |> Formula.of_term |> Formula.is_false then IntTerm.zero
    else assert false),
   Type.mk_bool)

let decode_ttsub = List.map decode_tsub >> TypTermSubst.tsub_of

let decode_formula true_as_pos bool_vars phi =
  if bool_vars = [] then phi
  else
    bool_vars
    |> TypTermSubst.bool_valuations
    |> List.map
      (fun ttsub ->
         if true_as_pos then
           let tmp =
             List.map (fun (x, (t, _)) -> x, Idnt.new_var (), t) ttsub
           in
           phi
           |> Formula.rename (List.map (fun (x, y, _) -> x, y) tmp)
           |> flip
             List.cons
             (List.map
                (fun (_, x, t) ->
                   if t |> Formula.of_term |> Formula.is_true then
                     IntFormula.gt (Term.mk_var x) IntTerm.zero
                   else if t |> Formula.of_term |> Formula.is_false then
                     IntFormula.leq (Term.mk_var x) IntTerm.zero
                   else assert false)
                tmp)
           |> Formula.band
           |> Formula.exists (List.map (fun (_, x, _) -> x, Type.mk_int) tmp)
           |> Qelim.integer_qelim_dyn
           |> flip List.cons [Formula.of_ttsub ttsub]
           |> Formula.band
         else
           [Formula.subst (decode_ttsub ttsub) phi; Formula.of_ttsub ttsub]
           |> Formula.band)
    |> Formula.bor
    |> FormulaSimplifier.simplify

let bool_vars tenv =
  List.filter_map
    (fun (x, ty) -> if ty = Type.mk_bool then Some(x) else None)
    tenv

let decode_sol true_as_pos ptenv =
  List.map
    (fun (pv, (enc_tenv, phi)) ->
       let tenv =
         List.assoc_fail
           pv ptenv
           ~on_failure:(fun () ->
               Format.printf
                 "EncBoolHCCSSolver.decode_sol:@,%a is not found@,tenv: %a@,"
                 Idnt.pr pv TypEnv.pr ptenv)
         |> Type.args_of
         |> List.map2 (fun (x, _) ty -> x, ty) enc_tenv
       in
       pv, (tenv, decode_formula true_as_pos (bool_vars tenv) phi))

(* val solve : HCCSSolver.t -> HCCSSolver.t *)
let solve true_as_pos (solver : HCCSSolver.t) hcs =
  hcs
  |> encode true_as_pos
  |> Logger.pprintf "encoded HCCS:@,  %a@," HCCS.pr
  |> solver
  |> decode_sol true_as_pos (HCCS.tenv hcs)
let solve =
  Logger.log_block3 "EncBoolHCCSSolver.solve"
    ~after:(Logger.printf "solution:@,  %a@," PredSubst.pr)
    solve
