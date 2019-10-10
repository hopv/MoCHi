open Util
open Combinator

(** Simple type inference *)

let cgen_mlexp env exp ty = assert false
let cgen_mlexp env exp ty =
  Logger.log_block3 "SimTypInfer.cgen_mlexp" cgen_mlexp env exp ty

let infer_mlexp env exp =
  let ty = Type.new_var () in
  let constr, exp' = cgen_mlexp env exp ty in
  let tsub = constr |> Type.unify in
  TypEnv.subst tsub env,
  Term.subst_tvars tsub exp,
  Type.subst tsub ty
let infer_mlexp env exp =
  Logger.log_block2 "SimTypInfer.infer_mlexp" infer_mlexp env exp

let unify ty1 ty2 =
  assert (ty1 <> Type.mk_top && ty2 <> Type.mk_top);
  if ty1 = ty2 then []
  else
    begin
      Logger.printf2 "adding constraint %a = %a@," Type.pr ty1 Type.pr ty2;
      [ty1, ty2]
    end

let cgen_term f_formula env t ty =
  CunTerm.fold
    (object
      method fvar x rs = fun env ty ->
        let ty' =
          List.assoc_fail
            ~on_failure:(fun () ->
                Format.printf
                  "SimTypInfer.cgen_term:@,%a is not found in {%a}@,"
                  Idnt.pr x
                  TypEnv.pr env)
            x
            env
        in
        let args = List.map (fun _ -> Type.new_var ()) rs in
        let constr, ts =
          List.map2 (fun r ty -> r env ty) rs args
          |> List.split
          |> Pair.map List.concat id
        in
        constr @ unify (Type.mk_fun_args_ret args ty) ty',
        Term.mk_app (Term.mk_var x) ts
      method funit () = fun env ty ->
        unify ty Type.mk_unit, UnitTerm.make
      method ftrue () = fun env ty ->
        unify ty Type.mk_bool, BoolTerm.mk_true
      method ffalse () = fun env ty ->
        unify ty Type.mk_bool, BoolTerm.mk_false
      method fint n = fun env ty ->
        unify ty Type.mk_int, IntTerm.make n
      method fbigint n = fun env ty ->
        unify ty Type.mk_int, IntTerm.of_big_int n
      method freal f = fun env ty ->
        unify ty Type.mk_real, RealTerm.make f
      method fstring s = fun env ty ->
        unify ty Type.mk_string, StringTerm.make s
      method fneg _ r1 = fun env ty ->
        let constr1, t1 = r1 env ty in
        constr1, NumTerm.neg ty t1
      method fadd _ r1 r2 = fun env ty ->
        let constr1, t1 = r1 env ty in
        let constr2, t2 = r2 env ty in
        constr1 @ constr2, NumTerm.add ty t1 t2
      method fsub _ r1 r2 = fun env ty ->
        let constr1, t1 = r1 env ty in
        let constr2, t2 = r2 env ty in
        constr1 @ constr2, NumTerm.sub ty t1 t2
      method fmul _ r1 r2 = fun env ty ->
        let constr1, t1 = r1 env ty in
        let constr2, t2 = r2 env ty in
        constr1 @ constr2, NumTerm.mul ty t1 t2
      method fdiv _ r1 r2 = fun env ty ->
        let constr1, t1 = r1 env ty in
        let constr2, t2 = r2 env ty in
        constr1 @ constr2, NumTerm.div ty t1 t2
      method fmax _ r1 r2 = fun env ty ->
        let constr1, t1 = r1 env ty in
        let constr2, t2 = r2 env ty in
        constr1 @ constr2, NumTerm.max ty t1 t2
      method fmin _ r1 r2 = fun env ty ->
        let constr1, t1 = r1 env ty in
        let constr2, t2 = r2 env ty in
        constr1 @ constr2, NumTerm.min ty t1 t2
      method fmod r1 r2 = fun env ty ->
        let constr1, t1 = r1 env Type.mk_int in
        let constr2, t2 = r2 env Type.mk_int in
        constr1 @ constr2 @ unify ty Type.mk_int, IntTerm.mk_mod t1 t2
      method fufun _ x rs = fun env ty ->
        let ty' =
          List.assoc_fail
            ~on_failure:(fun () ->
                Format.printf
                  "SimTypInfer.cgen_term:@,%a is not found in {%a}@,"
                  Idnt.pr x
                  TypEnv.pr env)
            x
            env
        in
        let args = List.map (fun _ -> Type.new_var ()) rs in
        let constr, ts =
          List.map2 (fun r ty -> r env ty) rs args
          |> List.split
          |> Pair.map List.concat id
        in
        constr @ unify (Type.mk_fun_args_ret args ty) ty',
        CunTerm.mk_ufun (x, ty') ts
      method fcoerce _ r = fun env ty ->
        let ty' = Type.new_var () in
        let constr, t = r env ty' in
        constr, CunTerm.mk_coerce (Type.mk_fun [ty'; ty]) t
      method fformula phi = fun env ty ->
        (*ty must be bool*)
        let constr, phi = f_formula env phi in
        constr @ unify ty Type.mk_bool, Formula.term_of phi
    end)
    t env ty
let cgen_term =
  Logger.log_block4 "SimTypInfer.cgen_term"
    ~before:(fun _ _ t _ -> Logger.printf "input:@, %a" Term.pr t)
    cgen_term

let cgen_atom f_formula env =
  CunAtom.fold_brel
    (object
      method fvar x ts =
        let ty =
          List.assoc_fail ~on_failure:(fun () ->
              Format.printf
                "SimTypInfer.cgen_atom:@,%a is not found in {%a}@,"
                Idnt.pr x
                TypEnv.pr env)
            x
            env
        in
        let args = List.map (fun _ -> Type.new_var ()) ts in
        let constr, ts' =
          List.map2 (cgen_term f_formula env) ts args
          |> List.split
          |> Pair.map List.concat id
        in
        constr @ unify (Type.mk_fun_args_ret args Type.mk_bool) ty,
        Atom.mk_var x ts'
      method fbrel c t1 t2 =
        let c', ty1, ty2, ret =
          (match c with
           | Const.Eq(ty) ->
             let x =
               (*if Type.is_int ty || Type.is_real ty then
                 ty
                 else*)
               Type.new_var ()
             in
             Const.Eq(x), x, x, Type.mk_bool
           | Const.Neq(ty) ->
             let x =
               (*if Type.is_int ty || Type.is_real ty then
                 ty
                 else*)
               Type.new_var ()
             in
             Const.Neq(x), x, x, Type.mk_bool
           | Const.Lt(ty) ->
             let x =
               (*if Type.is_int ty || Type.is_real ty then
                 ty
                 else*)
               Type.new_var ()
             in
             Const.Lt(x), x, x, Type.mk_bool
           | Const.Gt(ty) ->
             let x =
               (*if Type.is_int ty || Type.is_real ty then
                 ty
                 else*)
                 Type.new_var ()
             in
             Const.Gt(x), x, x, Type.mk_bool
           | Const.Leq(ty) ->
             let x =
               (*if Type.is_int ty || Type.is_real ty then
                 ty
                 else*)
               Type.new_var ()
             in
             Const.Leq(x), x, x, Type.mk_bool
           | Const.Geq(ty) ->
             let x =
               (*if Type.is_int ty || Type.is_real ty then
                 ty
                 else*)
               Type.new_var ()
             in
             Const.Geq(x), x, x, Type.mk_bool
           | c ->
             Logger.printf0 "unexpected error?@,";
             assert false
             (*Const.type_of c*))
        in
        let constr1, t1' = cgen_term f_formula env t1 ty1 in
        let constr2, t2' = cgen_term f_formula env t2 ty2 in
        constr1 @ constr2 @ unify ret Type.mk_bool, Atom.mk_brel c' t1' t2'
      method fdivides n t =
        let constr, t' = cgen_term f_formula env t Type.mk_int in
        constr, IntAtom.divides n t'
      method fterm c ts =
        let t = Term.mk_app (Term.mk_const c) ts in
        let constr1, t1 = cgen_term f_formula env t Type.mk_bool in
        constr1, t1 |> Atom.of_term
    end)
let cgen_atom = Logger.log_block3 "SimTypInfer.cgen_atom" cgen_atom

let rec cgen_formula env phi =
  Formula.fold
    (object
      method fatom atm = fun env ->
        let constr, atm = cgen_atom cgen_formula env atm in
        constr, Formula.of_atom atm
      method ftrue () = fun env ->
        [], Formula.mk_true
      method ffalse () = fun env ->
        [], Formula.mk_false
      method fnot r1 = fun env ->
        let constr1, phi1 = r1 env in
        constr1, Formula.bnot phi1
      method fand r1 r2 = fun env ->
        let constr1, phi1 = r1 env in
        let constr2, phi2 = r2 env in
        constr1 @ constr2, Formula.band [phi1; phi2]
      method for_ r1 r2 = fun env ->
        let constr1, phi1 = r1 env in
        let constr2, phi2 = r2 env in
        constr1 @ constr2, Formula.bor [phi1; phi2]
      method fimply r1 r2 = fun env ->
        let constr1, phi1 = r1 env in
        let constr2, phi2 = r2 env in
        constr1 @ constr2, Formula.imply phi1 phi2
      method fiff r1 r2 = fun env ->
        let constr1, phi1 = r1 env in
        let constr2, phi2 = r2 env in
        constr1 @ constr2, Formula.mk_iff phi1 phi2
      method fforall (x, _) r1 = fun env ->
        let ty = Type.new_var () in
        let constr1, phi1 = r1 ((x, ty) :: env) in
        constr1, Formula.forall [x, ty] phi1
      method fexists (x, _) r1 = fun env ->
        let ty = Type.new_var () in
        let constr1, phi1 = r1 ((x, ty) :: env) in
        constr1, Formula.exists [x, ty] phi1
    end)
    phi env
let cgen_formula = Logger.log_block2 "SimTypInfer.cgen_formula" cgen_formula

let infer_formula tenv phi =
  let tenv' =
    tenv
    @ (Formula.fvs phi @ Formula.coeffs phi @ CunFormula.ufuns_of phi
       |> List.filter (flip List.mem_assoc tenv >> not)
       |> List.unique
       |> TypEnv.of_vars)
  in
  let constr, phi' = cgen_formula tenv' phi in
  let tsub =
    try constr |> Type.unify
    with AbsTerm.CannotUnify ->
      Format.printf
        "unification error:@,  %a@,  @[<v>%a@]@,"
        (List.pr (Pair.pr Type.pr Type.pr) "@,") constr
        Formula.pr phi';
      assert false
  in
  TypEnv.subst tsub tenv', phi' |> Formula.subst_tvars tsub
let infer_formula =
  Logger.log_block2 "SimTypInfer.infer_formula"
    ~after:(Logger.printf "output:@, %a" (Pair.pr TypEnv.pr Formula.pr))
    infer_formula

let infer_formulas tenv phis =
  let tenv' =
    tenv
    @ (List.concat_map
         (fun phi ->
            Formula.fvs phi @ Formula.coeffs phi @ CunFormula.ufuns_of phi)
         phis
       |> List.filter (fun x -> not (List.mem_assoc x tenv))
       |> List.unique
       |> TypEnv.of_vars)
  in
  let ty = Type.new_var () in
  let constr, phis' =
    phis
    |> List.map (cgen_formula tenv')
    |> List.split
    |> Pair.map_fst List.concat
  in
  let tsub =
    try constr |> Type.unify
    with AbsTerm.CannotUnify ->
      Format.printf "unification error:@.  %a@." Formula.pr_list phis;
      assert false
  in
  TypEnv.subst tsub tenv',
  phis' |> List.map (Formula.subst_tvars tsub)
let infer_formulas =
  Logger.log_block2 "SimTypInfer.infer_formulas" infer_formulas

let cgen_pv env pv =
  PredVar.fold
    (fun p tenv ->
       let ty =
         List.assoc_fail
           ~on_failure:(fun () ->
               Format.printf
                 "SimTypInfer.cgen_pv:@,%a is not found in {%a}@,"
                 Idnt.pr p
                 TypEnv.pr env)
           p
           env
       in
       let args = List.map (fun _ -> Type.new_var ()) tenv in
       let constr, tenv' =
         List.map2
           (fun ty (x, _) ->
              unify ty
                (List.assoc_fail
                   ~on_failure:(fun () ->
                       Format.printf
                         "SimTypInfer.cgen_pv:@,%a is not found in {%a}@,"
                         Idnt.pr x
                         TypEnv.pr env)
                   x
                   env),
              (x, ty))
           args tenv
         |> List.split
         |> Pair.map List.concat id
       in
       constr @ unify (Type.mk_fun_args_ret args Type.mk_bool) ty,
       PredVar.make p tenv')
    pv
let cgen_pv = Logger.log_block2 "SimTypInfer.cgen_pv" cgen_pv

let cgen_pva env pva =
  Pva.fold
    (fun p tts ->
       let ty =
         List.assoc_fail
           ~on_failure:(fun () ->
               Format.printf
                 "SimTypInfer.cgen_pva:@,%a is not found in {%a}@,"
                 Idnt.pr p
                 TypEnv.pr env)
           p
           env
       in
       let args = List.map (fun _ -> Type.new_var ()) tts in
       let constr, tts' =
         List.map2
           (fun ty (t, _) ->
              cgen_term cgen_formula env t ty
              |> Pair.map_snd (flip Pair.make ty))
           args tts
         |> List.split
         |> Pair.map List.concat id
       in
       constr @ unify (Type.mk_fun_args_ret args Type.mk_bool) ty,
       Pva.make p tts')
    pva
let cgen_pva = Logger.log_block2 "SimTypInfer.cgen_pva" cgen_pva

let gen_tvar_if_unknown ty =
  if Type.is_unknown ty then Type.mk_var (Idnt.new_tvar ()) else ty

let cgen_horn_clause tenv hc =
  let tenv' =
    (hc |> HornClause.htenv_of |> List.map @@ Pair.map_snd gen_tvar_if_unknown)
    @ (hc |> HornClause.fvs |> TypEnv.of_vars)
    @ tenv
  in
  HornClause.fold
    (fun pvas phi ->
       let constr1, pvas' =
         pvas
         |> List.map (cgen_pva tenv')
         |> List.split
         |> Pair.map List.concat id
       in
       let constr2, phi' = cgen_formula tenv' phi in
       constr1 @ constr2, HornClause.mk_goal pvas' phi')
    (fun pv pvas phi ->
       let constr0, pv' = cgen_pv tenv' pv in
       let constr1, pvas' =
         pvas
         |> List.map (cgen_pva tenv')
         |> List.split
         |> Pair.map List.concat id
       in
       let constr2, phi' = cgen_formula tenv' phi in
       constr0 @ constr1 @ constr2,
       HornClause.mk_def ~tenv:(HornClause.htenv_of hc) pv' pvas' phi')
    hc
let cgen_horn_clause =
  Logger.log_block2 "SimTypInfer.cgen_horn_clause" cgen_horn_clause

let cgen_hccs tenv hcs =
  hcs
  |> List.map (cgen_horn_clause tenv)
  |> List.split
  |> Pair.map List.concat id
let cgen_hccs = Logger.log_block2 "SimTypInfer.cgen_hccs" cgen_hccs

(* type inference *)
(* tenv: constructor's type *)
let infer_hccs tenv hcs =
  let tenv' =
    tenv
    @ (hcs |> HCCS.pvs |> TypEnv.of_vars)
    @ (hcs |> HCCS.coeffs |> TypEnv.of_vars)
    @ (hcs |> HCCS.ufuns |> TypEnv.of_vars)
  in
  (*TypEnv.pr Format.std_formatter tenv';*)
  let constr, hcs' =
    hcs
    |> List.map
      (fun hc ->
         let constr, hc' = cgen_horn_clause tenv' hc in
         let gvs = TypEnv.ftvs tenv' in
         let tsub =
           try
             constr |> Type.unify ~gvs:gvs
           with AbsTerm.CannotUnify ->
             Format.printf "unification error:@.  %a@.  %a@." TypEnv.pr tenv HornClause.pr hc;
             assert false
         in
         List.filter_map
           (fun (x, ty) ->
              if List.mem x gvs then Some(Type.mk_var x, ty) else None)
           tsub,
         HornClause.subst_tvars tsub hc')
    |> List.split
    |> Pair.map List.concat id
  in
  let tsub =
    try
      constr |> Type.unify
    with AbsTerm.CannotUnify ->
      Format.printf "unification error:@.  %a@.  %a@." TypEnv.pr tenv HCCS.pr hcs;
      assert false
  in
  TypEnv.subst tsub tenv',
  HCCS.subst_tvars tsub hcs'
let infer_hccs =
  Logger.log_block2
    "SimTypInfer.infer_hccs"
    ~before:(fun _ -> Logger.printf "input:@,  %a@," HCCS.pr)
    infer_hccs
