open Util
open Combinator

(** Refinement types *)

type t =
  | Base of Idnt.t * Type.t * Formula.t
  | Fun of Idnt.t * t * t * (Idnt.t * Formula.t)

(** {6 Printers} *)

let rec pr_bind ppf (x, rty) = Format.fprintf ppf "(%a : %a)" Idnt.pr x pr rty
and pr ppf rty =
  match rty with
  | Base(x, ty, t) ->
    Format.fprintf ppf "@[<hov>";
    (if Formula.is_true t then String.pr ppf (Type.string_of ty)
     else
       Format.fprintf ppf "{%a:%s | %a}"
         Idnt.pr x (Type.string_of ty) Formula.pr t);
    Format.fprintf ppf "@]"
  | Fun(x, rty1, rty2, t) ->
    (if Formula.is_true (snd t) then
       Format.fprintf ppf "@[<hv>%a ->@ %a@]" pr_bind (x, rty1) pr rty2
     else
       Format.fprintf ppf "@[<hv>{%a:%a ->@ %a | %a}@]"
         Idnt.pr (fst t)
         pr_bind (x, rty1)
         pr rty2
         Formula.pr (snd t))

(** {6 Auxiliary constructors} *)

let answer_type = Base(Idnt.make "nu", Type.mk_answer, Formula.mk_true)
let mk_base x ty phi = Base(x, ty, phi)
let mk_fun ?(ps=[]) tys =
  match ps with
  | [] ->
    List.fold_right
      (fun (x, ty1) ty2 -> Fun(x, ty1, ty2, (Idnt.new_var(), Formula.mk_true)))
      (List.initial tys) (List.last tys |> snd)
  | _ ->
    assert (List.length tys - 1 = List.length ps);
    List.fold_right2
      (fun (x, ty1) p ty2 ->Fun (x, ty1, ty2, p))
      (List.initial tys) ps (List.last tys |> snd)
let mk_fun_ args ret =
  List.fold_right
    (fun (x, ty1, y, phi) ty2 -> Fun(x, ty1, ty2, (y, phi)))
    args ret

let mk_fun_args_ret ?(ps=[]) args ret =
  match ps with
  | [] ->
    List.fold_right
      (fun ty1 ty2 ->
         Fun(Idnt.new_var (), ty1, ty2, (Idnt.new_var(), Formula.mk_true)))
      args ret
  | _ ->
    assert(List.length args = List.length ps);
    List.fold_right2
      (fun ty1 p ty2 -> Fun(Idnt.new_var (), ty1, ty2, p) )
      args ps ret

let mk_fun_args_ret_rty ?(ps=[]) args ret =
  match ps with
  | [] ->
    List.fold_right
      (fun (x, ty1) ty2 -> Fun(x, ty1, ty2, (Idnt.new_var(), Formula.mk_true)))
      args ret
  | _ ->
    assert(List.length args = List.length ps);
    List.fold_right2 (fun (x, ty1) p ty2 ->Fun (x, ty1, ty2, p)) args ps ret

let mk_singleton ty v =
  let nv = Idnt.new_var () in
  Base(nv, ty, Formula.eq ty (Term.mk_var nv) v)

let of_simple_type =
  Type.fold
    (object
      method fvar x = mk_base (Idnt.new_var()) (Type.mk_var x) Formula.mk_true
      (*@todo*)
      method fbase tyc =
        mk_base (Idnt.new_var()) (Type.mk_const tyc) Formula.mk_true
      method farrow r1 r2 = mk_fun_args_ret [r1] r2
      method fforall p r1 = assert false
      method fexists p r1 = assert false
    end)

(** {6 Inspectors} *)

let rec args_ret rty =
  match rty with
  | Fun(x, rty1, rty2, (y, phi)) ->
    let args, ret = args_ret rty2 in
    (x, rty1, y, phi) :: args, ret
  | _ -> [], rty

let rec para f rty =
  match rty with
  | Base(x, ty, phi) -> f#fref x ty phi
  | Fun(x, rty1, rty2, (y, phi)) ->
    (*let r1 = para f rty1 in
      let r2 = para f rty2 in
      f#farrow x rty1 r1 rty2 r2 y phi*)
    let args, ret = args_ret rty in
    let args' = List.map (Quadruple.map_snd (para f)) args in
    let ret' = para f ret in
    f#ffun args args' ret ret'

let visit f rty =
  para
    (object
      method fref x ty phi = fun () -> f#fref x ty phi
      method ffun args args' ret ret' = fun () -> f#ffun args ret
    end)
    rty
    ()

let fold f =
  para
    (object
      method fref x ty phi = f#fref x ty phi
      method ffun _ args' _ ret' = f#ffun args' ret'
    end)

(** {6 Inspectors} *)

let rec is_closed env rty =
  match rty with
  | Base(x, _, p) -> Set_.diff (Formula.fvs p) (Formula.fpvs p @ env) = []
  | Fun(x, t1, t2, p) when is_closed env t1 -> is_closed (x :: env) t2
  | _ -> false

let fpvs =
  fold
    (object
      method fref x ty phi = Formula.fpvs phi
      method ffun args ret =
        List.concat_map Quadruple.snd args @ ret
        @ List.concat_map (Quadruple.fth >> Formula.fpvs) args
    end)

(** {6 Operators} *)

let rec ret rty =
  match rty with Fun (x, rty1, rty2, phi) -> ret rty2 | _ -> rty

let rec args_ret rty =
  match rty with
  | Fun (x, rty1, rty2, phi) ->
    let args, ret = args_ret rty2 in
    (x, rty1) :: args, ret
  | _ -> [], rty

let rec arity = function Fun (_,_,t,_) -> 1 + arity t | _ -> 0

let to_simple_type =
  fold
    (object
      method fref x ty phi = (*assert (Formula.is_true phi);*)ty
      method ffun args ret = List.map Quadruple.snd args @ [ret] |> Type.mk_fun
    end)

let rec subst xts rty =
  fold
    (object
      method fref x ty phi = fun xts ->
        let xts' = Map_.diff xts [x] in
        Base(x, ty, Formula.subst xts' phi)
      method ffun args ret = fun xts ->
        let xts', args' =
          List.fold_left
            (fun (xts', args') (x, r, y, phi) ->
               Map_.diff xts' [x],
               args' @ [x, r xts', y, Formula.subst (Map_.diff xts' [y]) phi])
            (xts, [])
            args
        in
        mk_fun_ args' (ret xts')
    end)
    rty xts

let subst_pvars psub =
  fold
    (object
      method fref x ty phi = mk_base x ty (CunFormula.subst_pvars psub phi)
      method ffun args ret =
        mk_fun_
          (List.map (Quadruple.map_fth (CunFormula.subst_pvars psub)) args)
          ret
    end)

let set_phi phi rty =
  match rty with
  | Base(x, ty, _) -> Base(x, ty, phi)
  | _ ->
    Logger.printf "unsupported type in RefTyp.set_phi: %a@," pr rty;
    assert false

let set_phi_ret phi rty =
  let args, ret = args_ret rty in
  mk_fun_args_ret_rty args (set_phi phi ret)

let set_pred pred = function
  | Base(x, ty, _) -> Base(x, ty, pred [Term.mk_var x, ty])
  | rty ->
    Logger.printf "unsupported type in RefTyp.set_pred: %a@," pr rty;
    assert false

let add_pvar tenv rty =
  match rty with
  | Base(x, ty, phi') ->
    let tenv = tenv @ [x, ty] in
    (* @todo too ad hoc, only work for game solving mode? *)
    let tenv = [x, ty] in
    let pvar = PredVar.make (Idnt.new_var ()) tenv in
    let phi = pvar |> PredVar.to_formula in
    Base(x, ty, Formula.mk_and phi phi'), pvar
  | _ ->
    Logger.printf "unsupported type in RefTyp.set_pvar: %a@," pr rty;
    assert false

let get_term rty =
  match rty with
  | Base(x, _, _) -> Term.mk_var x
  | rty ->
    Logger.printf "unsupported type in RefTyp.get_term: %a@," pr rty;
    assert false

let get_phi rty =
  match rty with
  | Base(_, _, phi) -> phi
  | rty ->
    Logger.printf "unsupported type in RefTyp.get_phi: %a@," pr rty;
    assert false

let new_var =
  let cnt = ref 0 in
  fun () -> cnt := !cnt + 1; Idnt.make ("__v" ^ (string_of_int !cnt))

let alpha xts rty =
  fold
    (object
      method fref x ty phi = fun xts ->
        let y = new_var () in
        Base(y, ty, Formula.subst ((x, Term.mk_var y) :: xts) phi)
      method ffun args ret = fun xts ->
        let xts', args' =
          List.fold_left
            (fun (xts', args') (x, r, y, phi) ->
               let z = new_var () in
               let w = new_var () in
               (x, Term.mk_var z) :: xts',
               args' @ [z, r xts',
                        w, Formula.subst ((y, Term.mk_var w) :: xts') phi])
            (xts, []) args
        in
        mk_fun_ args' (ret xts')
    end)
    rty
    xts

let mk_template name env rty =
  fold
    (object
      method fref x ty _ = fun name env ->
        let name = match name with
          | Idnt.T(_,_,_) -> name | _ -> Idnt.ret_args name 0 0 |> fst
        in
        mk_base x ty
          (Pva.make name (Map_.map_dom Term.mk_var env @ [Term.mk_var x, ty])
           |> Pva.to_formula)
      method ffun args ret = fun name env ->
        let ret_id, arg_ids = Idnt.ret_args name 0 (List.length args) in
        let env', args' =
          List.fold_left
            (fun (env', args') (id, (x, r, y, phi)) ->
               let rty = r id env' in
               env' @ [x, to_simple_type rty],
               args' @ [x, rty, y(*@todo*), phi(*@todo*)])
            (env, []) (List.combine arg_ids args)
        in
        mk_fun_ args' (ret ret_id env')
    end)
    rty name env

let merge_base x phi rty1 rty2 =
  match rty1, rty2 with
  | Base(x1, ty1, phi1), Base(x2, ty2, phi2)
    when Type.equiv_mod_unknown ty1 ty2 ->
    let phi2 = Formula.subst [x2, Term.mk_var x1] phi2 in
    let phi =
      Formula.bor
        [Formula.band [Formula.subst [x, BoolTerm.make true] phi; phi1];
         Formula.band [Formula.subst [x, BoolTerm.make false] phi; phi2]]
    in
    Base(x1, ty1, phi)
  | _ ->
    Format.printf_force "error: %a, %a@." pr rty1 pr rty2;
    failwith "Not Implemented. (RefTyp.merge)"

let drop_preds = to_simple_type >> of_simple_type
