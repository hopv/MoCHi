open Util
open Combinator

(** Simple type judgments *)

let cgen t ty =
  Term.para_wo_app
    (object
      method fvar x ts rs = fun ty ->
        let args =
          List.map
            (Term.fun_args >> function
              | Term.Const(Const.Annot ty), [_] -> ty
              | _ -> Type.mk_unknown)
            ts
        in
        try
          List.map2 apply rs args
          |> List.split
          |> Pair.map List.concat List.concat
          |> Pair.map_fst (List.cons (x, Type.mk_fun (args @ [ty])))
        with Invalid_argument _ ->
          Format.printf "%a@." Term.pr (Term.mk_app (Term.mk_var x) ts);
          assert false
      method fcon c ts rs = fun ty ->
        match c, ts, rs with
        | Const.Eq ty_arg, [t1; t2], [r1; r2] ->
          assert (Type.is_bool_unknown ty);
          (match Term.fun_args t1, Term.fun_args t2 with
           | (Term.Var(x1), []), (Term.Var(x2), []) ->
             Pair.map2 (@) (@) (r1 ty_arg) (r2 ty_arg)
             |> Pair.map_snd (List.cons (x1, x2))
           | _ ->
             Pair.map2 (@) (@) (r1 ty_arg) (r2 ty_arg))
        | _, _, _ ->
          let args, ret = (* args : [obj] , ret : (obj -> bool)*)
            match c with
            | Const.Annot(ty) -> ([ty], ty)
            | _ ->
              let ty = Const.type_of c in
              Logger.printf2 "c: %a  ty: %a@," (Const.pr []) c Type.pr ty;
              assert (not (Type.is_unknown ty));
              ty |> Type.args_ret
          in
          (*Logger.debug_assert
            (fun () -> Type.equiv ty ret)
            ~on_failure:
            (fun () ->
             Format.printf
               "error %a: %a <> %a@,"
               (Const.pr []) c
               Type.pr ty
               Type.pr ret);*)
          try
            List.map2 apply rs args
            |> List.split
            |> Pair.map List.concat List.concat
          with Invalid_argument _ ->
            Format.printf "%a@." Term.pr (Term.mk_app (Term.mk_const c) ts);
            assert false
      method fbin b x _ r _ [] = fun ty ->
        r (Binder.body_type_of b ty)
        |> Pair.map
          id (* @todo (List.filter (fst >> (<>) x))
                @todo check consistency with the type of x *)
          id (*@todo*)
    end)
    t ty

(** adhoc type inference *)
let infer t ty =
  let tenv, eqc = cgen t ty in
  let rec loop tenv =
    let tenv' =
      eqc
      |> List.concat_map
        (fun (x, y) ->
           let ty =
             Type.meet (List.assoc_fail x tenv) (List.assoc_fail y tenv)
           in
           [x, ty; y, ty])
      |> (@) tenv
      |> TypEnv.merge
    in
    if Set_.equiv tenv tenv' then tenv else loop tenv'
  in
  loop (TypEnv.merge tenv)
let infer =
  Logger.log_block2 "SimTypJudge.infer"
    ~before:(curry2 (Logger.printf "input:@,  %a@," TypTerm.pr))
    ~after:(Logger.printf "output:@,  %a" TypEnv.pr)
    infer

(* val env_of : Term.t -> Type.t -> TypEnv.t *)
let env_of t ty = infer t ty |> List.filter (fst >> Idnt.is_coeff >> not)
