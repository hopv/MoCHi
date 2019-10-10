open Util
open Combinator
open Term

let rec replace xs env rules t =
  try
    List.find_map
      (fun (pat, t') ->
         try
           Logger.printf "pattern: %a@," pr pat;
           Logger.printf "target: %a@," pr t;
           Logger.printf "xs: %a@," Idnt.pr_list xs;
           let env' = hounify xs env t pat in
           (*Logger.printf "succeed@,";*)
           Some(env', t')
         with AbsTerm.CannotUnify ->
           None)
      rules
  with
  | Not_found ->
    match t with
    | Var(x) -> env, Var(x)
    | App(t1, t2) ->
      let env, [t1; t2] =
        List.fold_left
          (fun (env, ts) t ->
             let env, t = replace xs env rules t in
             env, ts @ [t])
          (env, [])
          [t1; t2]
      in
      env, App(t1, t2)
    | Const(c) -> env, Const(c)
    | _ -> assert false
(*
     | Vector(ts) ->
        let env, ts =
          List.fold_left
            (fun (env, ts) t ->
             let env, t = replace xs env rules t in
             env, ts @ [t])
            (env, [])
            ts
        in
        env, Vector(ts)
     | VElem(t, i) ->
        let env, t = replace xs env rules t in
        env, VElem(t, i)
 *)
and hounify xs env t1 t2 =
  let add (x, t) env =
    Logger.printf2 "binding %a to %a@," pr t Idnt.pr x;
    let env1, env2 = List.partition (fst >> (=) x) env in
    let env2' = List.map (fun (x', t') -> x', subst [x, t] t') env2 in
    List.fold_left
      (fun env (_, t') -> hounify xs env t t')
      ((x, t) :: env2')
      env1
  in
  match fun_args t1, fun_args t2 with
  | (t1, ts1), (t2, ts2) when t1 = t2 ->
    if not (List.eq_length ts1 ts2) then raise AbsTerm.CannotUnify
    else List.fold_left2 (hounify xs) env ts1 ts2

  | (Var(x1), _), (Var(x2), _)
    when x1 <> x2 && not (List.mem x1 xs) && not (List.mem x2 xs) ->
    raise AbsTerm.CannotUnify
  | (Var(x), ts), _ when List.mem x xs ->
    if ts = [] then
      if occurs x t2 then raise AbsTerm.CannotUnify
      else add (x, t2) env
    else if List.exists (occurs x) ts then
      raise (Global.NotImplemented "Unifier.hounify")
    else
      let xs = List.map (fun _ -> Idnt.new_var ()) ts in
      let env', t2' =
        replace xs env (List.map2 (fun t x -> t, mk_var x) ts xs) t2
      in
      add (x,
           List.fold_right
             (fun x ->
                mk_binder (Binder.Lambda Type.mk_top(*@todo*)) (Pattern.V(x)))
             xs t2') env'
  | _, (Var(x), _) when List.mem x xs -> hounify xs env t2 t1
  | (Const(c1), _), (Const(c2), _) when c1 <> c2 ->
    raise AbsTerm.CannotUnify
(*
  | (Vector(ts1), []), (Vector(ts2), []) ->
     List.fold_left2 (hounify xs) env ts1 ts2
  | (VElem(t1, i1), []), (VElem(t2, i2), []) ->
     if i1 <> i2 then
       raise AbsTerm.CannotUnify
     else
       hounify xs env t1 t2
 *)
  | _, _ -> raise AbsTerm.CannotUnify
let hounify xs t1 t2 = hounify xs [] t1 t2

exception NeverMatch
exception MayNotMatch

let match_linpat xs t (nxs, n) =
  try
    List.find_maplr
      (fun nxs1 (n', x) nxs2 ->
         if List.mem x xs && n' = 1 || n' = -1 then
           let t' =
             if n' = 1 then IntTerm.of_lin_exp (LinIntExp.neg (nxs1 @ nxs2, n))
             else if n' = -1 then IntTerm.of_lin_exp (nxs1 @ nxs2, n)
             else assert false
           in
           TypTermSubst.mk_elem
             x
             (CunTerm.simplify (IntTerm.add t t'))
             Type.mk_int
           |> List.return
           |> Option.return
         else None)
      nxs
  with Not_found -> raise MayNotMatch

let match_tt valid xs (t1, ty1) (t2, ty2) =
  Logger.debug_assert (fun () -> ty1 = ty2);
  if t1 = t2 then []
  else if Set_.inter (Term.fvs t2) xs = [] then
    if valid (NumFormula.eq ty1 t1 t2) then [] else raise MayNotMatch
  else
    match t2 with
    | Term.Var(x) when List.mem x xs -> [TypTermSubst.mk_elem x t1 ty1]
    | _ ->
      begin
        try match_linpat xs t1 (CunTerm.to_lin_int_exp t2) with
        | Invalid_argument _ -> raise MayNotMatch
        | MayNotMatch -> raise MayNotMatch
        | NeverMatch -> raise NeverMatch
      end
let match_tt ?(valid = fun t -> false) =
  Logger.log_block3
    "Unifier.match_tt"
    ~before:(fun _ (t1, _) (t2, _) ->
        Logger.printf2 "t1: %a@,t2: %a@," Term.pr t1 Term.pr t2)
    (match_tt valid)
