open Util
open Combinator

(** Predicates *)

type t = TypEnv.t * Formula.t

(** {6 Auxiliary constructors} *)

let pr ppf (tenv, phi) =
  Format.fprintf ppf "(%a).%a" TypEnv.pr tenv Formula.pr phi

let make tenv phi = (tenv, phi)

let mk_bot ty =
  let args, ret = Type.args_ret ty in
  assert (Type.is_bool ret);
  let tenv = List.map (fun ty -> Idnt.new_var (), ty) args in
  make tenv Formula.mk_false
let mk_top ty =
  let args, ret = Type.args_ret ty in
  assert (Type.is_bool ret);
  let tenv = List.map (fun ty -> Idnt.new_var (), ty) args in
  make tenv Formula.mk_true

(** {6 Inspectors} *)

let type_of (tenv, phi) = Type.mk_fun_args_ret (List.map snd tenv) Type.mk_bool
let fvs (tenv, phi) =
  Set_.diff (phi |> Formula.fvs |> List.unique) (List.map fst tenv)
let coeffs (tenv, phi) =
  Set_.diff (phi |> Formula.coeffs |> List.unique) (List.map fst tenv)

(** {6 Operators} *)

let apply (tenv, phi) ttys =
  assert (List.length tenv = List.length ttys);
  let tsub =
    List.map2
      (fun (x, ty1) (t, ty2) ->
         if Type.equiv_mod_unknown ty1 ty2 then x, t
         else
           begin
             Format.printf "error: %a <> %a@." Type.pr ty1 Type.pr ty2;
             Format.printf
               "failed to apply %a to %a@."
               pr (tenv, phi) TypTerm.pr_list ttys;
             assert false
           end)
      tenv ttys
  in
  Formula.subst tsub phi

let fresh (tenv, phi) = tenv, Formula.fresh (fvs (tenv, phi)) phi

let normalize (tenv, phi) =
  let tenv' =
    List.mapi
      (fun i -> Pair.map_fst (fun _ -> Idnt.make ("x" ^ string_of_int i)))
      tenv
  in
  (tenv', Formula.subst (TermSubst.of_tenvs tenv tenv') phi)

let band preds =
  let preds = List.map normalize preds in
  preds |> List.hd |> fst, List.map snd preds |> Formula.band

let bor preds =
  let preds = List.map normalize preds in
  preds |> List.hd |> fst, List.map snd preds |> Formula.bor

let bnot (tenv, phi) = (tenv, Formula.bnot phi)

let is_true (_, phi) = Formula.is_true phi
let is_false (_, phi) = Formula.is_false phi
