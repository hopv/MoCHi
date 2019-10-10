open Util
open Combinator

(** {6 Constructors} *)

type t = Idnt.t * (Idnt.t * Type.t) list

(** {6 Printers} *)

let pr ppf (p, tenv) =
  Format.fprintf ppf "@[%a(%a)@]" Idnt.pr p TypEnv.pr_compact tenv

let pr_tex ppf (p, tenv) =
  Format.fprintf ppf "@[%a\\left(%a\\right)@]" Idnt.pr_tex p TypEnv.pr_compact_tex tenv
(** {6 Auxiliary constructors} *)

let make p tenv = p, tenv

let of_type p ty =
  let args, ret = Type.args_ret ty in
  assert (Type.is_bool ret);
  p, List.map (fun ty -> Idnt.new_var (), ty) args

(** {6 Auxiliary destructors} *)

let to_formula (p, tenv) =
  Term.mk_app
    (Term.mk_var p)
    (List.map
       (fun (x, ty) ->
          Term.mk_app (Term.mk_const(Const.Annot(ty))) [Term.mk_var x])
       tenv)
  |> Formula.of_term

(** {6 Morphisms} *)

let fold f (p, tenv) = f p tenv

let map_type f (p, tenv) = (p, TypEnv.map_type f tenv)

(** {6 Operators} *)

let alpha (p, tenv) =
  let tenv', map = TypEnv.alpha tenv in
  (p, tenv'), map

let rename_vars vmap (p, tenv) =
  (p, List.map (fun (x, ty) -> List.assocD x x vmap, ty) tenv)
let rename pvmap (p, tenv) = (List.assocD p p pvmap, tenv)
let rename_fail pvmap (p, tenv) = (List.assoc_fail p pvmap, tenv)

let reset_uid (p, tenv) = (Idnt.reset_uid p, tenv)
let normalize_args (p, tenv) =
  (p,
   List.mapi
     (fun i -> Pair.map_fst (fun _ -> Idnt.make ("x" ^ string_of_int i)))
     tenv)
let linearlize (p, tenv) =
  let rec loop tenv1 tenv2 phi =
    match tenv2 with
    | [] -> tenv1, phi
    | (x, ty) :: tenv2' ->
      if List.mem_assoc x tenv1 then
        let y = Idnt.new_var () in
        loop ((y, ty) :: tenv1)
          tenv2'
          (Formula.band [phi; Formula.eq ty (Term.mk_var x) (Term.mk_var y)])
      else
        loop ((x, ty) :: tenv1) tenv2' phi
  in
  let tenv, phi = loop [] (List.rev tenv) Formula.mk_true in
  (p, tenv), phi
let subst_tvars tsub (p, tenv) =
  make p (List.map (fun (x, ty) -> x, Type.subst tsub ty) tenv)

(** {6 Inspectors} *)

let eq_idnt (p1, _) (p2, _) = p1 = p2
let cong (p1, _) (p2, _) = Idnt.cong p1 p2
let idnt_of = fst
let args_of = snd
let fvs = snd >> List.map fst
let fvs_bool = snd >> List.filter (snd >> (=) Type.mk_bool) >> List.map fst
let fvs_ty = snd
let pat_match (p1, tenv1) (p2, tenv2) =
  Logger.debug_assert (fun () -> p1 = p2);
  TypTermSubst.pat_match tenv1 tenv2 |> TypTermSubst.tsub_of

let int_to_real (p, tenv) = p, TypEnv.int_to_real tenv
