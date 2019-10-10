open Combinator
open Util

(** @todo assume that the length of the arguments is >0 *)

type t = Idnt.t * TypTerm.t list

(** {6 Printers} *)

let pr ppf (p, tts) =
  Format.fprintf ppf "%a(%a)" Idnt.pr p TypTerm.pr_list_compact tts

let pr_tex ppf (p, tts) =
  Format.fprintf ppf "%a\\left(%a\\right)"
                 Idnt.pr_tex p TypTerm.pr_list_compact_tex tts

(** {6 Auxiliary constructors} *)

let make p tts = p, tts
let of_tenv p tenv = p, List.map (Pair.map_fst Term.mk_var) tenv
let of_pvar pv = of_tenv (PredVar.idnt_of pv) (PredVar.args_of pv)
let of_formula phi = Formula.let_pva phi make

(** {6 Auxiliary destructors} *)

let to_formula (p, tts) =
  Term.mk_app
    (Term.mk_var p)
    (List.map
       (fun (t, ty) -> Term.mk_app (Term.mk_const(Const.Annot(ty))) [t])
       tts)
  |> Formula.of_term

(** {6 Morphisms} *)

let fold f (p, tts) = f p tts
let map_term f = Pair.map_snd (List.map (TypTerm.map_term f))
let map_type f = Pair.map_snd (List.map (TypTerm.map_type f))

(** {6 Inspectors} *)

let idnt_of (p, _) = p
let args_of (_, args) = args
let type_of (_, args) = Type.mk_fun (List.map snd args @ [Type.mk_bool])
let tenv_of atm = [idnt_of atm, type_of atm]

let eq_idnt (p1, _) (p2, _) = p1 = p2

let fvs = snd >> List.concat_map TypTerm.fvs
let fvs_bool =
  args_of
  >> List.concat_map (TypTerm.term_of >> Formula.of_term >> Formula.fvs_bool)
let fvs_ty =
  args_of >> List.concat_map (uncurry2 SimTypJudge.env_of) >> TypEnv.merge
let coeffs = args_of >> List.concat_map (TypTerm.term_of >> Term.coeffs)
let ufuns_of f_formula =
  args_of >> List.concat_map (TypTerm.term_of >> CunTerm.ufuns_of f_formula)

let num_dup =
  List.classify eq_idnt
  >> List.map (fun pvas -> List.length pvas - 1)
  >> Integer.sum_list

let pvar_of (p, tts) =
  let ttsub = TypTermSubst.of_tts tts in
  let pv = ttsub |> TypTermSubst.tenv_of |> PredVar.make p in
  let phi = ttsub |> Formula.of_ttsub in
  let pv', phi' = (* pv may be non-linear *) PredVar.linearlize pv in
  pv', Formula.band [phi; phi']

let pat_match pv (p, tts) =
  assert (PredVar.idnt_of pv = p);
  try
    List.map2
      (fun (x, ty1) (t, ty2) ->
         Logger.log (fun () -> Type.meet ty1 ty2 |> ignore);
         (*assert (ty1 = ty2);*)
         x, t)
      (PredVar.args_of pv)
      tts
  with Invalid_argument _ -> raise Not_found(*@todo*)

let equiv implies_formulas simplify_formula
          env (p1, tts1) (p2, tts2) =
  p1 = p2 &&
  implies_formulas
    env
    (List.map2
       (fun tt1 tt2 -> Formula.eq_tt tt1 tt2 |> simplify_formula)
       tts1 tts2)

let matches implies_formulas simplify_formula
            p env (p1, tts1) (p2, tts2) =
  p1 = p2 &&
  List.for_all2
    (fun tt1 tt2 ->
       TypTerm.equiv tt1 tt2 ||
       List.exists p (TypTerm.fvs tt2)(* @todo *) ||
       (List.for_all (p >> not) (TypTerm.fvs tt1)(* @todo *) &&
        implies_formulas env [Formula.eq_tt tt1 tt2 |> simplify_formula]))
    tts1 tts2

(** {6 Operators} *)

let rename_vars vmap (p, tts) =
  make p (List.map (fun (t, ty) -> Term.rename vmap t, ty) tts)
let rename pvmap (p, tts) = List.assocD p p pvmap, tts
let rename_fail pvmap (p, tts) = List.assoc_fail p pvmap, tts
let fresh = map_term (fun _ -> Term.new_var ())
let simplify = map_term CunTerm.simplify
let subst sub = map_term (Term.subst sub)
let subst_fixed sub = map_term (Term.subst_fixed sub)
let subst_tvars tsub (p, tts) =
  make p (List.map (TypTerm.subst_tvars tsub) tts)

let int_to_real (p, tts) =
  p, List.map (Pair.map CunTerm.int_to_real Type.int_to_real) tts
