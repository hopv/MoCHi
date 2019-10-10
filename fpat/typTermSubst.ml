open Util
open Combinator

include Map_

type elem = (Idnt.t, TypTerm.t) _elem
type t = (Idnt.t, TypTerm.t) _t

(** {6 Printers} *)

let pr_elem ppf (x, (t, _)) = Format.fprintf ppf "%a -> %a" Idnt.pr x Term.pr t
let pr ppf ttsub = Format.fprintf ppf "[%a]" (List.pr pr_elem " && ") ttsub

(** {6 Morphisms} *)

let map_elem = List.map

(** {6 Auxiliary constructors} *)

let mk_elem x t ty = (x, (t, ty))

let of_tts =
  List.map
    (fun (t, ty) ->
       if Term.is_var t && not (Idnt.is_coeff (Term.var_of t))
       then Term.var_of t, (t, ty)
       else Idnt.new_var (), (t, ty))

let pat_match tenv1 tenv2 =
  Logger.debug_assert (fun () -> List.eq_length tenv1 tenv2);
  List.map2
    (fun (x1, ty1) (x2, ty2) ->
       Logger.debug_assert (fun () -> ty1 = ty2);
       x1, (TypTerm.make (Term.mk_var x2) ty1))
    tenv1 tenv2
let pat_match =
  Logger.log_block2
    "TypTermSubst.pat_match"
    ~before:(fun tenv1 tenv2 ->
        Logger.printf2
          "tenv1:@,  %a@,tenv2:@,  %a@,"
          TypEnv.pr tenv1 TypEnv.pr tenv2)
    pat_match

let bool_valuations bool_vars =
  Vector.product
    id
    (List.map
       (fun b ->
          [b, (BoolTerm.mk_true, Type.mk_bool);
           b, (BoolTerm.mk_false, Type.mk_bool)])
       bool_vars)

(** {6 Auxiliary destructors} *)

let tenv_of = List.map (Pair.map_snd TypTerm.type_of)
let tsub_of = List.map (Pair.map_snd TypTerm.term_of)

(** {6 Inspectors} *)

let fvs_elem (x, (t, _)) = x(*@todo*) :: Term.fvs t
let fvs = List.concat_map fvs_elem

let cyclic ttsub = raise (Global.NotImplemented "TypTermSubst.cyclic")

let lookup = List.assoc
