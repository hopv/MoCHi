open Combinator
open Util

(** Typed term expressions *)

type t = Term.t * Type.t

(** {6 Auxiliary constructors} *)

let make t ty = (t, ty)

(** {6 Printers} *)

(* val pr : Format.formatter -> t -> unit *)
let pr ppf (t, ty) =
  Format.fprintf
    ppf
    "@[%a : %a@]"
    Term.pr t
    Type.pr ty

let pr_tex ppf (t, ty) =
  Format.fprintf
    ppf
    "@[%a : %a@]"
    Term.pr_tex t
    Type.pr_tex ty

let pr_compact ppf (t, ty) =
  Format.fprintf
    ppf
    "@[%a:%a@]"
    Term.pr t
    Type.pr ty

let pr_compact_tex ppf (t, ty) =
  Format.fprintf
    ppf
    "@[%a:%a@]"
    Term.pr_tex t
    Type.pr_tex ty

(* val pr_list : Format.formatter -> t list -> unit *)
let pr_list ppf tts =
  Format.fprintf
    ppf
    "%a"
    (List.pr pr ",") tts

let pr_list_compact ppf tts =
  Format.fprintf
    ppf
    "%a"
    (List.pr pr_compact ",") tts

let pr_list_compact_tex ppf tts =
  Format.fprintf
    ppf
    "%a"
    (List.pr pr_compact_tex ",") tts

(** {6 Morphism} *)

let map_term f (t, ty) =
  make (f t) ty

let map_type f (t, ty) =
  make t (f ty)

(** {6 Auxiliary destructors} *)

let let_annot_term t k =
  try
    Term.let_app t (fun t1 t2 ->
        Term.let_const t1 (function
            | Const.Annot ty -> k t2 ty
            | c -> raise (Global.NoMatch "let_annot_term")
              (*Format.printf "c: %s@." (Const.string_of c); assert false*)))
  with Global.NoMatch _ ->
    raise (Global.NoMatch "let_annot_term")
let annot_term_of t = let_annot_term t Pair.make

(** {6 Inspectors} *)

let term_of = fst

let type_of = snd

let equiv_term (t1, _) (t2, _) =
  Term.equiv t1 t2

let equiv_type (_, ty1) (_, ty2) =
  Type.equiv ty1 ty2

let equiv tt1 tt2 =
  equiv_term tt1 tt2
  && equiv_type tt1 tt2

let fvs (t, _) = Term.fvs t

(** {6 Operators} *)

let fresh (t, ty) =
  make (Term.new_var ()) ty

let subst_tvars tsub (t, ty) =
  (Term.subst_tvars tsub t, Type.subst tsub ty)
