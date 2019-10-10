open Util
open Combinator

include Term

(** {6 Printers} *)

let ext_pr = ref Term.pr
let pr ppf = !ext_pr ppf
let ext_pr_tex = ref Term.pr_tex
let pr_tex ppf = !ext_pr_tex ppf

(** {6 Auxiliary constructors} *)

let make c ts = Term.mk_app (Term.mk_const c) ts
let of_term = id
let mk_true = BoolTerm.mk_true
let mk_false = BoolTerm.mk_false
let mk_var x = mk_app (mk_var x)
let mk_urel c t = mk_app (mk_const c) [t]
let mk_brel c t1 t2 = mk_app (mk_const c) [t1; t2]

let eq ty t1 t2 = mk_brel (Const.Eq ty) t1 t2
let neq ty t1 t2 = mk_brel (Const.Neq ty) t1 t2
let eq_tt ((t1, ty1) as tt1) ((t2, ty2) as tt2) =
  Logger.debug_assert
    (fun () -> TypTerm.equiv_type tt1 tt2)
    ~on_failure:(fun () ->
        Format.printf "%a <> %a@," TypTerm.pr tt1 TypTerm.pr tt2);
  eq ty1 t1 t2

(** {6 Auxiliary destructors} *)

let term_of atm = atm

(** {6 Inspectors} *)

let fpvs = Term.fun_args >> function Term.Var(v), _ -> [v] | _ -> []
let fpvs_strict = Term.fun_args >> function
  | Term.Var(v), ts when ts <> [] -> [v]
  | _ -> []
let is_pva pvs =
  fun_args
  >> function Var(p), ts when List.mem p pvs && ts <> [] -> true | _ -> false
let is_eq = fun_args >> function Const(Const.Eq(_)), _ -> true | _ -> false
let is_neq = fun_args >> function Const(Const.Neq(_)), _ -> true | _ -> false

(** {6 Operators} *)

let remove_annot =
  Term.fold
    (object
      method fvar = Term.mk_var
      method fcon = Term.mk_const
      method fapp t1 t2 =
        match t1 with
        | Term.Const (Const.Annot (_)) -> t2
        | _ -> Term.mk_app t1 [t2]
      method fbin = Term.mk_binder
    end)
