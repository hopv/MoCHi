open Util
open Combinator

(** Term expressions *)

include AbsTerm.Make(Binder)(Const)

let may_have_side_effect =
  fold_wo_app
    (object
      method fvar _ bs = bs <> [] (** @todo too conservative*)
      method fcon c bs = Const.has_side_effect c || List.exists id bs
      method fbin _ _ _ _ = true
    end)

let is_rand =
  fold
    (object
      method fvar _ = false
      method fcon = function
        | Const.RandBool | Const.RandInt | Const.RandReal -> true
        | _ -> false
      method fapp _ _ = false
      method fbin _ _ _ = false
    end)

let is_read =
  fold
    (object
      method fvar _ = false
      method fcon = function
        | Const.ReadBool(_) | Const.ReadInt(_) | Const.ReadReal(_) -> true
        | _ -> false
      method fapp _ _ = false
      method fbin _ _ _ = false
    end)

let is_simple =
  fold
    (object
      method fvar _ = true
      method fcon _ = true
      method fapp _ _ = false
      method fbin _ _ _ = false
    end)

let subst_tvars tsub =
  fold
    (object
      method fvar x = mk_var x
      method fcon c = mk_const (Const.subst_tvars tsub c)
      method fapp t1 t2 = mk_app t1 [t2]
      method fbin b p t1 = mk_binder (Binder.subst_tvars tsub b) p t1
    end)

let rec args_body_of acc t =
  match t with
  | Binder(Binder.Lambda(_), arg, t') -> args_body_of (arg :: acc) t'
  | Binder(Binder.Fix(_), arg, t') -> args_body_of acc t'
  | _ -> List.rev acc, t
let args_body_of = args_body_of []
