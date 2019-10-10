open Util
open Combinator
open Term

(** Number term expressions *)

(** {6 Auxiliary constructors} *)

let mk_uop c t = mk_app (mk_const c) [t]
let mk_bop c t1 t2 = mk_app (mk_const c) [t1; t2]
let neg ty t = mk_uop (Const.Neg ty) t
let add ty t1 t2 = mk_bop (Const.Add ty) t1 t2
let sub ty t1 t2 = mk_bop (Const.Sub ty) t1 t2
let mul ty t1 t2 = mk_bop (Const.Mul ty) t1 t2
let div ty t1 t2 = mk_bop (Const.Div ty) t1 t2
let div ty t1 t2 = mk_bop (Const.Div ty) t1 t2
let max ty t1 t2 = mk_bop (Const.Max ty) t1 t2
let min ty t1 t2 = mk_bop (Const.Min ty) t1 t2
let mod_ ty t1 t2 = mk_bop Const.Mod t1 t2
