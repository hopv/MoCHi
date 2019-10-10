open Util
open Combinator

(** Type expressions *)

include AbsTerm.Make(TypBinder)(TypConst)

(** {6 Auxiliary constructors} *)

let new_var () = mk_var (Idnt.new_tvar ())

let mk_unit = mk_const TypConst.Unit
let mk_bool = mk_const TypConst.Bool
let mk_int = mk_const TypConst.Int
let mk_real = mk_const TypConst.Real
let mk_string = mk_const TypConst.String
let mk_list ty = mk_app (mk_const TypConst.List) [ty]
let mk_ext id = mk_const (TypConst.Ext(id))

let tyc_answer = TypConst.Ext("X"(*@todo*))
let mk_answer = mk_const tyc_answer

let mk_bot = mk_const TypConst.Bot
let mk_top = mk_const TypConst.Top

let mk_unknown = mk_const TypConst.Unknown

(* ret: return *)
let mk_fun_args_ret args ret =
  List.fold_right
    (fun t1 t2 -> mk_app (mk_const TypConst.Arrow) [t1; t2])
    args
    ret

let mk_fun tys = mk_fun_args_ret (List.initial tys) (List.last tys)

let mk_ua = mk_fun [mk_unit; mk_answer]
let mk_uub = mk_fun [mk_unit; mk_unit; mk_bool]
let mk_ub = mk_fun [mk_unit; mk_bool]
let mk_bb = mk_fun [mk_bool; mk_bool]
let mk_bbb = mk_fun [mk_bool; mk_bool; mk_bool]
let mk_ii = mk_fun [mk_int; mk_int]
let mk_iii = mk_fun [mk_int; mk_int; mk_int]
let mk_iaa = mk_fun [mk_int; mk_answer; mk_answer]
let mk_ib = mk_fun [mk_int; mk_bool]
let mk_iib = mk_fun [mk_int; mk_int; mk_bool]
let mk_rr = mk_fun [mk_real; mk_real]
let mk_rrr = mk_fun [mk_real; mk_real; mk_real]
let mk_raa = mk_fun [mk_real; mk_answer; mk_answer]
let mk_rrb = mk_fun [mk_real; mk_real; mk_bool]
let mk_ir = mk_fun [mk_int; mk_real]

let mk_forall xs ty =
  List.fold_right
    (fun x ty -> mk_binder TypBinder.Forall (Pattern.V x) ty)
    xs ty

let mk_exists xs ty =
  List.fold_right
    (fun x ty -> mk_binder TypBinder.Exists (Pattern.V x) ty)
    xs ty

let mk_exists_pat p ty = mk_binder TypBinder.Exists p ty

(** {6 Morphisms} *)

let rec para f ty =
  match fun_args ty with
  | Var(x), [] ->
    f#fvar x
  | Const(c), [] when TypConst.is_base c ->
    f#fbase c
  | Const(TypConst.Arrow), [ty1; ty2] ->
    let r1 = para f ty1 in
    let r2 = para f ty2 in
    f#farrow ty1 r1 ty2 r2
  | Binder(TypBinder.Forall, p, ty1), [] ->
    let r1 = para f ty1 in
    f#fforall p ty1 r1
  | Binder(TypBinder.Exists, p, ty1), [] ->
    let r1 = para f ty1 in
    f#fexists p ty1 r1
  | _ ->
    (*invalid_arg "Type.para"*)
    Format.printf "%a@," pr ty;
    assert false

let visit f ty =
  para
    (object
      method fvar x = fun () -> f#fvar x
      method fbase c = fun () -> f#fbase c
      method farrow ty1 r1 ty2 r2 = fun () -> f#farrow ty1 ty2
      method fforall p ty1 r1 = fun () -> f#fforall p ty1
      method fexists p ty1 r1 = fun () -> f#fexists p ty1
    end)
    ty
    ()

let fold f =
  para
    (object
      method fvar x = f#fvar x
      method fbase c = f#fbase c
      method farrow ty1 r1 ty2 r2 = f#farrow r1 r2
      method fforall p ty1 r1 = f#fforall p r1
      method fexists p ty1 r1 = f#fexists p r1
    end)

(** {6 Auxiliary destructors} *)

let args_ret =
  lazy_para_wo_app
    (object
      method fvar x ts _ = [], mk_app (mk_var x) ts (* @todo assert false *)
      method fcon c ts rs =
        match c, ts, rs with
        | TypConst.Arrow, [ty; _], [_; r] ->
          Lazy.force r
          |> Pair.map_fst (List.cons ty)
        | _ -> [], mk_app (mk_const c) ts
      method fbin b x t _ ts _ = [], mk_app (mk_binder b x t) ts
    end)

let args_of = args_ret >> fst
let ret_of = args_ret >> snd

let let_fun ty k =
  match fun_args ty with
  | Const(TypConst.Arrow), [ty1; ty2] -> k ty1 ty2
  | _ -> assert false

let arg_ret ty = let_fun ty Pair.make

let args_ret_for_accessor ty =
  let_fun ty Pair.make

let let_base ty k =
  match fun_args ty with
  | Const(c), [] when TypConst.is_base c -> k c
  | _ ->
    Logger.debug_assert_false
      ~on_failure:
        (fun () -> Format.printf "error in Type.let_base:@,  ty=%a@," pr ty)
      ()

let let_ext ty k =
  match fun_args ty with
  | Const(TypConst.Ext(id)), [](*@todo*) -> k id
  | _ -> assert false

let rec forall_of ty =
  visit
    (object
      method fvar x = [], mk_var x
      method fbase c = [], mk_const c
      method farrow ty1 ty2 = [], mk_fun [ty1; ty2]
      method fforall (Pattern.V x) ty1 =
        let xs, ty1' = forall_of ty1 in
        x :: xs, ty1'
      method fexists p ty1 = [], mk_exists_pat p ty1
    end)
    ty

let let_forall ty k = uncurry2 k (forall_of ty)


(** {6 Inspectors} *)

let is_var =
  visit
    (object
      method fvar _ = true
      method fbase _ = false
      method farrow _ _ = false
      method fadt _ _ = false
      method fforall _ _ = assert false
      method fexists _ _ = assert false
    end)

let is_base =
  visit
    (object
      method fvar _ = false(*@todo*)
      method fbase _ = true
      method farrow _ _ = false
      method fforall _ _ = assert false
      method fexists _ _ = assert false
    end)

let is_const c' =
  visit
    (object
      method fvar x = false(*@todo assert false*)
      method fbase c = c = c'
      method farrow _ _ = false
      method fforall _ _ = assert false
      method fexists _ _ = assert false
    end)
let is_unit = is_const TypConst.Unit
let is_bool = is_const TypConst.Bool
let is_int = is_const TypConst.Int
let is_real = is_const TypConst.Real
let is_string = is_const TypConst.String
let is_ext =
  visit
    (object
      method fvar x = assert false
      method fbase = function TypConst.Ext(_) -> true | _ -> false
      method farrow _ _ = false
      method fforall _ _ = assert false
      method fexists _ _ = assert false
    end)
let is_bot = is_const TypConst.Bot
let is_top = is_const TypConst.Top

let is_var = function Var _ -> true | _ -> false
let is_unknown ty = is_const TypConst.Unknown ty || is_var ty
let is_unit_unknown ty = is_unit ty || is_unknown ty
let is_bool_unknown ty = is_bool ty || is_unknown ty
let is_int_unknown ty = is_int ty || is_unknown ty
let is_real_unknown ty = is_real ty || is_unknown ty

let equiv_mod_unknown ty1 ty2 =
  if is_var ty1 && is_var ty2 then
    ty1 = ty2
  else
    ty1 = ty2
    || is_unknown ty1
    || is_unknown ty2

let apply ty1 ty2 =
  let_fun ty1 (fun ty11 ty12 ->
      assert (equiv_mod_unknown ty2 ty11);
      ty12)

let is_fun =
  visit
    (object
      method fvar _ = false(*@todo*)
      method fbase _ = false
      method farrow _ _ = true
      method fforall _ _ = assert false
      method fexists _ _ = assert false
    end)


let contain_tvar t =
  let args, ret = args_ret t in
  List.exists is_var (ret::args)

(** [arity_of ty] returns the arity of [ty]
    @require [ty] has no var *)
let arity_of = args_ret >> fst >> List.length

(* @require ty has no var *)
let rec order_of ty =
  args_ret ty
  |> fst
  |> if_ ((=) [])
    (const 0)
    (List.map order_of >> Integer.max_list >> (+) 1)

let size_of =
  visit
    (object
      method fvar x = assert false
      method fbase c = assert false
      method farrow _ _ = assert false
      method fforall _ _ = assert false
      method fexists _ _ = assert false
    end)

let nth ty i =
  assert (i >= 0);
  let args, ret = args_ret ty in
  try
    List.nth (args @ [ret]) i
  with Invalid_argument _ ->
    Format.printf "%a, %a@," pr ty Integer.pr i;
    assert false

(** {6 Operators} *)

let rec meet ty1 ty2 =
  match ty1, ty2 with
  | Const(TypConst.Top), ty
  | Const(TypConst.Unknown), ty
  | Var(_), ty
  | ty, Const(TypConst.Top)
  | ty, Const(TypConst.Unknown)
  | ty, Var(_) -> ty
  | ty1, ty2 when ty1 = ty2 -> ty1
  | ty1, ty2 when is_fun ty1 && is_fun ty2 ->
    let ty11, ty12 = arg_ret ty1 in
    let ty21, ty22 = arg_ret ty2 in
    mk_fun [meet ty11 ty21; meet ty12 ty22]
  | _, _ ->
    (*@todo use intersection types*)
    Format.printf "Type.meet: ty1: %a, ty2: %a@." pr ty1 pr ty2;
    Logger.print_fpat_call_stack ();
    assert false
let meet_list = List.fold_left meet (Const TypConst.Top)

let rec join ty1 ty2 =
  match ty1, ty2 with
  | Const(TypConst.Bot), ty
  | ty, Const(TypConst.Bot) -> ty
  | ty1, ty2 when ty1 = ty2 -> ty1
  | _, _ ->
    (*@todo use union types*)
    Logger.debug_assert_false
      ~on_failure:
        (fun () -> Format.printf "ty1: %a@,ty2: %a@," pr ty1 pr ty2)
      ()
let join_list = List.fold_left join (Const TypConst.Bot)

(** @todo fix *)
let instantiate ty =
  let_forall ty
    (fun xs ty1 ->
       let sub = List.map (fun x -> x, new_var ()) xs in
       subst sub ty1)

let generalize ty xs = mk_forall (List.unique (Set_.diff (fvs ty) xs)) ty

let int_to_real =
  fold
    (object
      method fvar = mk_var
      method fbase c = if c = TypConst.Int then mk_real else mk_const c
      method farrow ty1 ty2 = mk_fun [ty1; ty2]
      method fforall (Pattern.V(x)) = mk_forall [x]
      method fexists (Pattern.V(x)) = mk_exists [x]
    end)

let real_to_int =
  fold
    (object
      method fvar = mk_var
      method fbase c = if c = TypConst.Real then mk_int else mk_const c
      method farrow ty1 ty2 = mk_fun [ty1; ty2]
      method fforall (Pattern.V(x)) = mk_forall [x]
      method fexists (Pattern.V(x)) = mk_exists [x]
    end)
