open Util
open Combinator

(** Refinement intersection types *)

type t =
  | Bot
  | Top
  | Base of Idnt.t * TypConst.t * Formula.t
  | Fun of (t * t) list (* binders are ... *)

let refine_unit = ref true
let refine_function = ref false

(** {6 Inspectors} *)

let is_base rty =
  match rty with
  | Bot -> false(*@todo*)
  | Top -> false(*@todo*)
  | Base(_, _, _) -> true
  | Fun(_) -> false

let bv_of rty =
  match rty with
  | Bot -> assert false
  | Top -> assert false
  | Base(bv, _, _) -> bv
  | Fun(_) -> assert false

let rec args_ret rty =
  match rty with
  | Fun([rty1, rty2]) ->
    let args, ret = args_ret rty2 in
    rty1 :: args, ret
  | Fun(_) ->
    assert false
  | _ ->
    [], rty

(* y is visible from x? *)
let rec visible x y =
  match x with
  | Idnt.V(_) ->
    false(*@todo*)
  | Idnt.T(z, uid, arg) ->
    begin
      match y with
      | Idnt.V(_) -> false(*@todo*)
      | Idnt.T(z', uid', arg') ->
        (z = z' && uid = uid' && arg' <= arg) ||
        (visible z y)
    end


let rec visible_vars x =
  match x with
  | Idnt.V(_) ->
    [x]
  | Idnt.T(x, uid, arg) ->
    visible_vars x
    @ List.init (arg + 1) (fun i -> Idnt.T(x, uid, i))

(** @require x is a structured variable
    @ensure returned var. y is base
    @ensure forall returned var. y, visible x y *)
let visible_vars env x =
  visible_vars x
  |> List.filter_map
    (fun x -> if Type.is_base (env x) then
        Some(x, env x)
      else None)

let refinable ty =
  if Type.is_fun ty then !refine_function
  else if Type.is_base ty then
    if Type.is_unit ty then
      !refine_unit
    else
      true
  else
    assert false

(** @require selective pred. abs. is applied *)
let find_last_base_exc env (x, uid) =
  let rec aux ty i j =
    if Type.is_base ty then
      j
    else if Type.is_fun ty then
      Type.let_fun
        ty
        (fun ty1 ty2 ->
           aux ty2 (i + 1) (if refinable ty1 then i else j))
    else
      begin
        Format.printf "%a@," Type.pr ty;
        assert false
      end
  in
  let i = aux (env x) 0 (-1) in
  if i = -1 then
    raise Not_found
  else
    Idnt.T(x, uid, i)

let find_last_base env (x, uid) =
  try
    find_last_base_exc env (x, uid)
  with Not_found ->
    (* condition must be Formula.mk_true *)
    Idnt.T(x, uid, -1)

let rec fresh_names new_var ty =
  match ty with
  | Bot -> []
  | Top -> []
  | Base(x, _, t) ->
    let y = new_var () in
    [x, y]
  | Fun(xs) ->
    List.concat_map
      (fun (rty1, rty2) ->
         let sub1 = fresh_names new_var rty1 in
         let sub2 = fresh_names new_var rty2 in
         sub1 @ sub2)
      xs

let pred_of_base rty =
  match rty with
  | Bot -> assert false
  | Top -> assert false
  | Base(x, _, t) -> x, t
  | Fun(_) -> assert false

(** {6 Printers} *)

let rec pr ppf rty =
  match rty with
  | Bot ->
    String.pr ppf "bot"
  | Top ->
    String.pr ppf "top"
  | Base(x, c, t) ->
    Format.fprintf ppf "@[<hov>";
    (if Formula.is_true t then
       String.pr ppf (TypConst.string_of c)
     else
       Format.fprintf
         ppf
         "{%a:%s | %a}"
         Idnt.pr x
         (TypConst.string_of c)
         Formula.pr t);
    Format.fprintf ppf "@]"
  | Fun(xs) ->
    assert (xs <> []);
    let pr_aux ppf (rty1, rty2) =
      Format.fprintf ppf "@[<hov>";
      (if is_base rty1 (*|| is_adt rty1*) then
         Format.fprintf ppf "%a:%a" Idnt.pr (bv_of rty1) pr rty1
       else
         Format.fprintf ppf "(%a)" pr rty1);
      Format.fprintf ppf "@ ->@ %a@]" pr rty2
    in
    Format.fprintf ppf "@[<hv>%a@]" (List.pr pr_aux " /\\@ ") xs

let pr_bind ppf (f, sty) =
  Format.fprintf ppf "%a: %a" Idnt.pr f pr sty
let pr_env ppf env =
  Format.fprintf ppf "@[<v>%a@]" (List.pr pr_bind "@ ") env

(** {6 Auxiliary constructors} *)

let answer_type =
  Base(Idnt.make "nu", TypConst.Ext("X"(*@todo*)), Formula.mk_true)

let mk_fun tys =
  List.fold_right
    (fun ty1 ty2 -> Fun [ty1, ty2])
    (List.initial tys)
    (List.last tys)

let rec of_simple_type ty =
  if Type.is_bot ty then
    Bot
  else if Type.is_top ty then
    Top
  else if Type.is_base ty then
    Type.let_base
      ty
      (fun c ->
         Base(Idnt.new_var(), c, Formula.mk_true))
  else if Type.is_fun ty then
    Type.let_fun
      ty
      (fun ty1 ty2 ->
         Fun([of_simple_type ty1, of_simple_type ty2]))
  else
    assert false

let rec subst xts rty =
  match rty with
  | Bot -> Bot
  | Top -> Top
  | Base(x, c, t) ->
    let xts' = Map_.diff xts [x] in
    Base(x, c, Formula.subst xts' t)
  | Fun(xs) ->
    Fun
      (List.map
         (fun (rty1, rty2) ->
            let xts' =
              if is_base rty1 (*|| is_adt rty1*) then
                Map_.diff xts [bv_of rty1]
              else
                xts
            in
            subst xts rty1,
            subst xts' rty2)
         xs)

let set_base_cond rty t =
  match rty with
  | Base(x, c, _) ->
    Base(x, c, t)
  | Fun(_) ->
    assert false


let rename xys rty =
  let xts = List.map (fun (x, y) -> x, Term.mk_var y) xys in
  let rec aux rty =
    match rty with
    | Base(x, c, t) ->
      let y = try List.assoc x xys with Not_found -> x in
      Base(y, c, Formula.subst xts t)
    | Fun(xs) ->
      Fun
        (List.map
           (fun (rty1, rty2) ->
              aux rty1, aux rty2)
           xs)
  in
  aux rty

let new_var =
  let cnt = ref 0 in
  fun () -> cnt := !cnt + 1; Idnt.make ("v" ^ (string_of_int !cnt))

let canonize rty =
  rename (fresh_names new_var rty) rty
let canonize =
  Logger.log_block1
    "RefType.canonize"
    canonize

let merge tys =
  match tys with
  | Fun(_) :: _ ->
    Fun
      (List.concat_map
         (function Fun(xs) -> xs | _ -> assert false)
         tys)
  | [ty] -> ty
  | [] -> raise Not_found (*Fun []*)
  | _ ->
    Format.printf
      "non-function types: @[<hv>%a@]@,"
      (List.pr pr " /\\@ ") tys;
    assert false

let pred_of_var env x =
  PredVar.make x (visible_vars env x)

let pva_of_var env x =
  Pva.make
    x
    (List.map
       (fun (x, ty) -> Term.mk_var x, ty)
       (visible_vars env x))

let rec mk_template flag env x =
  let ty = env x in
  let n = Type.arity_of ty in
  if n = 0 then
    if Type.is_ext ty then
      Type.let_ext
        ty
        (fun id ->
           Base(x, TypConst.Ext(id), Formula.mk_true))
    else if Type.is_base ty then
      Type.let_base
        ty
        (fun c ->
           Base
             (x,
              c,
              if flag then
                Pva.to_formula
                  (pva_of_var env x)
              else
                Formula.mk_true))
    else
      assert false
  else
    let j =
      try
        let Idnt.T(_, _, j) = find_last_base_exc env (x, -1) in
        j
      with Not_found ->
        -1(* reachable here *)
        (*Format.printf "%a@," Idnt.pr x;
            assert false*)
    in
    mk_fun
      (List.init
         n
         (fun i -> mk_template
             (i = j)
             env
             (Idnt.T(x, -1, i))) @
       [mk_template false env (Idnt.T(x, -1, n))])
let mk_template = mk_template false

let rec pvars rty =
  match rty with
  | Base(x, c, phi) ->
    begin
      try
        phi
        |> Pva.of_formula
        |> Pva.pvar_of
        |> fst
        |> List.return
      with Global.NoMatch _ -> []
    end
  | Fun(xs) ->
    List.concat_map
      (fun (rty1, rty2) ->
         pvars rty1 @ pvars rty2)
      xs
  | _ -> assert false

let rec env_ty args rty =
  match args, rty with
  | [], _ ->
    [], rty
  | Pattern.V(arg) :: args', Fun([rty1, rty2]) ->
    let xts =
      if is_base rty1(* || is_adt rty1*) then
        [bv_of rty1, Term.mk_var arg]
      else
        []
    in
    let env, rty' = env_ty args' (subst xts rty2) in
    (Idnt.string_of(*@todo*) arg, rty1) :: env, rty'
