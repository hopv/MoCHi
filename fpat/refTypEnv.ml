open Combinator
open Util

(** Refinement Type environments *)

type elem =
  | Env of Idnt.t * RefTyp.t
  | EFormula of Formula.t
type t = elem list (** head is the newest *)


(** {6 Printers} *)

let pr_elem ppf  = function
  | Env (x,ty) ->
    Format.fprintf ppf "@[%a : %a@]" Idnt.pr x RefTyp.pr ty
  | EFormula p ->
    Format.fprintf ppf "@[%a@]" Formula.pr p

let string_of_elem elem =
  pr_elem Format.str_formatter elem;
  Format.flush_str_formatter ()

let pr ppf tenv =
  Format.fprintf ppf "%a" (List.pr pr_elem ",@ ") (*List.rev*)tenv

let pr_compact ppf tenv =
  Format.fprintf ppf "%a" (List.pr pr_elem ",") tenv

(** {6 Morphisms} *)
let let_bind f = function
  | Env(x, ty) -> f x ty
  | _ -> assert false
let let_formula f = function
  | EFormula p -> f p
  | _ -> assert false

let apply id f =
  List.map (function Env(x, ty) -> Env(x, if x = id then f ty else ty) | t -> t)
let map_type f = List.map (function Env(x, ty) -> Env(x, f ty) | t -> t)
let map = List.map

(** {6 Auxiliary constructors} *)

let of_formula p = [EFormula p]
let of_tenv = List.map (fun (x, ty) -> Env(x, RefTyp.of_simple_type ty))
let of_rty_env = List.map (fun (x, ty) -> Env(x, ty))

let of_tenv_with_template tys =
  let aux (id, ty) =
    let ty = RefTyp.of_simple_type ty in
    let rty = RefTyp.mk_template id [] ty in
    id, rty
  in
  tys |> List.map aux |> of_rty_env
let of_tenv_with_template =
  Logger.log_block1 "RefTypEnv.of_tenv_with_template"
    ~after:(Logger.printf "output: %a" pr)
    of_tenv_with_template

(** make a refinement type template with a predicate variable for return type
    e.g. from "map : (int -> int) -> list -> list",
         make "map : (f : (x1:int) -> int) ->
                     (l1:list) ->
                     {l2:list | map f l1 l2}" *)
let of_tenv_with_simple_template tys =
  tys
  |> List.map
    (fun (x, t) ->
       let ty = RefTyp.of_simple_type t in
       let args, ret = RefTyp.args_ret ty in
       let env =
         args |> List.map (fun (x, rty) -> x, RefTyp.to_simple_type rty)
       in
       let ty =
         RefTyp.mk_fun_args_ret_rty args
           (RefTyp.mk_template (Idnt.ret_args x 0 0 |> fst) env ret)
           (* avoiding name confusion on typenv @todo *)
       in
       Env (x, ty))
let of_tenv_with_simple_template =
  Logger.log_block1 "RefTypEnv.of_tenv_with_simple_template"
    ~after:(Logger.printf "output: %a" pr)
    of_tenv_with_simple_template

(** make a refinement type template with predicate variables for the
    last argument type and return type
    e.g. from "map : (int -> int) -> list -> list", make
    "map : (f : (x1:{x1':int| f[0] (x1')}) ->
           {x2:int| f[1] (x1)(x2)}) ->
           (l1:{l:list | map[0] (l)}) -> {l2:list | (map (l1)(l2))}"
*)
let rec of_tenv_with_precondition_template env tys =
  tys
  |> List.map
    (fun (x, t) ->
       let ty = RefTyp.of_simple_type t in
       let args, ret_ty = RefTyp.args_ret ty in
       let args' =
         let rec args_with_template args env' =
           match args with
           | [] -> []
           | (id, RefTyp.Fun(_,_,_,_) as hd) :: tl ->
             let [Env(x, ty)] =
               of_tenv_with_precondition_template
                 env'
                 [id, RefTyp.to_simple_type (snd hd)]
             in
             (x, ty) :: args_with_template tl (env' @ [(x, ty)])
           | hd :: tl -> hd :: args_with_template tl (env' @ [hd])
         in
         let args = args_with_template args env in
         let init, last = List.initial_last args in
         let last =
           match last with
           | (id, RefTyp.Fun(_,_,_,_) as arg) -> arg
           | rty ->
             Pair.map_snd
               (RefTyp.mk_template
                  (Idnt.ret_args x 0 0 |> fst)
                  (List.map (Pair.map_snd RefTyp.to_simple_type) (env @ init)))
               rty
         in
         init @ [last]
       in
       let ty =
         RefTyp.mk_fun_args_ret_rty
           args'
           (RefTyp.mk_template (Idnt.ret_args x 0 1 |> fst)
              (List.map (Pair.map_snd RefTyp.to_simple_type) (env @ args'))
              ret_ty)
       in
       Env (x, ty))
let of_tenv_with_precondition_template tys =
  of_tenv_with_precondition_template [] tys
let of_tenv_with_precondition_template =
  Logger.log_block1 "RefTypEnv.of_tenv_with_precondition_template"
    ~after:(Logger.printf "output: %a" pr)
    of_tenv_with_precondition_template


(** {6 Operators} *)

let rty_env_of tenv =
  List.fold_left
    (fun y -> function Env(x, ty) -> (x, ty) :: y | _ -> y)
    [] tenv
  |> List.rev

(** @param x is a structured variable
    @return the type of x *)
let lookup tenv x =
  match x with
  | Idnt.V(_) | Idnt.C(_) -> List.assoc x (rty_env_of tenv)
  | _ -> raise Not_found
(** @param x is a structured variable
    @return the type of x *)
let lookupF tenv x =
  try lookup tenv x
  with Not_found ->
    Format.printf "type of %a not found@.  tenv: %a@." Idnt.pr x pr tenv;
    assert false

let subst_pvars psub =
  List.map
    (function
      | Env(x, rty) -> Env(x, RefTyp.subst_pvars psub rty)
      | EFormula(phi) -> EFormula(CunFormula.subst_pvars psub phi))

let subst tsub =
  List.map
    (function
      | Env(x, rty) -> Env(x, RefTyp.subst tsub rty)
      | EFormula(phi) -> EFormula(Formula.subst tsub phi))

let alpha xts =
  List.map
    (function
      | Env(x,ty) -> Env(x,RefTyp.alpha [] ty)
      | EFormula p -> EFormula p)

let domain =
  List.fold_left
    (fun acc -> function
       | Env(x, RefTyp.Base(_, ty, _)) ->
         (x, ty) :: acc
       | _ -> acc)
    []

let member tenv x =
  List.exists
    (function
      | Env (id, _) when Idnt.equiv id x -> true
      | _ -> false)
    tenv

let fpvs_elem = function
  | Env (_, rty) -> RefTyp.fpvs rty
  | EFormula phi -> Formula.fpvs phi

let fpvs = List.concat_map fpvs_elem

(*
type elem =
  A of Idnt.t * RefTypSchema.t
| B of Formula.t
type t = elem list

let pr_binding ppf (x, s) =
  Format.fprintf ppf "%a: %a"
    Idnt.pr x
    RefTypSchema.pr s

let pr_elem ppf = function
| A(x, s) ->
    pr_binding ppf (x, s)
| B(phi) ->
    Formula.pr ppf phi




let rec fv env =
  match env with
    [] ->
      []
  | (A(id, sigma))::env' ->
      (TypeSchema.fv sigma) @ (Util.diff (fv env') [id])
  | (B(phi))::env' ->
      (Fol.fv phi) @ (fv env')

let rec ftv env =
  match env with
    [] ->
      []
  | (A(_, sigma))::env' ->
      (TypeSchema.ftv sigma) @ (ftv env')
  | (B(_))::env' ->
      ftv env'

let generalize tau env =
  let ids = List.unique (Util.diff (ExpType.ftv tau) (ftv env)) in
  TypeSchema.Forall([ids, tau])


let rec simplify env =
  match env with
    [] ->
      []
  | (A(id, sigma))::env' ->
      (A(id, TypeSchema.simplify sigma))::(simplify env')
  | (B(phi))::env' ->
      (B(Fol.simplify phi))::(simplify env')

*)

let arity_of rtenv x = lookupF rtenv x |> RefTyp.arity

let rec formula_of rtenv acc =
  match rtenv with
  | [] -> acc
  | Env(x1, RefTyp.Base(x2, _, phi)) :: rest
  | Env(x1, RefTyp.Fun(_, _, _, (x2, phi))) :: rest ->
    if Idnt.equiv x1 x2
    then formula_of rest (phi :: acc)
    else formula_of rest (Formula.subst [x2, Term.mk_var x1] phi :: acc)
  | EFormula phi :: rest -> formula_of rest (phi :: acc)
let formula_of rtenv = formula_of rtenv [] |> Formula.band


(* update base type of refinement type templates (typed unknown with
   ADT) by using simple types obtained from OCaml *)
let update_base_types_of_templates ((tmpls, constr), (progs, dtyps)) =
  let rec rty_map rty ty =
    match rty with
    | RefTyp.Fun(x, rty1, rty2, phi) when Type.is_fun ty ->
      let _, [t1; t2] = Type.fun_args ty in
      RefTyp.Fun(x, rty_map rty1 t1, rty_map rty2 t2, phi)
    | _ -> rty
  in
  let aux tenv rtenv =
    match rtenv with
    | Env (id,  rty) when List.mem_assoc id tenv ->
      let ty_args, ty_ret = TypEnv.lookup tenv id |> Type.args_ret in
      let args, ret = RefTyp.args_ret rty in
      let args, ret =
        (List.map2 (fun (id, rty) ty -> id, rty_map rty ty) args ty_args),
        (rty_map ret ty_ret)
      in
      Env (id, RefTyp.mk_fun_args_ret_rty args ret)
    | _ -> rtenv
  in
  let env = List.map snd progs |> List.concat in
  (* @todo maybe happen ill overwriting *)
  let env = env @ (List.concat_map snd dtyps) in
  (* for ADT constructors refinement types *)
  (List.map (aux env) tmpls, constr), (progs, dtyps)
