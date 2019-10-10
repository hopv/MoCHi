
open Util
open CEGAR_type

exception NoProgress
exception CannotDiscoverPredicate
exception NonLinear

type var = string

type counterexample = int list

module VarSet =
  Set.Make(
    struct
      type t = var
      let compare = compare
    end)

type const =
  | Temp of string (* for temporary use *)
  | Unit
  | True
  | False
  | Char of char
  | String of string
  | Float of float
  | Int32 of int32
  | Int64 of int64
  | Nativeint of nativeint
  | Rand of base * int option
  | And
  | Or
  | Not
  | Lt
  | Gt
  | Leq
  | Geq
  | EqUnit
  | EqBool
  | EqInt
  | CmpPoly of string * string
  | Int of int
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Tuple of int
  | Proj of int * int (* Proj(n,i): 0 <= i < n *)
  | If (* for abstraction and model-checking *)
  | Bottom
  | Label of int
  | TreeConstr of int * string
  | CPS_result


and t =
  | Const of const
  | Var of var
  | App of t * t
  | Let of var * t * t (*** for temporary use ***)
  | Fun of var * typ option * t (*** for temporary use ***)


and event = Event of string | Branch of int

(*
and ce_node = BranchNode of int | EventNode of string
*)
and ce_node = int
and ce = ce_node list



and fun_def = var * var list * t * event list * t
and typ = t CEGAR_type.t
and env = (var * typ) list
and attr = ACPS
and prog = {env:env; defs:fun_def list; main:var; info:info}
and info =
  {attr : attr list;
   exparam_orig : prog option;
   non_rec : (var * t) list;
   orig_fun_list : var list;
   inlined : var list;
   pred_share : (var * int list * int list list * var * int list) list;
   fairness : Fair_termination_type.fairness option}

let init_info =
  {attr = [];
   exparam_orig = None;
   non_rec = [];
   orig_fun_list = [];
   inlined = [];
   pred_share = [];
   fairness = None}

let coeff_suffix = "_COEF"
let is_extra_coeff_name s = Str.string_match (Str.regexp @@ Format.sprintf ".*%s.*" coeff_suffix) s 0

let prefix_randint = "#randint"
let make_randint_name n = Format.sprintf "%s_%d" prefix_randint n
let decomp_randint_name s =
  try
    let s1,s2 = String.split s "_" in
    assert (s1 = prefix_randint);
    int_of_string s2
  with _ -> raise (Invalid_argument "decomp_randint_name")
let is_randint_var s =
  try
    ignore @@ decomp_randint_name s;
    true
  with _ -> false


let prefix_randint = "#randint"
let make_randint_name n = Format.sprintf "%s_%d" prefix_randint n
let decomp_randint_name s =
  try
    let s1,s2 = String.split s "_" in
    assert (s1 = prefix_randint);
    Some (int_of_string s2)
  with _ -> None
let is_randint_var s =
  Option.is_some @@ decomp_randint_name s

let prefix_randint_label = "randint"
let make_randint_label n = Format.sprintf "%s_%d" prefix_randint_label n
let decomp_randint_label s =
  try
    let s1,s2 = String.split s "_" in
    assert (s1 = prefix_randint_label);
    int_of_string s2
  with _ -> raise (Invalid_argument "decomp_randint_label")
let is_randint_label s =
  try
    ignore @@ decomp_randint_label s;
    true
  with _ -> false


let _Const c = Const c
let _Var x = Var x
let _App t1 t2 = App(t1,t2)
let _Let x t1 t2 = Let(x,t1,t2)
let _Fun x ?typ t = Fun(x, typ, t)


let new_id name = Id.to_string (Id.new_var ~name Type.typ_unknown)
let decomp_id s =
  try
    let len = String.length s in
    let i = String.rindex s '_' in
    String.sub s 0 i, int_of_string (String.sub s (i+1) (len-i-1))
  with Failure "int_of_string" | Not_found -> s, 0
let add_name x s =
  let name,n = decomp_id x in
  if n <> 0
  then name ^ s ^ "_" ^ string_of_int n
  else name ^ s
let id_name x = fst (decomp_id x)
let rename_id s =
  let name = id_name s in
  name ^ "_" ^ string_of_int (Id.new_int ())





let make_app t ts = List.fold_left (fun t1 t2 -> App(t1, t2)) t ts
let make_fun xs t =
  let f = new_id "f" in
  [f, xs, Const True, t], f
let make_annot_fun x typ t = Fun(x, Some typ, t)
let make_fun_temp xs t = List.fold_right (fun x t -> Fun(x,None,t)) xs t
let make_if t1 t2 t3 =
  match t1 with
  | Const True -> t2
  | Const False -> t3
  | _ -> make_app (Const If) [t1;t2;t3]
let make_int n = Const (Int n)
let make_br t1 t2 = make_if (Const (Rand(TBool, None))) t1 t2
let make_and t1 t2 =
  match t1,t2 with
  | Const True, t
  | t, Const True -> t
  | Const False, _ -> Const False
  | _ -> make_app (Const And) [t1; t2]
let make_ands ts = List.fold_right make_and ts (Const True)
let make_or t1 t2 =
  match t1,t2 with
  | Const False, t
  | t, Const False -> t
  | Const True, _ -> Const True
  | Var _, _ when t1 = t2 -> t1
  | _ -> make_app (Const Or) [t1; t2]
let make_ors ts = List.fold_right make_or ts (Const False)
let make_not t = App(Const Not, t)
let make_not_s t =
  match t with
  | Const True -> Const False
  | Const False -> Const True
  | App(Const Not, t) -> t
  | _ -> make_not t
let make_imply t1 t2 = make_or (make_not_s t1) t2
let make_geq t1 t2 = make_app (Const Geq) [t1; t2]
let make_lt t1 t2 = make_app (Const Lt) [t1; t2]
let make_gt t1 t2 = make_app (Const Gt) [t1; t2]
let make_leq t1 t2 = make_app (Const Leq) [t1; t2]
let make_geq t1 t2 = make_app (Const Geq) [t1; t2]
let make_eq_int t1 t2 = make_app (Const EqInt) [t1; t2]
let make_eq_bool t1 t2 =
  match t1,t2 with
  | Const False, t
  | t, Const False -> make_not t
  | Const True, t
  | t, Const True -> t
  | _ -> make_app (Const EqBool) [t1; t2]
let make_add t1 t2 = make_app (Const Add) [t1; t2]
let make_sub t1 t2 = make_app (Const Sub) [t1; t2]
let make_mul t1 t2 = make_app (Const Mul) [t1; t2]
let make_div t1 t2 = make_app (Const Div) [t1; t2]
let make_mod t1 t2 = make_app (Const Mod) [t1; t2]
let make_label n t = make_app (Const (Label n)) [t]
let make_proj n i t = make_app (Const (Proj(n,i))) [t]
let make_tuple ts = make_app (Const (Tuple (List.length ts))) ts
let make_let bindings t = List.fold_right (Fun.uncurry _Let) bindings t

let make_tree label ts = make_app (Const (TreeConstr(List.length ts, label))) ts

let rec add_bool_labels leaf = function
  | [] -> leaf
  | b::bs -> make_tree (string_of_bool b) [add_bool_labels leaf bs]

let make_br_exists n = function
  | [] -> assert false
  | [(bs, t)] -> make_tree (make_randint_label n) [add_bool_labels t bs]
  | (bs, t)::xs ->
    let make_br_exists_aux t1 (bs2, t2) = make_tree "br_exists" [t1; (add_bool_labels t2 bs2)] in
    make_tree (make_randint_label n) [List.fold_left make_br_exists_aux (add_bool_labels t bs) xs]


let arg_num typ = arg_num (Const Unit) typ


let rec get_fv = function
  | Const _ -> StringSet.empty
  | Var x -> StringSet.singleton x
  | App(t1, t2) -> StringSet.union (get_fv t1) (get_fv t2)
  | Let(x,t1,t2) -> StringSet.union (get_fv t1) (StringSet.remove x @@ get_fv t2)
  | Fun(x,_,t) -> StringSet.remove x (get_fv t)
let get_fv_list ts = List.fold_left (fun s t -> StringSet.union s (get_fv t)) StringSet.empty ts
let get_fv t = StringSet.elements @@ get_fv t
let get_fv_list ts = StringSet.elements @@ get_fv_list ts



let rec get_typ_arity = function
  | TFun(typ1,typ2) -> 1 + get_typ_arity (typ2 (Const Unit))
  | typ -> 0


let decomp_var = function
  | Var x -> Some x
  | _ -> None
let rec decomp_app = function
  | App(t1,t2) ->
      let t,ts = decomp_app t1 in
      t, ts@[t2]
  | t -> t, []
let rec decomp_fun = function
  | Fun(x,_,t) ->
      let xs,t = decomp_fun t in
      x::xs, t
  | t -> [], t
let rec decomp_annot_fun acc = function
  | Fun(x, typ, t) -> decomp_annot_fun ((x,typ)::acc) t
  | t -> List.rev acc, t
let decomp_annot_fun t = decomp_annot_fun [] t
let rec decomp_tfun ?(xs=None) = function
  | TFun(typ1,typ2) ->
      let arg,xs' =
        match xs with
        | None -> Const Unit, None
        | Some [] -> assert false
        | Some (x::xs') -> x, Some xs'
      in
      let typs,typ = decomp_tfun ~xs:xs' (typ2 arg) in
      typ1::typs, typ
  | typ -> [], typ
let rec decomp_tfun_env = function
  | TFun(typ1,typ2) ->
      let x = new_id "x" in
      let typs,typ = decomp_tfun_env (typ2 @@ Var x) in
      (x,typ1)::typs, typ
  | typ -> [], typ
let rec decomp_let = function
  | Let(x,t1,t2) ->
      let bindings,t2' = decomp_let t2 in
      (x,t1)::bindings, t2'
  | t -> [], t

let rec decomp_ands t =
  match decomp_app t with
  | Const And, [t1;t2] -> decomp_ands t1 @ decomp_ands t2
  | _ -> [t]
let rec decomp_ors t =
  match decomp_app t with
  | Const Or, [t1;t2] -> decomp_ors t1 @ decomp_ors t2
  | _ -> [t]


let is_app_randint ?(is_read_int=false) t =
  match t with
  | App _ ->
      let t',ts = decomp_app t in
      begin
        match t' with
        | Const (Rand (TInt, Some _)) -> true
        | Const (Rand (TInt, _)) -> not is_read_int
        | _ -> false
      end
  | _ -> false

let is_app_read_int = is_app_randint ~is_read_int:true

let get_ext_funs {env; defs} =
  env
  |> List.filter_out (fun (f,_) -> List.exists (fun (g,_,_,_,_) -> f = g) defs)
  |> List.map fst

let get_ext_fun_env prog =
  let ext_funs = get_ext_funs prog in
  List.map (fun f -> f, List.assoc f prog.env) ext_funs


let rec size t =
  match t with
  | Const _ -> 1
  | Var _ -> 1
  | App(t1, t2) -> 1 + size t1 + size t2
  | Let _ -> unsupported "CEGAR_syntax.size Let"
  | Fun(_,_,t) -> 1 + size t

let prog_size prog =
  List.fold_left (fun sum (f,xs,t1,e,t2) -> sum + List.length xs + size t1 + size t2) 0 prog.defs

let randint_ID_map = ref (fun _ -> "no corresponding identifier")
let rec is_rand = function
  | App(t, _) -> is_rand t
  | Const(Rand(TInt, id)) -> id
  | _ -> None
let add_ID_map r = function
  | Some(n) ->
    let m = !randint_ID_map in randint_ID_map := fun x -> if x=n then r else m x
  | None -> ()
let rec make_ID_map_fd = function
  | [] -> ()
  | (r,_,_,_,body)::ds -> add_ID_map r (is_rand body); make_ID_map_fd ds
let make_ID_map {defs=defs} = make_ID_map_fd defs


(** collect events that appear in HORS *)
let gather_events defs =
  let aux (_,_,_,es,_) =
    let aux' = function
      | Event s -> s
      | _ -> assert false in
    List.map aux' es in
  List.flatten_map aux defs
