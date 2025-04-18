open Util
open CEGAR_syntax
open CEGAR_type

module Debug = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

module S = Syntax
module U = Term_util

module Print = struct
  include Print_
  include CEGAR_print
end

type ext_path_part = Positive | Negative | Do_not_Care
type ext_path = ext_path_part list

exception TypeBottom
exception Type_not_found of var

let const_of_bool b = if b then True else False
let type_not_found x = raise (Type_not_found x)
let map_body_def f def = { def with body = f def.body }
let map_def_prog f prog = { prog with defs = List.map f prog.defs }
let map_body_prog f prog = map_def_prog (map_body_def f) prog

let rec subst x t fv t' =
  let sbst = subst x t fv in
  match t' with
  | Const c -> Const c
  | Var y when x = y -> t
  | Var y -> Var y
  | App (t1, t2) -> App (sbst t1, sbst t2)
  | Let (y, t1, t2) when x = y -> Let (y, sbst t1, t2)
  | Let (y, t1, t2) -> Let (y, sbst t1, sbst t2)
  | Fun (y, typ, t1) when x = y -> Fun (y, typ, t1)
  | Fun (y, typ, t1) ->
      if List.exists (( = ) y) fv then
        let y' = rename_id y in
        Fun (y', typ, sbst @@ subst y (Var y') [ y' ] t1)
      else Fun (y, typ, sbst t1)

let subst x t t' = subst x t (get_fv t) t'
let subst_var x y t = subst x (Var y) t

let rec subst_map' map = function
  | Const c -> Const c
  | Var x -> StringMap.find_default (Var x) x map
  | App (t1, t2) -> App (subst_map' map t1, subst_map' map t2)
  | Let (x, t1, t2) ->
      let map' = StringMap.remove x map in
      Let (x, subst_map' map' t1, subst_map' map' t2)
  | Fun (x, typ, t1) ->
      let map' = StringMap.remove x map in
      let typ' = Option.map (subst_typ_map' map') typ in
      Fun (x, typ', subst_map' map' t1)

and subst_typ' x t = function
  | TBase (b, ps) ->
      (* ASSUME: [ps] does not contain [x] *)
      TBase (b, List.map (subst x t) -| ps)
  | TFun (typ1, typ2) -> TFun (subst_typ' x t typ1, subst_typ' x t -| typ2)
  | TConstr (c, tys, ps) ->
      let c' = match c with TFixPred p -> TFixPred (subst x t -| p) | _ -> c in
      let tys' = List.map (subst_typ' x t) tys in
      let ps' = List.map (subst x t) -| ps in
      TConstr (c', tys', ps')

and subst_typ_map' map = function
  | TBase (b, ps) ->
      (* ASSUME: [ps] does not contain an element in Dom(map) *)
      TBase (b, List.map (subst_map' map) -| ps)
  | TFun (typ1, typ2) -> TFun (subst_typ_map' map typ1, subst_typ_map' map -| typ2)
  | _ -> assert false

let rec subst_map map = function
  | Const c -> Const c
  | Var x when List.mem_assoc x map -> List.assoc x map
  | Var x -> Var x
  | App (t1, t2) -> App (subst_map map t1, subst_map map t2)
  | Let (x, t1, t2) ->
      let map' = List.filter (fun (y, _) -> x <> y) map in
      Let (x, subst_map map' t1, subst_map map' t2)
  | Fun (x, typ, t1) ->
      let map' = List.filter (fun (y, _) -> x <> y) map in
      let typ' = Option.map (subst_typ_map map') typ in
      Fun (x, typ', subst_map map' t1)

and subst_typ x t = function
  | TBase (b, ps) ->
      (* ASSUME: y does not contain x *)
      TBase (b, List.map (subst x t) -| ps)
  | TFun (typ1, typ2) -> TFun (subst_typ x t typ1, subst_typ x t -| typ2)
  | TConstr (c, tys, ps) ->
      let c' = match c with TFixPred p -> TFixPred (subst x t -| p) | _ -> c in
      let tys' = List.map (subst_typ x t) tys in
      let ps' = List.map (subst x t) -| ps in
      TConstr (c', tys', ps')

and subst_typ_map map = function
  | TBase (b, ps) ->
      (* ASSUME: y does not contain an element in Dom(map) *)
      let ps' y = List.map (subst_map map) (ps y) in
      TBase (b, ps')
  | TFun (typ1, typ2) -> TFun (subst_typ_map map typ1, fun y -> subst_typ_map map (typ2 y))
  | _ -> assert false

let subst_def x t (f, xs, t1, t2) = (f, xs, subst x t t1, subst x t t2)

let rec arg_num = function
  | TBase _ -> 0
  | TFun (_, typ) -> 1 + arg_num (typ (Const Unit))
  | TConstr _ -> 0

let col_events prog =
  let rec aux t =
    match t with
    | Const (Event s) -> [ s ]
    | Const _ -> []
    | Var _ -> []
    | App (t1, t2) -> aux t1 @ aux t2
    | Let (_, t1, t2) -> aux t1 @ aux t2
    | Fun (_, _, t1) -> aux t1
  in
  List.flatten_map (fun { body } -> aux body) prog.defs

let pop_main { env; defs; main; info } =
  let compare_fun f g = compare (g = main, f) (f = main, g) in
  let compare_def { fn = f } { fn = g } = compare_fun f g in
  let compare_env (f, _) (g, _) = compare_fun f g in
  let env' = List.sort compare_env env in
  let defs' = List.sort compare_def defs in
  { env = env'; defs = defs'; main; info }

let rec get_arg_env typ xs =
  match (typ, xs) with
  | TFun (typ1, typ2), x :: xs ->
      let typ2 = typ2 @@ Var x in
      (x, typ1) :: get_arg_env typ2 xs
  | _ -> []

let rec put_arg_into_if_term t =
  match t with
  | Const c -> Const c
  | Var x -> Var x
  | App _ -> (
      match decomp_app t with
      | Const If, t1 :: t2 :: t3 :: ts ->
          let ts' = List.map put_arg_into_if_term ts in
          let t1' = put_arg_into_if_term t1 in
          let t2' = put_arg_into_if_term @@ make_app t2 ts' in
          let t3' = put_arg_into_if_term @@ make_app t3 ts' in
          make_if t1' t2' t3'
      | Const If, _ ->
          Format.eprintf "%a@." CEGAR_print.term t;
          assert false
      | t', ts ->
          let ts' = List.map put_arg_into_if_term ts in
          make_app t' ts')
  | Fun (x, typ, t) -> Fun (x, typ, put_arg_into_if_term t)
  | Let (x, t1, t2) -> Let (x, put_arg_into_if_term t1, put_arg_into_if_term t2)

let put_arg_into_if prog = map_body_prog put_arg_into_if_term prog

let eta_expand_def env ({ fn = f; args = xs; body = t2 } as def) =
  let d = arg_num (List.assoc f env) - List.length xs in
  let ys = List.init d (fun _ -> new_id "x") in
  let t2' = List.fold_left (fun t x -> App (t, Var x)) t2 ys in
  { def with fn = f; args = xs @ ys; body = t2' }
(* put_arg_into_term t2' *)

let eta_expand prog = { prog with defs = List.map (eta_expand_def prog.env) prog.defs }

let rec make_arg_let t =
  let desc =
    match t.S.desc with
    | S.Const c -> S.Const c
    | S.Var x -> S.Var x
    | S.App (t, ts) ->
        let f = Id.new_var ~name:"f__" t.S.typ in
        let xts = List.map (fun t -> (Id.new_var t.S.typ, t)) ts in
        let t' =
          let desc = S.App (U.make_var f, List.map (fun (x, _) -> U.make_var x) xts) in
          let typ = Type_util.Ty.unknown in
          S.make desc typ
        in
        (List.fold_left (fun t2 (x, t1) -> U.make_let [ (x, t1) ] t2) t' ((f, t) :: xts)).S.desc
    | S.If (t1, t2, t3) ->
        let t1' = make_arg_let t1 in
        let t2' = make_arg_let t2 in
        let t3' = make_arg_let t3 in
        S.If (t1', t2', t3')
    | S.Local (S.Decl_let bindings, t2) ->
        let bindings' = List.map (fun (f, t) -> (f, make_arg_let t)) bindings in
        let t2' = make_arg_let t2 in
        S.Local (S.Decl_let bindings', t2')
    | S.BinOp (op, t1, t2) ->
        let t1' = make_arg_let t1 in
        let t2' = make_arg_let t2 in
        S.BinOp (op, t1', t2')
    | S.Not t -> S.Not (make_arg_let t)
    | S.Fun _ -> assert false
    | S.Event _ -> assert false
    | _ -> assert false
  in
  S.make desc t.typ

let assoc_renv n env =
  try snd @@ List.find (fun (s, _) -> Some n = decomp_randint_name s) env
  with Not_found -> assert false

let decomp_rand_typ ?(xs = None) typ =
  let xs = Option.map (fun ys -> ys @ [ Const Unit ]) xs in
  match decomp_tfun ~xs typ with
  | typs, typ' when is_typ_result typ' ->
      let typs', typ'' = List.decomp_snoc typs in
      let preds =
        match typ'' with
        | TFun (TBase (TInt, preds), typ''') when is_typ_result @@ typ''' (Const Unit) -> preds
        | _ -> assert false
      in
      (typs', preds)
  | _ -> assert false

let rec col_rand_ids t =
  match t with
  | Const (Rand (TInt, Some n)) -> [ n ]
  | Const _ -> []
  | Var _ -> []
  | App (t1, t2) -> col_rand_ids t1 @ col_rand_ids t2
  | Let _ -> unsupported "col_rand_ids"
  | Fun _ -> unsupported "col_rand_ids"

let get_renv_aux prog i =
  let { fn = f; args = xs } =
    List.find (fun { body } -> List.mem i @@ col_rand_ids body) prog.defs
  in
  let typs, _ = decomp_tfun (List.assoc f prog.env) in
  let env = List.combine xs typs in
  List.filter (is_base -| snd) env

let get_renv prog =
  let rand_ids = List.filter_map (decomp_randint_name -| fst) prog.env in
  List.map (Pair.add_right @@ get_renv_aux prog) rand_ids

let make_renv n prog =
  let rand_ids = List.init n succ in
  let env = List.map (Pair.add_right @@ get_renv_aux prog) rand_ids in
  let make xtyps =
    let typ0 = TFun (TFun (typ_int, fun _ -> typ_result), fun _ -> typ_result) in
    List.fold_right (fun (x, typ1) typ2 -> TFun (typ1, subst_typ x -$- typ2)) xtyps typ0
  in
  List.map (Pair.map make_randint_name make) env

let nil _ = []

let int_binop_typ op =
  TFun
    ( TBase (TInt, nil),
      fun x -> TFun (TBase (TInt, nil), fun y -> TBase (TInt, fun r -> [ make_eq_int r (op x y) ]))
    )

let bool_binop_typ b = TFun (b, fun _ -> TFun (b, fun _ -> typ_bool ()))

let get_const_typ env = function
  | Unit -> typ_unit
  | True -> typ_bool ()
  | False -> typ_bool ()
  | Char _ -> typ_abst "char"
  | String _ -> typ_abst "string"
  | Float _ -> typ_abst "float"
  | Int32 _ -> typ_abst "int32"
  | Int64 _ -> typ_abst "int64"
  | Nativeint _ -> typ_abst "nativeint"
  | Rand (TInt, None) -> TFun (TFun (TBase (TInt, nil), fun _ -> typ_unit), fun _ -> typ_unit)
  | Rand (TInt, Some n) -> assoc_renv n env
  | Rand (TBool, _) -> TBase (TBool, nil)
  | Rand _ -> assert false
  | And -> bool_binop_typ !!typ_bool
  | Or -> bool_binop_typ !!typ_bool
  | Not -> TFun (!!typ_bool, fun _ -> !!typ_bool)
  | Lt -> bool_binop_typ (TBase (TInt, nil))
  | Gt -> bool_binop_typ (TBase (TInt, nil))
  | Leq -> bool_binop_typ (TBase (TInt, nil))
  | Geq -> bool_binop_typ (TBase (TInt, nil))
  | EqUnit -> bool_binop_typ (TBase (TUnit, nil))
  | EqBool -> bool_binop_typ !!typ_bool
  | EqInt -> bool_binop_typ (TBase (TInt, nil))
  | CmpPoly (typ, _) -> bool_binop_typ (TBase (TAbst typ, nil))
  | Int n -> TBase (TInt, fun x -> [ make_eq_int x (Const (Int n)) ])
  | Add -> int_binop_typ make_add
  | Sub -> int_binop_typ make_sub
  | Mul -> int_binop_typ make_mul
  | Div -> int_binop_typ make_div
  | Mod -> int_binop_typ make_mod
  | Tuple _ -> assert false
  | Proj _ -> assert false
  | If -> assert false
  | Bottom -> raise TypeBottom
  | Label _ -> assert false
  | Temp _ -> assert false
  | CPS_result -> typ_result
  | TreeConstr (n, _) ->
      let typ = typ_unit in
      let typs = List.make n typ in
      List.fold_right (fun typ1 typ2 -> TFun (typ1, fun _ -> typ2)) typs typ
  | Event _ -> TFun (typ_unit, fun _ -> typ_unit)
  | Empty -> assert false
  | MemSet -> assert false
  | AddSet -> assert false
  | Subset -> assert false
  | LinSet -> assert false

let rec get_typ env = function
  | Const c -> get_const_typ env c
  | Var x -> ( try List.assoc x env with Not_found -> type_not_found x)
  | App (Const (Label _), t) -> get_typ env t
  | App (Const (Rand (TInt, _)), t) -> (
      match get_typ env t with TFun (_, typ) -> typ (Var "") | _ -> assert false)
  | App (App (App (Const If, _), t1), t2) -> (
      try get_typ env t1 with TypeBottom -> get_typ env t2)
  | App (t1, t2) -> ( match get_typ env t1 with TFun (_, typ) -> typ t2 | _ -> assert false)
  | Let (x, t1, t2) ->
      let typ = get_typ env t1 in
      let env' = (x, typ) :: env in
      get_typ env' t2
  | Fun (x, Some typ, t) ->
      let typ' = get_typ ((x, typ) :: env) t in
      TFun (typ, fun y -> subst_typ x y typ')
  | Fun _ -> assert false

let rec get_arg_num = function TFun (_, typ) -> 1 + get_arg_num (typ (Const Unit)) | _ -> 0

let rec has_bottom = function
  | Var _ -> false
  | Const Bottom -> true
  | Const _ -> false
  | App (t1, t2) -> has_bottom t1 || has_bottom t2
  | _ -> assert false

let rec normalize_bool_term ?(imply = Fun.flip List.mem) t =
  match t with
  | Const c -> Const c
  | Var x -> Var x
  | App (Const Not, App (App (Const ((Lt | Gt | Leq | Geq) as op), t1), t2)) ->
      let op' = match op with Lt -> Geq | Gt -> Leq | Leq -> Gt | Geq -> Lt | _ -> assert false in
      normalize_bool_term ~imply (App (App (Const op', t1), t2))
  | App (Const Not, t1) -> (
      match normalize_bool_term ~imply t1 with
      | App (Const Not, t1') -> t1'
      | t1' -> App (Const Not, t1'))
  | App (App (Const EqBool, Const True), t) | App (App (Const EqBool, t), Const True) ->
      normalize_bool_term ~imply t
  | App (App (Const EqBool, Const False), t) | App (App (Const EqBool, t), Const False) ->
      make_not @@ normalize_bool_term ~imply t
  | App (App (Const And, _), _) as t -> (
      let rec decomp = function
        | App (App (Const And, t1), t2) -> decomp t1 @@@ decomp t2
        | t -> [ normalize_bool_term ~imply t ]
      in
      let rec aux ts1 = function
        | [] -> List.rev ts1
        | t :: ts2 -> if imply (ts1 @@@ ts2) t then aux ts1 ts2 else aux (t :: ts1) ts2
      in
      let ts' = aux [] (decomp t) in
      match ts' with
      | [] -> Const True
      | [ App (Const Not, t1); t2 ] when t1 = t2 -> Const False
      | [ t1; App (Const Not, t2) ] when t1 = t2 -> Const False
      | t' :: ts'' -> List.fold_left make_and t' ts'')
  | App (App (Const Or, _), _) as t -> (
      let rec decomp = function
        | App (App (Const Or, t1), t2) -> decomp t1 @@@ decomp t2
        | t -> [ normalize_bool_term ~imply t ]
      in
      let rec aux ts1 = function
        | [] -> ts1
        | t :: ts2 -> if imply (ts1 @@@ ts2) (make_not t) then aux ts1 ts2 else aux (t :: ts1) ts2
      in
      let ts' = aux [] (decomp t) in
      match ts' with [] -> Const False | t' :: ts'' -> List.fold_left make_or t' ts'')
  | App (App ((Const (EqInt | Lt | Gt | Leq | Geq) as op), t1), t2) -> (
      let neg xs = List.map (fun (x, n) -> (x, -n)) xs in
      let rec decomp = function
        | Const (Int n) -> [ (None, n) ]
        | Var x -> [ (Some (Var x), 1) ]
        | App (App (Const Add, t1), t2) -> decomp t1 @@@ decomp t2
        | App (App (Const Sub, t1), t2) -> decomp t1 @@@ neg (decomp t2)
        | App (App (Const Mul, t1), t2) -> (
            let xns1 = decomp t1 in
            let xns2 = decomp t2 in
            let reduce xns = List.fold_left (fun acc (_, n) -> acc + n) 0 xns in
            let is_const xns = List.for_all (fst |- ( = ) None) xns in
            match (is_const xns1, is_const xns2) with
            | false, false -> raise NonLinear
            | true, false ->
                let k = reduce xns1 in
                List.rev_map (fun (x, n) -> (x, n * k)) xns2
            | false, true ->
                let k = reduce xns2 in
                List.rev_map (fun (x, n) -> (x, n * k)) xns1
            | true, true -> [ (None, reduce xns1 * reduce xns2) ])
        | App (App (Const (Div | Mod), _), _) -> raise NonLinear
        | _ ->
            Format.eprintf "t: @[%a@." CEGAR_print.term t;
            unsupported "CEGAR_util.normalize_bool_term"
      in
      let xns1 = decomp t1 in
      let xns2 = decomp t2 in
      let xns =
        let compare (x1, _) (x2, _) =
          let aux = function
            | None -> (true, "")
            | Some (Var x) -> (false, x)
            | _ -> assert false
          in
          compare (aux x2) (aux x1)
        in
        List.sort compare (xns1 @@@ neg xns2)
      in
      let d = List.fold_left (fun d (_, n) -> Math.gcd d (abs n)) 0 xns in
      let xns' =
        let rec aux = function
          | [] -> []
          | (x, n) :: xns ->
              let xns1, xns2 = List.partition (fun (y, _) -> x = y) xns in
              let n' = List.fold_left (fun acc (_, n) -> acc + n) 0 ((x, n) :: xns1) in
              (x, n') :: aux xns2
        in
        xns
        |> List.filter (fun (_, n) -> n <> 0)
        |> List.map (fun (x, n) ->
               assert (n mod d = 0);
               (x, n / d))
        |> aux
      in
      match xns' with
      | [] -> (
          match op with
          | Const (EqInt | Leq | Geq) -> Const True
          | Const (Lt | Gt) -> Const False
          | _ -> assert false)
      | (x, n) :: xns'' ->
          let xns = List.rev xns'' in
          let op', t1', t2' =
            let aux = function
              | None, n -> Const (Int n)
              | Some x, 1 -> x
              | Some x, n -> make_mul (make_int n) x
            in
            let t1, xns', op' =
              if n < 0 then
                let op' =
                  match op with
                  | Const EqInt -> Const EqInt
                  | Const Lt -> Const Gt
                  | Const Gt -> Const Lt
                  | Const Leq -> Const Geq
                  | Const Geq -> Const Leq
                  | _ -> assert false
                in
                (aux (x, -n), xns, op')
              else (aux (x, n), neg xns, op)
            in
            let ts = List.map aux xns' in
            let t2 =
              match ts with
              | [] -> Const (Int 0)
              | t :: ts' ->
                  let make_add_sub t1 t2 =
                    match t2 with
                    | Const (Int n) when n < 0 -> make_sub t1 (make_int (-n))
                    | App (App (Const Mul, Const (Int n)), t2') when n < 0 ->
                        make_sub t1 (make_mul (make_int (-n)) t2')
                    | _ -> make_add t1 t2
                  in
                  List.fold_left make_add_sub t ts'
            in
            (op', t1, t2)
          in
          make_app op' [ t1'; t2' ])
  | App (t1, t2) -> App (normalize_bool_term ~imply t1, normalize_bool_term ~imply t2)
  | Let _ -> assert false
  | Fun (x, typ, t) -> Fun (x, typ, normalize_bool_term ~imply t)

let normalize_bool_term ?(imply = fun env t -> List.mem t env) t =
  try normalize_bool_term ~imply t with NonLinear -> t

let assoc_fun_def defs f =
  let make_fun xs t =
    let xs' = List.map rename_id xs in
    let map = List.map2 (fun x x' -> (x, Var x')) xs xs' in
    List.fold_right (fun x t -> Fun (x, None, t)) xs' (subst_map map t)
  in
  let defs' = List.filter (fun { fn = g } -> f = g) defs in
  match defs' with
  | [] -> assert false
  | [ { args = xs; cond = Const True; body = t } ] -> make_fun xs t
  | [ _ ] -> failwith "Not implemented: CEGAR_abst_CPS.assoc_fun_def"
  | [ { args = xs1; cond = t11; body = t12 }; { args = xs2; cond = t21; body = t22 } ]
    when make_not t11 = t21 ->
      assert (xs1 = xs2);
      make_fun xs1 (make_if t11 t12 t22)
  | [ { args = xs1; cond = t11; body = t12 }; { args = xs2; cond = t21; body = t22 } ]
    when t11 = make_not t21 ->
      assert (xs1 = xs2);
      make_fun xs1 (make_if t21 t22 t12)
  | { args = xs } :: _ ->
      assert (List.for_all (fun { args; cond } -> args = xs && cond = Const True) defs');
      let ts = List.map (fun { body } -> body) defs' in
      make_fun xs (List.fold_left make_br (List.hd ts) (List.tl ts))

let rec get_fv' = function
  | Const _ -> []
  | Var x -> [ x ]
  | App (t1, t2) -> get_fv' t2 @@@ get_fv' t1
  | Let (x, t1, t2) -> get_fv' t1 @@@ List.remove_all (get_fv' t2) x
  | Fun (x, _, t) -> List.remove_all (get_fv' t) x

(*
let get_fv_def' { args; body } =
  List.Set.(get_fv' body - args)
  |> List.classify
  |> List.map (fun xs -> (List.hd xs, List.length xs))

let create_tbl_num_occurrence id_of defs =
  let tbl = Hashtbl.create (List.length defs) in
  let add x y n =
    let x' = id_of x in
    let y' = id_of y in
    let m = Hashtbl.find_default tbl (x', y') 0 in
    Hashtbl.replace tbl (x', y') (n + m)
  in
  List.iter (fun ({ fn } as def) -> get_fv_def' def |> List.iter (fun (g, n) -> add fn g n)) defs;
  tbl

let approximate_used_num { defs } =
  let fs = defs |> List.map (fun { fn = f } -> f) |> List.unique in
  let _, id_of, map = assign_id_by_eq @@ ("_" :: fs) in
  let edges =
    defs
    |> List.map (fun ({ fn } as def) -> (fn, get_fv_def def))
    |> List.classify ~eq:(Eq.on fst)
    |> List.map (fun edges ->
           (fst (List.hd edges), List.fold_left (fun acc (_, deps) -> deps @@@ acc) [] edges))
    |> List.map (fun (f, fs) -> try (id_of f, List.map id_of fs) with Not_found -> assert false)
    |> List.flatten_map (fun (f, deps) ->
           if deps = [] then [ (f, -1) ] else List.map (Pair.pair f) deps)
  in
  let scc = Graph_wrapper.scc edges in
  let repr_of id =
    try if id < 0 then id else List.find (List.mem id) scc |> List.hd
    with Not_found ->
      Format.printf "id: %d@." id;
      assert false
  in
  let repr_id_of = repr_of -| id_of in
  let edges' = edges |> List.map (Pair.map_same repr_of) |> List.filter_out (fun (f, g) -> f = g) in
  let name_of =
    let rev_map = List.map Pair.swap map in
    fun id -> if id = -1 then "_" else List.assoc ~eq:( = ) id rev_map
  in
  Format.printf "map: %a@." Print.(list (string * int)) map;
  let g = Graph_wrapper.from_directed_edges edges' in
  let tbl = Hashtbl.create (List.length map) in
  let root =
    fs |> List.map repr_id_of |> List.filter (fun id -> List.for_all (snd |- ( <> ) id) edges')
  in

  List.iter (Hashtbl.add tbl -$- 1) root;
  let fv_tbl = create_tbl_num_occurrence repr_id_of defs in
  Format.printf "fv_tbl: %a@." Print.(list ((name_of |> string) * (name_of |> string) * int))
  @@ Hashtbl.to_list fv_tbl;
  let rec num_of f =
    if f = -1 then -1
    else
      try Hashtbl.find tbl f
      with Not_found ->
        let caller = List.filter_map (fun (g, f') -> if f = f' then Some g else None) edges' in
        let n =
          List.fold_left (fun acc g -> acc + (num_of g * Hashtbl.find fv_tbl (g, f))) 0 caller
        in
        Hashtbl.add tbl f n;
        n
  in
  let name_of id =
    try
      let f = try name_of id with Not_found -> assert false in
      Format.sprintf "%s:%d" f (num_of id)
    with Not_found -> assert false
  in
  let () = Graph_wrapper.save_as_dot ~name_of "deps.dot" g in
  exit 0
*)

let get_non_rec red_CPS { defs; env; main; info } =
  let orig_fun_list = info.orig_fun_list in
  let force = info.inlined in
  let non_rec =
    let not_fun_arg_copy { fn; args; body } =
      let env' = get_arg_env (List.assoc fn env) args @@@ env in
      let fv = get_fv' body in
      List.for_all (fun x -> is_base (List.assoc x env') || List.count (( = ) x) fv <= 1) args
    in
    let check ({ fn = f } as def) =
      let defs' = List.filter (fun { fn = g } -> f = g) defs in
      let used = List.count (fun { body } -> List.mem f @@ get_fv body) defs in
      f <> main
      && (List.for_all (fun { args; body } -> List.Set.(get_fv body <= args)) defs'
         || ((1 >= used || List.mem f force) && 2 >= List.length defs'))
      && if !Flag.Method.expand_nonrec_full then true else not_fun_arg_copy def
    in
    defs
    |> List.filter check
    |> List.map (fun { fn = f } -> f)
    |> List.unique
    |> List.rev_map (Pair.add_right (assoc_fun_def defs))
  in
  let non_rec' =
    if !Flag.PredAbst.expand_non_rec_init then non_rec
    else
      let orig_fun_list' = List.Set.(orig_fun_list - force) in
      List.filter_out (fun (f, _) -> List.mem f orig_fun_list') non_rec
  in
  let ( ++ ) = StringMap.union (fun _ _ _ -> assert false) in
  let update (finished, rest) =
    let map = finished ++ rest in
    let finished', rest' =
      StringMap.Labels.fold rest ~init:(finished, StringMap.empty)
        ~f:(fun ~key ~data:t (finished, rest) ->
          let t' = red_CPS @@ subst_map' map t in
          let add = StringMap.add key t' in
          if t' = t then (add finished, rest) else (finished, add rest))
    in
    (not (StringMap.is_empty rest'), (finished', rest'))
  in
  fixed_point_update update (StringMap.empty, StringMap.of_list non_rec')
  |> fst
  |> StringMap.to_list

let print_prog_typ' fm { env; defs; main; info } =
  let env' = List.filter_out (fun (f, _) -> List.mem_assoc f info.non_rec) env in
  CEGAR_print.prog_typ fm { env = env'; defs; main; info }

let eval_step_by_step prog =
  let assoc_fun_def defs f =
    let make_fun xs t =
      let xs' = List.map rename_id xs in
      let map = List.map2 (fun x x' -> (x, Var x')) xs xs' in
      List.fold_right (fun x t -> Fun (x, None, t)) xs' (subst_map map t)
    in
    let defs' = List.filter (fun { fn = g } -> f = g) defs in
    match defs' with
    | [ { args = xs; cond = Const True; body = t } ] -> make_fun xs t
    | [ _ ] -> failwith "Not implemented: CEGAR_abst_CPS.assoc_fun_def"
    | [ { args = xs1; cond = t11; body = t12 }; { args = xs2; cond = t21; body = t22 } ]
      when make_not t11 = t21 ->
        assert (xs1 = xs2);
        make_fun xs1 (make_if t11 t12 t22)
    | [ { args = xs1; cond = t11; body = t12 }; { args = xs2; cond = t21; body = t22 } ]
      when t11 = make_not t21 ->
        assert (xs1 = xs2);
        make_fun xs1 (make_if t21 t22 t12)
    | [ { args = xs1; cond = Const True; body = t12 }; { cond = Const True; body = t22 } ] ->
        make_fun xs1 @@ make_br t22 t12
    | _ ->
        Format.eprintf "LENGTH[%s]: %d@." f @@ List.length defs';
        assert false
  in
  let counter = ref 0 in
  let rec get_tf l_then l_else =
    Format.fprintf !Flag.Print.target "[%d] t/f?" !counter;
    if Option.is_some l_then then
      Format.fprintf !Flag.Print.target " (t -> %d?, " @@ Option.get l_then;
    if Option.is_some l_else then Format.fprintf !Flag.Print.target "f -> %d?)" @@ Option.get l_else;
    Format.fprintf !Flag.Print.target ": @?";
    match read_line () with
    | "t" ->
        Format.fprintf !Flag.Print.target "t@.";
        true
    | "f" ->
        Format.fprintf !Flag.Print.target "f@.";
        false
    | _ -> get_tf l_then l_else
  in
  let rec eval_cond t t_then t_else =
    match t with
    | Const True -> true
    | Const False -> false
    | Const (Rand (TBool, _)) ->
        let aux = function App (Const (Label n), _) -> Some n | _ -> None in
        incr counter;
        get_tf (aux t_then) (aux t_else)
    | App (App (App (Const If, t1), t2), t3) ->
        if eval_cond t1 t_then t_else then eval_cond t2 t_then t_else
        else eval_cond t3 t_then t_else
    | _ -> assert false
  in
  let rec eval t =
    if true then Color.printf Red "EVAL:@.";
    if true then Format.fprintf !Flag.Print.target "%a@." CEGAR_print.term t;
    (*    ignore @@ read_line ();*)
    match decomp_app t with
    | Const If, [ t1; t2; t3 ] -> if eval_cond t1 t2 t3 then eval t2 else eval t3
    | Const (Label n), [ t ] ->
        Color.printf Green "Label %d@." n;
        if false then ignore @@ read_line ();
        eval t
    | Fun (x, _, t1), t2 :: ts ->
        if true then Color.printf Blue "[%s |-> %a]@." x CEGAR_print.term t2;
        eval @@ make_app (subst x t2 t1) ts
    | Var f, ts ->
        let subst' x t1 t2 =
          if true then Color.printf Blue "[%s |-> %a]@." x CEGAR_print.term t1;
          subst x t1 t2
        in
        let xs, t' = decomp_fun @@ assoc_fun_def prog.defs f in
        eval @@ List.fold_right2 subst' xs ts t'
    | _ ->
        Color.printf Blue "%a@." CEGAR_print.term t;
        assert false
  in
  let t_main = assoc_fun_def prog.defs prog.main in
  eval t_main

let initialize_env prog = { prog with env = [] }

let rec has_no_effect t =
  match t with
  | Const _ -> true
  | Var _ -> true
  | App _ -> false
  | Let (_, t1, t2) -> has_no_effect t1 && has_no_effect t2
  | Fun _ -> true

let assign_id_to_rand prog =
  let count = ref 0 in
  let rec aux t =
    match t with
    | Const (Rand (TInt, None)) -> Const (Rand (TInt, None))
    | Const (Rand (TInt, Some _)) ->
        incr count;
        Const (Rand (TInt, Some !count))
    | Const c -> Const c
    | Var x -> Var x
    | App (t1, t2) -> App (aux t1, aux t2)
    | Let (x, t1, t2) -> Let (x, aux t1, aux t2)
    | Fun (x, typ, t) -> Fun (x, typ, aux t)
  in
  let prog' = map_body_prog aux prog in
  let env = make_renv !count prog' @ prog.env in
  { prog' with env }

let make_map_randint_to_preds prog =
  let env' = List.filter (is_randint_var -| fst) prog.env in
  let aux (f, typ) =
    let i = Option.get @@ decomp_randint_name f in
    let { args = xs } = List.find (fun { body } -> List.mem i @@ col_rand_ids body) prog.defs in
    let _, preds = decomp_rand_typ ~xs:(Some (List.map _Var xs)) typ in
    (i, preds)
  in
  List.map aux env'

let conv_path ext_ce =
  let aux = List.map (List.map (fun b -> if b then Positive else Negative)) in
  List.map (fun (n, bs) -> (n, aux bs)) ext_ce

let rec arrange_ext_preds_sequence = function
  | [] -> []
  | (r, bs) :: ext ->
      let rs, rest = List.partition (fun (f, _) -> f = r) ext in
      (r, bs :: List.map snd rs) :: arrange_ext_preds_sequence rest

let is_same_branching (_, _, ce1, _) (_, _, ce2, _) = ce1 = ce2

let rec group_by_same_branching = function
  | [] -> []
  | x :: xs ->
      let gr, rest = List.partition (is_same_branching x) xs in
      (x :: gr) :: group_by_same_branching rest

(*
r1: [Positive, Negative, Positive], r2: [Positive, Negative]
r1: [Positive, Negative, Negative], r2: [Positive, Negative]
->
(r1, 0, Positive), (r1, 1, Negative), (r1, 2, Positive), (r2, 0, Positive), (r2, 1, Negative)
(r1, 0, Positive), (r1, 1, Negative), (r1, 2, Negative), (r2, 0, Positive), (r2, 1, Negative)

*)
let remove_meaningless_pred path1 path2 =
  let bs1 =
    List.concat
    @@ List.concat_map
         (fun (n1, bss1) -> List.mapi (fun i bs -> List.mapi (fun j b -> (n1, i, j, b)) bs) bss1)
         path1
  in
  let bs2 =
    List.concat
    @@ List.concat_map
         (fun (n2, bss2) -> List.mapi (fun i bs -> List.mapi (fun j b -> (n2, i, j, b)) bs) bss2)
         path2
  in
  let aux acc (n', i', j', b1) (_, _, _, b2) =
    if b1 <> b2 then
      let modify =
        List.map (fun ((n, bss) as seq) ->
            if n = n' then
              ( n,
                List.mapi
                  (fun i bs ->
                    if i = i' then List.mapi (fun j b -> if j = j' then Do_not_Care else b) bs
                    else bs)
                  bss )
            else seq)
      in
      match acc with None -> Some modify | Some modify' -> Some (modify |- modify')
    else acc
  in
  match List.fold_left2 aux None bs1 bs2 with None -> None | Some modify -> Some (modify path1)

let rec found_and_merge_paths (_, _, _, path) = function
  | [] -> None
  | ((path', orig_ce, ce, ext_path) as p) :: ps -> (
      match remove_meaningless_pred path ext_path with
      | None -> (
          match found_and_merge_paths p ps with
          | None -> None
          | Some (merged_path, rest) -> Some (merged_path, p :: rest))
      | Some merged -> Some ((path', orig_ce, ce, merged), ps))

let rec merge_similar_paths_aux = function
  | [] -> []
  | p :: ps -> (
      match found_and_merge_paths p ps with
      | None -> p :: merge_similar_paths_aux ps
      | Some (merged_path, rest) -> merged_path :: merge_similar_paths_aux rest)

let rec merge_similar_paths l =
  let l' = merge_similar_paths_aux l in
  if List.length l = List.length l' then l else merge_similar_paths l'

let inlined_functions { info } = List.unique @@ List.map fst @@ info.non_rec

let rec col_app t =
  match t with
  | Const _ -> []
  | Var _ -> []
  | App _ -> (
      let hd, ts = decomp_app t in
      let apps = List.flatten_map col_app ts in
      match hd with Var f -> (f, ts) :: apps | _ -> apps)
  | Let _ -> unsupported "col_app"
  | Fun _ -> unsupported "col_app"

(* BUGGY *)
(* only remove trivially the same arguments *)
let elim_same_arg prog =
  let find_same_arg defs =
    let fs = List.map (fun def -> def.fn) defs in
    let apps =
      defs
      |> List.flatten_map (fun { cond; body = t } ->
             assert (col_app cond = []);
             col_app t)
      |> List.filter (fun (f, _) -> List.mem f fs)
    in
    let candidates =
      let aux f i t1 j t2 = if i < j && t1 = t2 then Some (f, i, j) else None in
      List.flatten_map
        (fun (f, ts) -> List.flatten_mapi (fun i t1 -> List.filter_mapi (aux f i t1) ts) ts)
        apps
    in
    let check f i j (g, ts) = f = g => (List.length ts > j && List.nth ts i = List.nth ts j) in
    List.filter (fun (f, i, j) -> List.for_all (check f i j) apps) candidates
  in
  let same_args = List.unique @@ find_same_arg prog.defs in
  let rec elim_arg (f, j) t =
    match t with
    | Const _ -> t
    | Var _ -> t
    | App _ ->
        let hd, ts = decomp_app t in
        let ts' = List.map (elim_arg (f, j)) ts in
        if hd = Var f then make_app hd @@ List.filteri (fun i _ -> i <> j) ts' else make_app hd ts'
    | Let _ -> unsupported "col_app"
    | Fun _ -> unsupported "col_app"
  in
  let elim_arg_def defs (f, i, j) =
    let elim { fn = g; args = xs; cond; body = t } =
      if g = f then (
        let x = List.nth xs i in
        let y = List.nth xs j in
        let xs' = List.filter_out (( = ) y) xs in
        Debug.printf "elim[%d,%d]: %s@." i j y;
        let cond' = subst y (Var x) cond in
        let t' = elim_arg (f, j) @@ subst y (Var x) t in
        { fn = g; args = xs'; cond = cond'; body = t' })
      else
        let t' = elim_arg (f, j) t in
        { fn = g; args = xs; cond; body = t' }
    in
    List.map elim defs
  in
  let rec elim_args_def defs same_args =
    match same_args with
    | [] -> defs
    | (_, i, j) :: same_args' when i = j -> elim_args_def defs same_args'
    | (f, i, j) :: same_args' ->
        let defs' = elim_arg_def defs (f, i, j) in
        let same_args'' =
          let pred k = if k > j then k - 1 else k in
          List.map
            (fun (g, i', j') -> if f = g then (f, pred i', pred j') else (g, i', j'))
            same_args'
        in
        elim_args_def defs' same_args''
  in
  let rec subst_arg_typ_aux j x typ =
    match typ with
    | TBase _ -> assert false
    | TFun (typ1, typ2) -> if j = 0 then typ2 x else TFun (typ1, subst_arg_typ_aux (j - 1) x -| typ2)
    | TConstr _ -> assert false
  in
  let rec subst_arg_typ i j typ =
    match typ with
    | TBase _ -> assert false
    | TFun (typ1, typ2) ->
        if i = 0 then TFun (typ1, fun x -> subst_arg_typ_aux (j - 1) x @@ typ2 x)
        else TFun (typ1, subst_arg_typ (i - 1) (j - 1) -| typ2)
    | TConstr _ -> assert false
  in
  let elim_arg_env env (f, i, j) =
    let elim (g, typ) =
      if g = f then
        let typ' = subst_arg_typ i j typ in
        (g, typ')
      else (g, typ)
    in
    List.map elim env
  in
  let rec elim_args_env env same_args =
    match same_args with
    | [] -> env
    | (_, i, j) :: same_args' when i = j -> elim_args_env env same_args'
    | (f, i, j) :: same_args' ->
        let env' = elim_arg_env env (f, i, j) in
        let same_args'' =
          let pred k = if k > j then k - 1 else k in
          List.map
            (fun (g, i', j') -> if f = g then (f, pred i', pred j') else (g, i', j'))
            same_args'
        in
        elim_args_env env' same_args''
  in
  Debug.printf "same_args: %a@."
    (List.print @@ fun fm (f, i, j) -> Format.fprintf fm "%s,%d,%d" f i j)
    same_args;
  let defs' = elim_args_def prog.defs same_args in
  let env' = elim_args_env prog.env same_args in
  { prog with defs = defs'; env = env' }

let rename_fun_arg =
  let rec tr t =
    match t with
    | Const c -> Const c
    | Var y -> Var y
    | App (t1, t2) -> App (tr t1, tr t2)
    | Let (y, t1, t2) -> Let (y, tr t1, tr t2)
    | Fun (y, typ, t1) ->
        let y' = new_id y in
        let t1' = subst_var y y' @@ tr t1 in
        Fun (y', typ, t1')
  in
  map_body_prog tr

let max_label { defs } =
  let rec aux t =
    match t with
    | Const (Label n) -> n
    | Const _ -> 0
    | Var _ -> 0
    | App (t1, t2) -> max (aux t1) (aux t2)
    | Let (_, t1, t2) -> max (aux t1) (aux t2)
    | Fun (_, _, t1) -> aux t1
  in
  List.fold_left (fun n { body } -> max n (aux body)) 0 defs

let rec exists_const c t =
  match t with
  | Const c' -> c = c'
  | Var _ -> false
  | App (t1, t2) -> exists_const c t1 || exists_const c t2
  | Let _ -> assert false
  | Fun _ -> assert false

let fun_of_binop = function
  | And -> make_and
  | Or -> make_or
  | Lt -> make_lt
  | Gt -> make_gt
  | Leq -> make_leq
  | Geq -> make_geq
  | EqBool -> make_eq_bool
  | EqInt -> make_eq_int
  | Add -> make_add
  | Sub -> make_sub
  | Mul -> make_mul
  | Div -> make_div
  | MemSet -> make_mem
  | AddSet -> make_addset
  | Subset -> make_subset
  | _ -> [%invalid_arg]

module Term = struct
  let ( @ ) = make_app
  let ( @@ ) = make_app
  let unit = Const Unit
  let true_ = Const True
  let tt = Const True
  let false_ = Const False
  let ff = Const False
  let int = make_int
  let var = _Var
  let vars = List.map _Var
  let let_ = _Let
  let fun_ = _Fun
  let br = make_br
  let if_ = make_if
  let event = make_event
  let ( = ) = make_eq_int
  let ( < ) = make_lt
  let ( > ) = make_gt
  let ( <= ) = make_leq
  let ( >= ) = make_geq
  let ( && ) = make_and
  let ( || ) = make_or
  let not = make_not
  let not' = make_not'
  let ( => ) t1 t2 = (not t1) || t2
  let ( + ) = make_add
  let ( - ) = make_sub
  let ( * ) = make_mul
  let ( / ) = make_div
  let ( mod ) = make_mod
  let ( |-> ) = subst

  let ( <| ) t1 op t2 = make_app (Const op) [ t1; t2 ]
  and ( |> ) mb t2 = mb t2

  let empty = Const Empty
  let mem = make_mem
  let addset = make_addset
  let subset = make_subset
  let linset = make_linset
end
