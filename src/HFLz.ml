open Util

type var = V of string [@@deriving show]
type op = Add | Sub | Mul | Div | Eq | Neq | Leq | Geq | Lt | Gt | And | Or [@@deriving show]

type hflz =
  | Bool of bool
  | Int of int
  | Var of var
  | Abs of var * hflz
  | App of hflz * hflz
  | Op of op * hflz * hflz
  | Forall of var * hflz
[@@deriving show]

type rule = { fn : var; args : var list; body : hflz } [@@deriving show]
type hes = rule list [@@deriving show]

let mk_var ~toplevel s =
  let s = Re2.replace_exn ~f:(fun _ -> "_") (Re2.create_exn "'") s in
  if List.mem s toplevel then V (String.uppercase_ascii s) else V s

let rec negate x =
  match x with
  | Bool b -> Bool (not b)
  | Op (Neq, x, y) -> Op (Eq, x, y)
  | Op (Eq, x, y) -> Op (Neq, x, y)
  | Op (Geq, x, y) -> Op (Lt, x, y)
  | Op (Leq, x, y) -> Op (Gt, x, y)
  | Op (Gt, x, y) -> Op (Leq, x, y)
  | Op (Lt, x, y) -> Op (Geq, x, y)
  | Op (And, x, y) -> Op (Or, negate x, negate y)
  | Op (Or, x, y) -> Op (And, negate x, negate y)
  | t ->
      Format.eprintf "Cannot negate %a@." pp_hflz t;
      assert false

(* transform e (if e1 then e2 else e3) to if e1 then e e2 else e e3.
   To fix these "ill"-formed CPS expressions that the preprocess encode_as_int introduced.
*)
let rec commuting_conversion (expr : CEGAR_syntax.t) (* TODO: unnecessary now? *) =
  let rec aux x (y : CEGAR_syntax.t) : CEGAR_syntax.t =
    match y with
    | App (App (App (Const If, a), b), c) ->
        (*App (App ((App (Const If, a)), b), c)*)
        App (App (App (Const If, a), aux x b), aux x c)
    | _ -> App (x, y)
  in
  match expr with
  | Let _ -> assert false
  | Var _ | Const _ -> expr
  | Fun (f, x, y) -> Fun (f, x, commuting_conversion y)
  | App (App (App (Const If, a), b), c) ->
      App (App (App (Const If, a), commuting_conversion b), commuting_conversion c)
  | App (x, y) ->
      let x' = commuting_conversion x in
      let y' = commuting_conversion y in
      aux x' y'

let make_or t1 t2 =
  if t1 = Bool true || t2 = Bool true then Bool true
  else if t1 = Bool false then t2
  else if t2 = Bool false then t1
  else Op (Or, t1, t2)

let make_and t1 t2 =
  if t1 = Bool false || t2 = Bool false then Bool false
  else if t1 = Bool true then t2
  else if t2 = Bool true then t1
  else Op (And, t1, t2)

let make_eq t1 t2 = match (t1, t2) with Int n, Int m -> Bool (n = m) | _ -> Op (Eq, t1, t2)

let hflz_of_cegar ~toplevel : CEGAR_syntax.t -> hflz =
  let mode = Flag.Reachability in
  let rec aux : CEGAR_syntax.t -> hflz =
   fun t ->
    match t with
    | Var v -> Var (mk_var ~toplevel v)
    | Let _ -> assert false
    | Const Unit -> Bool true
    | Const CPS_result -> (
        match mode with
        | NonTermination -> Bool false
        | Reachability -> Bool true
        | _ -> unsupported "HFLz.of_cegar: mode")
    | Const Bottom -> Bool true
    | Const True -> Bool true
    | Const False -> Bool false
    | Const (Int i) -> Int i
    | Const (Int32 i) -> Int (Int32.to_int i)
    | Const (Int64 i) -> Int (Int64.to_int i)
    | App (App (App (Const If, x), y), z) ->
        let x = aux x in
        make_and (make_or (negate x) (aux y)) (make_or x (aux z))
    | App (App (Const Add, x), y) -> Op (Add, aux x, aux y)
    | App (App (Const Sub, x), y) -> Op (Sub, aux x, aux y)
    | App (App (Const Mul, x), y) -> Op (Mul, aux x, aux y)
    | App (App (Const Div, x), y) -> Op (Div, aux x, aux y)
    | App (App (Const And, x), y) -> make_and (aux x) (aux y)
    | App (App (Const Or, x), y) -> make_or (aux x) (aux y)
    | App (App (Const Lt, x), y) -> Op (Lt, aux x, aux y)
    | App (App (Const Gt, x), y) -> Op (Gt, aux x, aux y)
    | App (App (Const Leq, x), y) -> Op (Leq, aux x, aux y)
    | App (App (Const Geq, x), y) -> Op (Geq, aux x, aux y)
    | App (App (Const EqInt, x), y) -> make_eq (aux x) (aux y)
    | App (Const Not, x) -> aux x |> negate
    | App (Const (TreeConstr _), x) -> aux x
    | App (Const (Label _), x) -> aux x
    (* I do not know why *)
    (*| App(Const (Rand(_, None)), Fun(f, _, t)) -> Forall(mk_var ~toplevel f, aux t)*)
    | App (Const (Event "fail"), _) -> Bool false
    | App (x, y) -> App (aux x, aux y)
    | Const (Rand (TInt, None)) -> (
        (* I have little time! *)
        match mode with
        | NonTermination -> Var (V "Exists")
        | Reachability -> Var (V "Forall")
        | _ -> unsupported "HFLz.of_cegar: mode")
    | Fun (f, _, x) -> Abs (mk_var ~toplevel f, aux x)
    | t ->
        Format.eprintf "%a@.%a@." CEGAR_syntax.pp t CEGAR_print.term t;
        assert false
  in
  aux -| commuting_conversion

let rule_of_fun_def ~toplevel : CEGAR_syntax.fun_def -> rule =
 fun def ->
  let fn = mk_var ~toplevel def.fn in
  let args = List.map (mk_var ~toplevel) def.args in
  let body = hflz_of_cegar ~toplevel def.body in
  let body =
    match negate (hflz_of_cegar ~toplevel def.cond) with Bool false -> body | p -> make_or p body
  in
  { fn; args; body }

let hes_of_prog : CEGAR_syntax.prog -> hes =
 fun { defs; main = orig_main; _ } ->
  (* Format.eprintf "%a" CEGAR_print.prog prog; *)
  let toplevel = List.map (fun x -> x.CEGAR_syntax.fn) defs in
  let rules =
    let merge rule1 rule2 =
      let body = make_and rule1.body rule2.body in
      { rule1 with body }
    in
    defs
    |> List.map (rule_of_fun_def ~toplevel)
    |> List.sort (fun x y -> compare x.fn y.fn)
    |> List.group_consecutive (fun x y -> x.fn = y.fn)
    |> List.map (List.reduce_left merge)
  in
  let main, others =
    let main_var = mk_var ~toplevel orig_main in
    let others = List.remove_if (fun x -> x.fn = main_var) rules in
    let main = List.find (fun x -> x.fn = main_var) rules in
    let remove_forall : hflz -> hflz * var list =
      let rec go acc = function
        | App (Var (V "Forall"), Abs (v, t)) -> go (v :: acc) t
        | t -> (t, acc)
      in
      go []
    in
    let main =
      let body, _args = remove_forall main.body in
      (* { main' with args; body } *)
      (* 鈴木さんのはこっちに非対応 *)
      { main with body }
    in
    (main, others)
  in
  main :: others

module Print = struct
  (*{{{*)
  open Fmt
  open Format

  let list_comma : 'a Fmt.t -> 'a list Fmt.t =
   fun format_x ppf xs ->
    let sep ppf () = Fmt.pf ppf ",@," in
    Fmt.pf ppf "[@[%a@]]" Fmt.(list ~sep format_x) xs

  let list_semi : 'a Fmt.t -> 'a list Fmt.t =
   fun format_x ppf xs ->
    let sep ppf () = Fmt.pf ppf ";@," in
    Fmt.pf ppf "[@[%a@]]" Fmt.(list ~sep format_x) xs

  let list_set : 'a Fmt.t -> 'a list Fmt.t =
   fun format_x ppf xs ->
    let sep ppf () = Fmt.pf ppf ",@," in
    Fmt.pf ppf "{@[%a@]}" Fmt.(list ~sep format_x) xs

  let list_ketsucomma : 'a Fmt.t -> 'a list Fmt.t =
   fun format_x ppf xs ->
    let sep ppf () = pf ppf "@,, " in
    pf ppf "[ @[<hv -2>%a@] ]" (list ~sep format_x) xs

  module Prec = struct
    (*{{{*)
    type t = int

    let succ x = x + 1
    let succ_if b x = if b then x + 1 else x
    let zero = 0
    let arrow = 1
    let abs = 1
    let or_ = 2
    let and_ = 3
    let eq = 4
    let add = 6
    let mul = 7
    let div = 8
    let neg = 9
    let app = 10

    let of_op = function
      | Add -> add
      | Sub -> add
      | Mul -> mul
      | Div -> div
      | Eq -> eq
      | Neq -> eq
      | Leq -> eq
      | Geq -> eq
      | Lt -> eq
      | Gt -> eq
      | And -> and_
      | Or -> or_

    let op_is_leftassoc = function
      | Add -> true
      | Sub -> true
      | Mul -> true
      | Div -> true
      | And -> true
      | Or -> true
      | Eq -> false
      | Neq -> false
      | Leq -> false
      | Geq -> false
      | Lt -> false
      | Gt -> false

    let op_is_rightassoc = function _ -> false
  end
  (*}}}*)

  type prec = Prec.t
  type 'a t_with_prec = Prec.t -> 'a t

  let ignore_prec : 'a t -> 'a t_with_prec = fun orig _prec ppf x -> orig ppf x

  let show_paren : bool -> formatter -> ('a, formatter, unit) format -> 'a =
   fun b ppf fmt -> if b then Fmt.pf ppf ("(" ^^ fmt ^^ ")") else Fmt.pf ppf fmt

  let var ppf (V x) = Fmt.string ppf x

  let rec hflz_ prec ppf (phi : hflz) =
    match phi with
    | Bool true -> Fmt.string ppf "true"
    | Bool false -> Fmt.string ppf "false"
    | Int n when n >= 0 -> Fmt.int ppf n
    | Int n -> Fmt.pf ppf "(%d)" n
    | Var v -> var ppf v
    | App (psi1, psi2) ->
        show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]" (hflz_ Prec.app) psi1
          (hflz_ Prec.(succ app))
          psi2
    | Abs (x, psi) -> show_paren (prec > Prec.abs) ppf "@[<1>\\%a.@,%a@]" var x (hflz_ Prec.abs) psi
    | Op (op, psi1, psi2) -> (
        let op_prec = Prec.of_op op in
        let nx_prec = op_prec + 1 in
        let pr = show_paren (prec > op_prec) in
        let recur = hflz_ nx_prec in
        match op with
        | Add -> pr ppf "@[<hv 0>%a@ + %a@]" recur psi1 recur psi2
        | Sub -> pr ppf "@[<hv 0>%a@ - %a@]" recur psi1 recur psi2
        | Mul -> pr ppf "@[<hv 0>%a@ * %a@]" recur psi1 recur psi2
        | Div -> pr ppf "@[<hv 0>%a@ / %a@]" recur psi1 recur psi2
        | Eq -> pr ppf "@[<hv 0>%a@ = %a@]" recur psi1 recur psi2
        | Neq -> pr ppf "@[<hv 0>%a@ != %a@]" recur psi1 recur psi2
        | Leq -> pr ppf "@[<hv 0>%a@ <= %a@]" recur psi1 recur psi2
        | Geq -> pr ppf "@[<hv 0>%a@ >= %a@]" recur psi1 recur psi2
        | Lt -> pr ppf "@[<hv 0>%a@ < %a@]" recur psi1 recur psi2
        | Gt -> pr ppf "@[<hv 0>%a@ > %a@]" recur psi1 recur psi2
        | And -> pr ppf "@[<hv 0>%a@ /\\ %a@]" recur psi1 recur psi2
        | Or -> pr ppf "@[<hv 0>%a@ \\/ %a@]" recur psi1 recur psi2)
    | Forall (v, t) -> show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]" var v (hflz_ Prec.abs) t

  let hflz : hflz Fmt.t = hflz_ Prec.zero

  let rule : rule Fmt.t =
   fun ppf rule ->
    Fmt.pf ppf "@[<2>%a %a@ =v@ %a.@]" var rule.fn
      (list ~sep:(fun ppf () -> string ppf " ") var)
      rule.args hflz rule.body

  let hes : hes Fmt.t =
   fun ppf hes ->
    Fmt.pf ppf "/*@.Generated by@.%t*/@.@." Cmd.(print_env ~cmd:true ~json:false);
    Fmt.pf ppf "%%HES@.";
    Fmt.pf ppf "@[<v>%a@]@." (Fmt.list rule) hes;
    Fmt.pf ppf "Forall p      =v ∀n. p n.@."
  (*Fmt.pf ppf "Exists p        =v ExistsAux 1000 0 p.@.";
    Fmt.pf ppf "ExistsAux x p =v x > 0 /\\ (p x \\/ p (0-x) \\/ ExistsAux (x-1)
        p).@."*)
end
(*}}}*)
