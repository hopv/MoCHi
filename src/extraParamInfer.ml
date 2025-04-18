open Syntax
open Type
open Type_util
open Term_util

let origWithExparam = ref (make_int 0)
let exCoefficients = ref []

let to_string_CoeffInfos coeffsMap =
  let f = subst_map (List.map (Util.Pair.map_snd make_int) coeffsMap) in
  let g v = Lid.to_string @@ var_of_term v in
  let h = function
    | { desc = Const (Int n) } -> string_of_int n
    | _ -> raise (Invalid_argument "")
  in
  let isZero = function
    | { desc = Const (Int n) } -> n = 0
    | { desc = Var (LId v) } -> Id.is_coefficient v
    | t ->
        Format.eprintf "%a@." Print.term t;
        invalid_arg "ExtraParamInfer.to_string_CoeffInfos"
  in
  let areAllZero = List.for_all isZero (List.map f !exCoefficients) in
  try
    if areAllZero then ""
    else
      List.fold_left2
        (fun s c v -> s ^ "\t" ^ g c ^ " = " ^ h v ^ "\n")
        "" (List.rev !exCoefficients) (List.rev_map f !exCoefficients)
  with _ -> ""

let withExparam = ref (make_int 0)

let rec transType = function
  | TFun (({ Id.name = t1Name; Id.typ = t1 } as t1Id), t2) when is_fun_typ t1 ->
      let t1 = transType t1 in
      TFun
        ( Id.new_var ~name:(t1Name ^ "_EXPARAM") Ty.int,
          TFun ({ t1Id with Id.typ = t1 }, transType t2) )
  | TFun (t1, t2) -> TFun (t1, transType t2)
  | t -> t

let counter = ref 0
let nthCoefficient = ref []

let freshCoefficient () =
  let _ = counter := !counter + 1 in
  let freshName = "c" ^ string_of_int (!counter - 1) ^ "_COEFFICIENT" in
  let freshId = Id.new_coeff ~name:freshName Ty.int in
  let _ = nthCoefficient := !nthCoefficient @ [ freshId ] in
  let freshCoeff = make_var freshId in
  exCoefficients := freshCoeff :: !exCoefficients;
  freshCoeff

let rec makeTemplate = function
  | [] -> freshCoefficient ()
  | x :: xs -> Term.((freshCoefficient () * var x) + makeTemplate xs)

let rec insertExparam scope expr =
  match expr.desc with
  | Const _ -> expr
  | Var (LId v) ->
      let typ = transType v.Id.typ in
      let v = Id.set_typ v typ in
      Term.var v
  | Var _ -> assert false
  | Fun _ -> assert false (* ??? *)
  | App (f, args) ->
      let insertToArgs = function
        | t when is_base_typ t.typ -> [ insertExparam scope t ]
        | t -> [ makeTemplate scope; insertExparam scope t ]
      in
      make (App (insertExparam scope f, BRA_util.concat_map insertToArgs args)) expr.typ
  | If (predicate, thenClause, elseClause) ->
      let desc =
        If
          ( insertExparam scope predicate,
            insertExparam scope thenClause,
            insertExparam scope elseClause )
      in
      make desc expr.typ
  | Local (Decl_let bindings, e) ->
      let rec extend sc = function
        | [] -> sc
        | (x, _body) :: bs when Id.typ x = Ty.int && List.for_all Util.(fst |- Id.( <> ) x) bindings
          ->
            extend (x :: sc) bs
        | _ :: bs -> extend sc bs
      in
      let scope = extend scope bindings in
      let insertExparamBinding (x, body) =
        let args, body = decomp_funs body in
        let insertExparamArgs (sc, ags) = function
          | t when Id.typ t = Ty.int -> (t :: sc, ags @ [ t ])
          | t when is_base_typ (Id.typ t) -> (sc, ags @ [ t ])
          | t when is_fun_typ (Id.typ t) ->
              let t_exparamId = Id.new_var ~name:(Id.name t ^ "_EXPARAM") Ty.int in
              (t_exparamId :: sc, ags @ [ t_exparamId; { t with Id.typ = transType t.Id.typ } ])
          | _ -> assert false
        in
        let scope, args = List.fold_left insertExparamArgs (scope, []) args in
        ({ x with Id.typ = transType x.Id.typ }, make_funs args @@ insertExparam scope body)
      in
      let desc =
        Local
          ( Decl_let (List.map insertExparamBinding bindings),
            insertExparam (extend scope bindings) e )
      in
      make desc expr.typ
  | BinOp (op, expr1, expr2) ->
      let desc = BinOp (op, insertExparam scope expr1, insertExparam scope expr2) in
      make desc expr.typ
  | Not e ->
      let desc = Not (insertExparam scope e) in
      make desc expr.typ
  | _ -> Util.unsupported "ExtraParamInfer"

let rec removeDummySubstitutions = function
  | { desc = Local (Decl_let [ (_, { desc = Const (Int 0) }) ], e) } -> removeDummySubstitutions e
  | e -> e

let substituteZero e =
  let toZero = function
    | { desc = Var (LId id) } when Id.is_coefficient id -> make_int 0
    | e -> e
  in
  BRA_transform.everywhere_expr toZero e

let initPreprocessForExparam e =
  let e = removeDummySubstitutions e in
  let _ = withExparam := e in
  substituteZero e

let addTemplate prog =
  let _ = counter := 0 in
  let prog = insertExparam [] prog in
  let _ = counter := !counter - 1 in
  let rec dummySubst = function
    | -1 -> prog
    | n -> make_let [ (List.nth !nthCoefficient n, make_int 0) ] (dummySubst (n - 1))
    (*    | n -> make_letrec [(List.nth !nthCoefficient n), [], make_var (List.nth !nthCoefficient n)] (tmp (n-1))*)
  in
  origWithExparam := prog;
  dummySubst !counter
