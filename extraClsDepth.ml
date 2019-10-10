open Syntax
open Term_util
open Type

(* h -> h_DEPTH *)
let makeDepthVar id = make_var (Id.add_name_after "_DEPTH" id)

let maxConstDepth constDepthList =
  make_int (List.fold_left
	      (fun m n -> if m > int_of_term n then m else int_of_term n)
	      0
	      constDepthList)

let dynamicGreaterThan a b =
  if a.desc = Const (Int 0) then b
  else if b.desc = Const (Int 0) then a
  else make_if (make_gt a b) a b

let rec dynamicMaximum = function
  | [x] -> x
  | x::xs ->
    let freshVarId = Id.new_var ~name:"tmp_DEPTH" Ty.int in
    let freshVar = make_var freshVarId in
    make_let
      [(freshVarId, dynamicMaximum xs)]
      (dynamicGreaterThan freshVar x)
  | [] -> assert false

(* f g (h g) i (g, h: toplevel)
-> DEPTH: (if i_DEPTH > 1 then i_DEPTH else 1) *)
let maxDepthOf depthList =
  match
    let isConstDepth = function
      | {desc = Const (Int _)} -> true
      | _ -> false
    in
    List.partition isConstDepth depthList
  with
    | [], [] -> make_int 0
    | constDepthList, [] -> maxConstDepth constDepthList
    | [], indefiniteDepthList -> dynamicMaximum indefiniteDepthList
    | constDepthList, indefiniteDepthList -> dynamicMaximum ((maxConstDepth constDepthList) :: indefiniteDepthList)

let incrementDepth = function
  | {desc = Const (Int n)} -> {desc = Const (Int (n+1)); typ = Ty.int; attr=[]}
  | e -> make_add e (make_int 1)

let rec closureDepth varToDepth expr =
  match expr.desc with
    | Var v when is_fun_typ (Id.typ v) ->
      begin
	try
	  List.assoc (Id.to_string v) varToDepth
	with Not_found ->
	  print_endline (Id.to_string v);
	  (raise Not_found)
      end
    | Const _
    | Var _ -> make_int 0
    | Fun (x, e) -> assert false (* ? *)
    | App (f, args) ->
      dynamicGreaterThan (closureDepth varToDepth f) (incrementDepth (maxDepthOf (List.map (closureDepth varToDepth) args)))
    | If (predicate, thenClause, elseClause) ->
      make_if predicate (closureDepth varToDepth thenClause) (closureDepth varToDepth elseClause)
    | Local (_, _) -> assert false (* TODO *)
    | BinOp (_, _, _) -> make_int 0
    | Not _ -> make_int 0
    | _ -> assert false (* unimplemented *)

let rec transType = function
  | TFun ({Id.name=t1Name; Id.typ=t1} as t1Id, t2) when is_fun_typ t1 ->
    let t1 = transType t1 in
    TFun (Id.new_var ~name:(t1Name^"_DEPTH") Ty.int, TFun ({t1Id with Id.typ = t1}, transType t2))
  | TFun (t1, t2) -> TFun (t1, transType t2)
  | t -> t

let rec insertClsDepth varToDepth expr =
  match expr.desc with
    | Const _ -> expr
    | Var v ->
      let typ = transType v.Id.typ in
      {desc = Var {v with Id.typ = typ}; typ = typ; attr=[]}
    | Fun (x, e) -> assert false (* ? *)
    | App (f, args) ->
      let insertToArgs = function
	| t when is_base_typ t.typ -> [insertClsDepth varToDepth t]
	| t -> [closureDepth varToDepth t; insertClsDepth varToDepth t]
      in
      { expr with
	desc = App (insertClsDepth varToDepth f, BRA_util.concat_map insertToArgs args)}
    | If (predicate, thenClause, elseClause) ->
      { expr with
	desc = If ((insertClsDepth varToDepth predicate),
		   (insertClsDepth varToDepth thenClause),
		   (insertClsDepth varToDepth elseClause))}
    | Local(Decl_let bindings, e) ->
      let makeBaseEnv varToDepth = function
	| (x, body) when is_base_typ (Id.typ x) -> varToDepth
	| (x, body) when not @@ is_fun body && is_fun_typ (Id.typ x) ->
	  let x_depthId = Id.new_var ~name:((Id.name x) ^ "_DEPTH") Ty.int in
	  let x_depth = make_var x_depthId in
	  (Id.to_string x, x_depth)::varToDepth
	| (x, body) -> (Id.to_string x, make_int 0)::varToDepth
      in
      let insertClsDepthBinding varToDepth (varToDepth', bindings') = function
	| (x, body) when is_base_typ (Id.typ x) ->
	  (varToDepth', (x, insertClsDepth varToDepth body)::bindings')
	| (x, body) when not @@ is_fun body && is_fun_typ (Id.typ x) ->
	  let x_depthId =
	    begin
	      try
		BRA_transform.extract_id (List.assoc (Id.to_string x) varToDepth)
	      with Not_found ->
	        Id.new_var ~name:((Id.name x) ^ "_DEPTH") Ty.int
	    end
	  in
	  let x_depth = make_var x_depthId in
	  ( (Id.to_string x, x_depth)::varToDepth'
	  , (x_depthId, closureDepth varToDepth body)::({x with Id.typ = transType x.Id.typ}, insertClsDepth varToDepth body)::bindings')
	| (x, body) ->
          let args,body = decomp_funs body in
	  let insertToArgs (vtd, ags) = function
	    | t when is_base_typ (Id.typ t) -> (vtd, ags@[t])
	    | t when is_fun_typ (Id.typ t) ->
	      let t_depthId = Id.new_var ~name:((Id.name t) ^ "_DEPTH") Ty.int in
	      ((Id.to_string t, make_var t_depthId)::vtd, ags@[t_depthId; {t with Id.typ = transType t.Id.typ}])
	    | _ -> assert false
	  in
	  let (varToDepth, args) =
	    List.fold_left
	      insertToArgs
	      (varToDepth, [])
	      args
	  in
	  ((Id.to_string x, make_int 0)::varToDepth', ({x with Id.typ = transType x.Id.typ}, make_funs args @@ insertClsDepth varToDepth body)::bindings')
      in
      let varToDepth' = List.fold_left makeBaseEnv varToDepth bindings in
      let (varToDepth, bindings) =
	List.fold_left (insertClsDepthBinding varToDepth') (varToDepth, []) bindings
      in
      { expr with
	desc = Local(Decl_let bindings, insertClsDepth varToDepth e)}
    | BinOp (op, expr1, expr2) ->
      { expr with
	desc = BinOp (op, insertClsDepth varToDepth expr1, insertClsDepth varToDepth expr2)}
    | Not e ->
      { expr with
	desc = Not (insertClsDepth varToDepth e)}
    | _ -> assert false (* unimplemented *)

let addExtraClsDepth = insertClsDepth []
