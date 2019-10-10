open Map
open BRA_types
open BRA_util

let rec default_val t = {Syntax.desc = default_val' t; Syntax.typ = t; attr=[]}
and default_val' =
  let open Syntax in
  let open Type in function
    | TBase TUnit -> Const Unit
    | TBase TBool -> Const False
    | TBase TInt -> Const (Int 0)
    | TBase (TPrim s) -> invalid_arg "default_val: not yet implemented syntax(TPrim)"
    | TFun ({Id.typ = t1}, t2) -> Fun (Id.new_var ~name:"_" t1, default_val t2)
    | TAttr(_, typ) -> default_val' typ
    | TData _ -> invalid_arg "default_val: not yet implemented syntax(TData)"
    | TApp _ -> invalid_arg "default_val: not yet implemented syntax(TApp)"
    | TTuple _ -> invalid_arg "default_val: not yet implemented syntax(TTuple)"
    | TVarLazy _ -> assert false
    | TVar(t,_) ->
      begin
        match !t with
        | None -> raise (Invalid_argument "default_val: not yet implemented syntax(TVar None)")
        | Some t' -> default_val' t'
      end
    | TFuns _ -> invalid_arg "default_val: not yet implemented syntax(TFuns)"
    | TRecord _ -> invalid_arg "default_val: not yet implemented syntax(TRecord)"
    | TVariant _ -> invalid_arg "default_val: not yet implemented syntax(TVariant)"
    | TModule _ -> invalid_arg "default_val: not yet implemented syntax(TModule)"

let state_transducer trans_prev_statevar trans_statevar trans_argvars state =
  {state with
    prev_statevars = trans_prev_statevar state.prev_statevars
    ; statevars = trans_statevar state.statevars
    ; argvars = trans_argvars state.argvars}

let is_basetype_variable = function
  | {Syntax.typ = Type.TFun (_, _)} -> false
  | _ -> true

(* remove variables of functional type *)
let remove_functional_vars = state_transducer (List.filter is_basetype_variable) (List.filter is_basetype_variable) (List.filter is_basetype_variable)

let filter_non_integer =
  let is_integer = function
    | {Syntax.typ = Type.TBase Type.TInt} -> true
    | _ -> false
  in
  state_transducer (List.filter is_integer) (List.filter is_integer) (List.filter is_integer)

let build_var name typ = Term_util.make_var (Id.new_var ~name typ)
let make_prev_statevar_name function_name baseId = "s_prev_" ^ function_name ^ "_" ^ baseId.Id.name
let make_prev_statevar_id function_name baseId = Id.new_var ~name:(make_prev_statevar_name function_name baseId) baseId.Id.typ
let make_prev_statevar function_name baseId = build_var (make_prev_statevar_name function_name baseId) baseId.Id.typ
let make_statevar_name function_name baseId = "s_" ^ function_name ^ "_" ^ baseId.Id.name
let make_statevar_id function_name baseId = Id.new_var ~name:(make_statevar_name function_name baseId) baseId.Id.typ
let make_statevar function_name baseId = build_var (make_statevar_name function_name baseId) baseId.Id.typ

let build_record {id = {Id.name = f_name}; args = f_args} =
  let open Type in
  let record =
    ref { update_flag    = build_var "update_flag" Ty.bool
	; set_flag       = build_var ("set_flag_" ^ f_name) Ty.bool
	; prev_set_flag  = build_var ("prev_set_flag_" ^ f_name) Ty.bool
	; prev_statevars = List.map (make_prev_statevar f_name) f_args
	; statevars      = List.map (make_statevar f_name) f_args
	; argvars        = List.map Term_util.make_var f_args
	} in
  let _ = record := filter_non_integer !record in
  !record

let build_state function_infos target =
  { initial_state = Term_util.false_term :: List.map (fun {Syntax.typ = t} -> default_val t) (build_record target).argvars
  ; statetable = List.fold_left (fun map function_info -> InnerState.add function_info.id (build_record function_info) map) InnerState.empty function_infos
  }

let get_update_flag state f = (InnerState.find f.id state.statetable).update_flag
let get_set_flag state f = (InnerState.find f.id state.statetable).set_flag
let get_prev_set_flag state f = (InnerState.find f.id state.statetable).prev_set_flag
let get_prev_statevars state f = (InnerState.find f.id state.statetable).prev_statevars
let get_statevars state f = (InnerState.find f.id state.statetable).statevars
let get_argvars state f = (InnerState.find f.id state.statetable).argvars

let passed_statevars {BRA_types.verified = verified; BRA_types.state = state} f =
  let table = InnerState.find verified.id state.statetable in
  if f = verified.id then
    table.prev_set_flag :: table.prev_statevars
  else
    table.set_flag :: table.statevars

let propagated_statevars {BRA_types.verified = verified; BRA_types.state = state} =
  let table = InnerState.find verified.id state.statetable in
  table.set_flag :: table.statevars

let find_state {BRA_types.state = state} f = InnerState.find f.id state.statetable

let type_of_state {BRA_types.state = {BRA_types.initial_state = inits}} = List.map (fun {Syntax.typ = t} -> t) inits
