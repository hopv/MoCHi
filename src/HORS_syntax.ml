type symbol = string
type args = symbol list

type expr =
  | Var   of symbol
  | Apply of expr * expr
  | Abst  of string * expr

type rule = symbol * expr

type rules = rule list

let rec pp_rule fm (sym, v) =
  Format.fprintf fm "%s => %a@." sym pp_expr v

and pp_expr fm = function
  | Var "_" ->
     Format.fprintf fm "[DUMMY]"
  | Var name ->
     Format.fprintf fm "%s" name
  | Apply (e1, e2) ->
     Format.fprintf fm "(%a %a)" pp_expr e1 pp_expr e2
  | Abst (x, e) ->
     Format.fprintf fm "(fun %s -> %a)" x pp_expr e
