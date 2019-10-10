open Util

module CS = CEGAR_syntax

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type base =
  | Unit
  | Bool
  | Int
  | Abst of string

type t =
  | Base of base * CS.var * CS.t
  | Fun of CS.var * t * t
  | Inter of CS.typ * t list

let print_base fm = function
  | Unit -> Format.pp_print_string fm "unit"
  | Bool -> Format.pp_print_string fm "bool"
  | Int -> Format.pp_print_string fm "int"
  | Abst s -> Format.pp_print_string fm s

let rec occur x = function
  | Base(_,_,p) -> List.mem x (CS.get_fv p)
  | Fun(_, typ1,typ2) -> occur x typ1 || occur x typ2
  | Inter(_, typs) -> List.exists (occur x) typs

let rec print fm = function
  | Base(base,x,CS.Const CS.True) ->
      Format.fprintf fm "%a" print_base base
  | Base(base,x,p) ->
      Format.fprintf fm "{%a:%a | %a}" CEGAR_print.var x print_base base CEGAR_print.term p
  | Fun(x, typ1, typ2) ->
      if occur x typ2
      then Format.fprintf fm "(@[%a:%a@ ->@ %a@])" CEGAR_print.var x print typ1 print typ2
      else Format.fprintf fm "(@[%a@ ->@ %a@])" print typ1 print typ2
  | Inter(sty, []) when !!Debug.check -> Format.fprintf fm "Top(%a)" CEGAR_print.typ sty
  | Inter(_, []) -> Format.fprintf fm "Top"
  | Inter(_, [typ]) -> print fm typ
  | Inter(_, typs) -> Format.fprintf fm "(@[%a@])" (print_list print " /\\@ ") typs


let rec decomp_fun n typ =
  match typ with
  | Base _
  | Inter _ -> assert (n=0); [], typ
  | Fun(x,typ1,typ2) ->
      if n <= 0 then
        [], typ
      else
        let typs,typ' = decomp_fun (n-1) typ2 in
        (x,typ1)::typs, typ'

let to_simple_base base =
  match base with
  | Unit -> CEGAR_type.TUnit
  | Bool -> CEGAR_type.TBool
  | Int -> CEGAR_type.TInt
  | Abst s -> CEGAR_type.TAbst s

let rec to_simple typ =
  match typ with
  | Base(base, _, _) -> CEGAR_type.TBase(to_simple_base base, Fun.const [])
  | Fun(_, typ1, typ2) -> CEGAR_type.TFun(to_simple typ1, fun _ -> to_simple typ2)
  | Inter(styp, typs) -> styp

let rec arg_num = function
  | Base _ -> 0
  | Inter(typ, _) -> CS.arg_num typ
  | Fun(_,_,typ2) -> 1 + arg_num typ2
