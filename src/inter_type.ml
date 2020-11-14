open Util

type base =
    True
  | False
  | State of int

type t =
    Base of base
  | Inter of t list
  | Fun of t * t

let rec decomp_fun n typ =
  match typ with
  | Base _ -> assert (n=0); [], typ
  | Inter _ -> assert (n=0); [], typ
  | Fun(typ1,typ2) ->
      if n <= 0
      then [], typ
      else
        let typs,typ' = decomp_fun (n-1) typ2 in
        typ1::typs, typ'

let print_base fm = function
    True -> Format.fprintf fm "True"
  | False -> Format.fprintf fm "False"
  | State n -> Format.fprintf fm "q%d" n

let rec print fm = function
    Base b -> print_base fm b
  | Inter [] -> Format.fprintf fm "Top"
  | Inter typs ->
      Format.fprintf fm "(@[<v>";
      print_list print " /\\@ " fm typs;
      Format.fprintf fm "@])"
  | Fun(typ1,typ2) ->
      Format.fprintf fm "(@[<hov 2>%a ->@ %a@])" print typ1 print typ2
