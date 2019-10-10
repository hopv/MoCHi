(* Temporary Implementation of Interface to Omega Calculator (oc) *)
(* To use functions in this module, you need to install omega calculator and set Environment.omega to the installation path. *)

(*
  type: CEGAR_syntax.var list ->
    CEGAR_syntax.var list -> CEGAR_syntax.t list -> CEGAR_syntax.t -> bool

  xs: universally quantified variables
  ys: existentially quantified variables
  cond: precondition
  p: formula that will be checked

*)

open Util
open CEGAR_print
open CEGAR_syntax

exception Unknown

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let rec print_conj print fm xs =
  match xs with
  | [] -> ()
  | [x] -> print fm x
  | x::xs ->
      Format.fprintf fm "(%a)" print x;
      Format.fprintf fm "& %a" (print_conj print) xs

let extract_result cin =
  let rec discard s =
    try let l = input_line cin in
        if String.length l = 0 || l.[0] = '#' then discard s
        else discard (s^l)
    with _ -> s
  in
  let s = discard "" in
  let s = String.strip s in
  if s = "{ TRUE }" then true else
  if s = "{ FALSE }" then false else
  raise Unknown

(*
  Omega does not support Boolean constant
*)
let rec replace_bool_const = function
  | Const(True) -> make_geq (make_int 0) (make_int 0)
  | Const(False) -> make_gt (make_int 0) (make_int 0)
  | App(t1, t2) -> App(replace_bool_const t1, replace_bool_const t2)
  | e -> e

let is_valid_forall_exists xs ys cond p =
  let cond = List.map replace_bool_const cond in
  let p = replace_bool_const p in
  let input_file = Filename.change_extension !!Flag.Input.main "oc" in
  let result_file = Filename.change_extension !!Flag.Input.main "oc_out" in
  let vars fm xs = print_list_aux CEGAR_print.var "," false fm xs in

  let cout = open_out input_file in
  let input_fm = Format.formatter_of_out_channel cout in
  (if xs = [] then
      begin
      Debug.printf "{[]:exists(%a: not (%a) || (%a) )};@." vars ys (print_conj CEGAR_print.term) cond CEGAR_print.term p;
      Format.fprintf input_fm "{[]:exists(%a: not (%a) || (%a) )};@." vars ys (print_conj CEGAR_print.term) cond CEGAR_print.term p
    end
   else
    begin
      Debug.printf "{[]:forall(%a: exists(%a: not (%a) || (%a) ))};@." vars xs vars ys (print_conj CEGAR_print.term) cond CEGAR_print.term p;
      Format.fprintf input_fm "{[]:forall(%a: exists(%a: not (%a) || (%a) ))};@." vars xs vars ys (print_conj CEGAR_print.term) cond CEGAR_print.term p
    end);
  close_out cout;

  let cmd = Format.sprintf "%s %s > %s" !Flag.External.omega input_file result_file in
  let _ = Sys.command cmd in
  let cin = open_in result_file in
  let result = extract_result cin in
  close_in cin;
  result
