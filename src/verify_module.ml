open Util
open Mochi_util
open Term_util
open Type_util

module Debug = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

let main f parsed =
  let verify x =
    Verbose.printf "Start verification of %a:@." Id.print x;
    let main = Id.new_var_id x in
    let t =
      parsed
      |> Trans.replace_main ~main:Term.(let_ [ (main, var x) ] unit)
      |> Trans.elim_unused_let ~leave_last:true
    in
    let r = f t in
    if r then Format.fprintf !Flag.Print.target "%a is safe@.@." Id.print x
    else Format.fprintf !Flag.Print.target "%a is unsafe@.@." Id.print x;
    r
  in
  Term_util.get_top_funs parsed |> List.map verify |> List.for_all Fun.id

let main verify parsed =
  let fs = get_top_funs parsed in
  let target =
    let aux f =
      Format.fprintf !Flag.Print.target "TARGET: %a@." Id.print f;
      let xs, _ = decomp_tfun @@ Id.typ f in
      let aux x = make_rand_unit @@ Id.typ x in
      Term.(var f @@ List.map aux xs)
    in
    List.map aux fs
  in
  let main =
    let body = List.fold_right make_seq target unit_term in
    Format.fprintf !Flag.Print.target "body: %a@." Print.term body;
    make_let [ (new_var_of_term body, body) ] unit_term
  in
  parsed
  |@> Format.fprintf !Flag.Print.target "parsed: %a@." Print.term
  |> Trans.replace_main ~main
  |@> Format.fprintf !Flag.Print.target "set main: %a@." Print.term
  |> verify
