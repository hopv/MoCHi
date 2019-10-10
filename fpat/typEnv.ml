open Combinator
open Util

(** Type environments *)

include Map_

type elem = (Idnt.t, Type.t) _elem
type t = (Idnt.t, Type.t) _t

(** {6 Printers} *)

let pr_elem ppf (x, ty) = Format.fprintf ppf "@[%a : %a@]" Idnt.pr x Type.pr ty

let pr_elem_tex ppf (x, ty) =
  Format.fprintf ppf "@[%a : %a@]" Idnt.pr_tex x Type.pr_tex ty

let pr_elem_compact ppf (x, ty) =
  Format.fprintf ppf "@[%a:%a@]" Idnt.pr x Type.pr ty

let pr_elem_compact_tex ppf (x, ty) =
  Format.fprintf ppf "@[%a:%a@]" Idnt.pr_tex x Type.pr_tex ty

let pr ppf tenv =
  Format.fprintf ppf "%a" (List.pr pr_elem ",@ ") (*List.rev*)tenv

let pr_tex ppf tenv =
  Format.fprintf ppf "%a" (List.pr pr_elem_tex ",@ ") (*List.rev*)tenv

let pr_compact ppf tenv =
  Format.fprintf ppf "%a" (List.pr pr_elem_compact ",") tenv

let pr_compact_tex ppf tenv =
  Format.fprintf ppf "%a" (List.pr pr_elem_compact_tex ",") tenv

(** {6 Morphisms} *)

let map_type = map_codom

(** {6 Auxiliary constructors} *)

let of_vars tenv =
  tenv |> List.unique |> List.map (fun x -> x, Type.mk_var (Idnt.new_tvar ()))
let of_types = List.map (fun ty -> Idnt.new_var (), ty)
let of_type = Type.args_of >> of_types

let rec of_sexp = function
  | Sexp.L([]) -> []
  | Sexp.L([Sexp.S(x); Sexp.S("Int")]) -> [Idnt.make x, Type.mk_int]
  | Sexp.L([Sexp.S(x); Sexp.S("Real")]) -> [Idnt.make x, Type.mk_real]
  | Sexp.L([Sexp.S(x); Sexp.S("Bool")]) -> [Idnt.make x, Type.mk_bool]
  | Sexp.L(es) -> List.concat_map of_sexp es
  | e ->
    Format.printf "sexp: %a@," Sexp.pr e;
    assert false (* @todo support datatypes *)

(** {6 Inspectors} *)

let string_of_elem = Printer.string_of pr_elem

let sexp_of tenv =
  tenv |> List.unique
  |> List.map (fun (x, ty) ->
      let args, ret = Type.args_ret ty in
      if args = [] then
        "(declare-const " ^ Idnt.string_of x ^ " " ^ Type.let_base ret TypConst.sexp_of ^ ")"
      else
        "(declare-fun " ^ Idnt.string_of x ^ " (" ^
        (String.concat " " (List.map (fun arg -> Type.let_base arg TypConst.sexp_of) args))
        ^ ") " ^ Type.let_base ret TypConst.sexp_of ^ ")")

(** {6 Operators} *)

let alpha tenv =
  tenv
  |> List.map (fun (x, ty) -> x, Idnt.new_var (), ty)
  |> Pair.unfold (List.map Triple.get23) (List.map Triple.get12)

(** @param x is a structured variable
    @return the type of x *)
let rec lookup tenv x =
  match x with
  | Idnt.V(_) | Idnt.C(_) ->
    List.assocF x tenv
      ~on_failure:(fun () -> Format.printf "type of %a not found@," Idnt.pr x)
  | Idnt.T(x', _, arg) ->
    begin
      let silent = !Global.silent in
      try
        Global.silent := true;
        Type.nth (lookup tenv x') arg
        |> sef (fun _ -> Global.silent := silent)
      with
      | e ->
        Global.silent := silent;
        Logger.printf ~kind:Logger.Debug
          "raise %a@." String.pr (Printexc.to_string e);
        List.assoc_fail x tenv
          ~on_failure:(fun () ->
              Format.printf "type of %a not found@," Idnt.pr x)
    end
  | _ -> Format.printf "error in typEnv.ml: x = %a@," Idnt.pr x; assert false

let filter_ty ty =
  List.filter_map (fun (x, ty') -> if ty' = ty then Some(x) else None)

(** check whether the result is consistent and eliminate duplicated elements *)
let merge =
  List.classify (comp2 Idnt.equiv fst fst)
  >> List.map
    (function
      | ((x, _) :: _ as tenv) -> x, Type.meet_list @@ List.map snd tenv
      | _ -> assert false)

let subst tenv = tenv |> Type.subst |> Pair.map_snd |> List.map
let ftvs tenv = tenv |> List.concat_map (snd >> Type.fvs)

let int_to_real tenv = tenv |> (Type.int_to_real |> Pair.map_snd |> List.map)
let real_to_int tenv = tenv |> (Type.real_to_int |> Pair.map_snd |> List.map)
