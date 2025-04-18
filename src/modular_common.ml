open Util
open Type
open Type_util
open Syntax
open Term_util

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

type program = {
  fun_typ_env : Ref_type.env;
  fun_typ_neg_env : Ref_type.neg_env;
  fun_def_env : (id * term) list;
  exn_decl : term Type.row list;
}

type label = int
type ce = (label * bool) list
type ce_set = (id * ce) list

let print_typ_env = Ref_type.Env.print
let print_typ_neg_env = Ref_type.NegEnv.print
let print_def_env fm def = List.print (Pair.print Id.print Print.term) fm def

let print_prog fm { fun_typ_env; fun_typ_neg_env; fun_def_env } =
  Format.fprintf fm "@[";
  Format.fprintf fm "fun_typ_env: %a@\n" print_typ_env fun_typ_env;
  Format.fprintf fm "fun_typ_neg_env: %a@\n" print_typ_neg_env fun_typ_neg_env;
  Format.fprintf fm "fun_def_env: %a@\n" print_def_env fun_def_env;
  Format.fprintf fm "@]"

let print_ce_aux fm (l, b) = Format.pp_print_int fm (if b then l else -l)
let print_ce fm ce = (List.print print_ce_aux) fm ce
let print_ce_set fm ce_set = (List.print @@ Pair.print Id.print print_ce) fm ce_set

let compose_id ?nid ?arg orig =
  let name = Id.to_string orig in
  let nid' = Option.map_default (( ^ ) ":" -| string_of_int) "" nid in
  let arg' = Option.map_default (( ^ ) "@" -| string_of_int) "" arg in
  Id.make (Format.sprintf "%s%s%s" name nid' arg') (Id.typ orig)

let decomp_id x =
  let s = Id.to_string x in
  match String.rsplit s ~by:":" with
  | exception Not_found -> (s, None, [])
  | _, "" -> (s, None, [])
  | x', rest -> (
      match String.split_on_string ~by:"@" rest with
      | [] -> assert false
      | nid :: args -> (
          try (x', Some (int_of_string nid), List.map int_of_string args)
          with _ -> invalid_arg "Modular_common.decomp_id"))

let same_top_fun x y =
  let x_orig, _, x_args = decomp_id x in
  let y_orig, _, y_args = decomp_id y in
  x_args = [] && y_args = [] && x_orig = y_orig

let rec is_atom t =
  match t.desc with
  | App ({ desc = Const (Rand _) }, [ _ ]) -> true
  | App ({ desc = Event (_, _) }, [ _ ]) -> true
  | BinOp (_, t1, t2) -> is_atom t1 && is_atom t2
  | _ -> false

let rec is_simple_term t =
  match t.desc with
  | Const _ -> true
  | Var _ -> true
  | Tuple ts -> List.for_all is_simple_term ts
  | _ -> is_randint_unit t || is_randbool_unit t

let inline_simple_fun = Tr2.make ()

let inline_simple_fun_desc env desc =
  match desc with
  | Local (Decl_let bindings, t) ->
      let bindings' = List.map (Pair.map_snd @@ inline_simple_fun.term env) bindings in
      let env' = List.filter (snd |- is_simple_term) bindings' @ env in
      Local (Decl_let bindings', inline_simple_fun.term env' t)
  | App ({ desc = Var (LId f) }, ts)
    when List.exists
           (fun (g, t) -> Id.(g = f) && List.length (fst @@ decomp_funs t) = List.length ts)
           env
         && List.for_all is_simple_term ts ->
      let _, t = List.find (fst |- Id.same f) env in
      let xs, t' = decomp_funs t in
      (List.fold_right2 subst xs ts t').desc
  | _ -> inline_simple_fun.desc_rec env desc

let () = inline_simple_fun.desc <- inline_simple_fun_desc
let inline_simple_fun t = inline_simple_fun.term [] t

let debug s t =
  if !!Dbg.check then (
    Dbg.printf "%s: %a@.@." s Print.term t;
    Check.assert_check_afv t)

let normalize add_id t =
  t
  |@> debug "NORMALIZE0"
  |> Trans.replace_bottom_def
  |@> debug "NORMALIZE1"
  |> Trans.short_circuit_eval
  |@> debug "NORMALIZE2"
  |> Trans.normalize_let ~is_atom
  |@> debug "NORMALIZE3"
  |> Trans.flatten_let
  |@> debug "NORMALIZE4"
  |> Trans.remove_no_effect_trywith
  |@> debug "NORMALIZE5"
  |> inline_simple_fun
  |@> debug "NORMALIZE6"
  |> fixed_point ~eq:same_term
       (Trans.inline_var
       |@- debug "NORMALIZE6.1"
       |- Trans.inline_simple_exp
       |@- debug "NORMALIZE6.2"
       |- Trans.bool_eta_reduce
       |@- debug "NORMALIZE6.3"
       |- Trans.reconstruct
       |@- debug "NORMALIZE6.4"
       |- Trans.elim_unused_let ~leave_last:true
       |@- debug "NORMALIZE6.5")
  |@> debug "NORMALIZE7"
  |> Trans.add_id_if (function { desc = If _ } -> add_id | _ -> false)
  |> snd
  |> Trans.reconstruct
  |> Trans.alpha_rename

(* `used_by f prog` returns top-level functions used (directly/indirectly) by f *)
let used_by f prog =
  let rec aux acc rest =
    match rest with
    | [] -> acc
    | f :: rest' when Id.List.mem f acc -> aux acc rest'
    | f :: rest' ->
        let xs, t = decomp_funs @@ Id.List.assoc f prog.fun_def_env in
        aux (f :: acc) (List.Set.diff ~eq:Id.eq (get_fv t) (f :: xs) @ rest')
  in
  let fs = List.unique ~eq:Id.eq @@ aux [] [ f ] in
  if Id.List.mem f @@ get_fv @@ snd @@ decomp_funs @@ Id.List.assoc f prog.fun_def_env then fs
  else List.filter_out (Id.same f) fs

let term_of_prog prog =
  prog.fun_def_env |> List.last |> fst |> make_var |> make_lets prog.fun_def_env

let take_funs_of_depth env f depth =
  let rec aux acc fs depth =
    if depth <= 0 then acc
    else
      let fs' =
        let aux g =
          let xs, t = decomp_funs @@ Id.List.assoc g env in
          List.Set.diff ~eq:Id.eq (get_fv t) (g :: xs)
        in
        fs |> List.flatten_map aux |> List.unique ~eq:Id.eq
      in
      aux (fs @ acc) fs' (depth - 1)
  in
  aux [] [ f ] depth

let make_etyp prog =
  let row_constr = constr_of_string "Assert_failure" in
  let row = { row_constr; row_args = []; row_ret = None } in
  let rows = prog.exn_decl @ [ row ] in
  (row_constr, TVariant (VNonPoly, rows))
