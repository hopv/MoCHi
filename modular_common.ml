open Util
open Syntax
open Term_util
open Type


module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)


type program =
  {fun_typ_env : Ref_type.env;
   fun_typ_neg_env : Ref_type.neg_env;
   fun_def_env : (id * term) list;
   exn_decl : (string * typ list) list}

type label = int
type ce = (label * bool) list
type ce_set = (id * ce) list

let print_typ_env = Ref_type.Env.print
let print_typ_neg_env = Ref_type.NegEnv.print
let print_def_env fm def = List.print (Pair.print Id.print Print.term) fm def

let print_prog fm {fun_typ_env; fun_typ_neg_env; fun_def_env} =
  Format.fprintf fm "@[";
  Format.fprintf fm "fun_typ_env: %a@\n" print_typ_env fun_typ_env;
  Format.fprintf fm "fun_typ_neg_env: %a@\n" print_typ_neg_env fun_typ_neg_env;
  Format.fprintf fm "fun_def_env: %a@\n" print_def_env fun_def_env;
  Format.fprintf fm "@]"

let print_ce_aux fm (l,b) = Format.pp_print_int fm (if b then l else -l)
let print_ce fm ce = (List.print print_ce_aux) fm ce
let print_ce_set fm ce_set = (List.print @@ Pair.print Id.print print_ce) fm ce_set

let compose_id ?nid ?arg orig =
  let name = Id.to_string orig in
  let nid' = Option.map_default ((^) ":" -| string_of_int) "" nid in
  let arg' = Option.map_default ((^) "@" -| string_of_int) "" arg in
  Id.make 0 (Format.sprintf "%s%s%s" name nid' arg') [] (Id.typ orig)

let decomp_id x =
  let s = Id.to_string x in
  match String.rsplit s ~by:":" with
  | exception Not_found -> s, None, []
  | _, "" -> s, None, []
  | x', rest ->
      match String.nsplit rest ~by:"@" with
      | [] -> assert false
      | nid::args ->
          try
            x', Some (int_of_string nid), List.map int_of_string args
          with _ -> invalid_arg "Modular_common.decomp_id"

let same_top_fun x y =
  let x_orig,_,x_args = decomp_id x in
  let y_orig,_,y_args = decomp_id y in
  x_args = [] && y_args = [] && x_orig = y_orig

let rec is_atom t =
  match t.desc with
  | App({desc=Const(Rand _)}, [_]) -> true
  | App({desc=Event(_, _)}, [_]) -> true
  | BinOp(_, t1, t2) -> is_atom t1 && is_atom t2
  | _ -> false


let rec is_simple_term t =
  match t.desc with
  | Const _ -> true
  | Var _ -> true
  | Tuple ts -> List.for_all is_simple_term ts
  | _ -> is_randint_unit t || is_randbool_unit t

let inline_simple_fun = make_trans2 ()
let inline_simple_fun_desc env desc =
  match desc with
  | Local(Decl_let bindings, t) ->
      let bindings' = List.map (Pair.map_snd @@ inline_simple_fun.tr2_term env) bindings in
      let env' = List.filter (snd |- is_simple_term) bindings' @ env in
      Local(Decl_let bindings', inline_simple_fun.tr2_term env' t)
  | App({desc=Var f}, ts) when List.exists (fun (g,t) -> Id.(g = f) && List.length (fst @@ decomp_funs t) = List.length ts) env && List.for_all is_simple_term ts ->
      let _,t = List.find (fst |- Id.same f) env in
      let xs,t' = decomp_funs t in
      (List.fold_right2 subst xs ts t').desc
  | _ -> inline_simple_fun.tr2_desc_rec env desc
let () = inline_simple_fun.tr2_desc <- inline_simple_fun_desc
let inline_simple_fun t = inline_simple_fun.tr2_term [] t

let normalize add_id t =
  t
  |@> Debug.printf "NORMALIZE0: %a@.@." Print.term
  |> Trans.replace_bottom_def
  |@> Debug.printf "NORMALIZE1: %a@.@." Print.term
  |> Trans.short_circuit_eval
  |@> Debug.printf "NORMALIZE2: %a@.@." Print.term
  |> Trans.normalize_let ~is_atom:is_atom
  |@> Debug.printf "NORMALIZE3: %a@.@." Print.term
  |> Trans.flatten_let
  |@> Debug.printf "NORMALIZE4: %a@.@." Print.term
  |> Trans.remove_no_effect_trywith
  |@> Debug.printf "NORMALIZE5: %a@.@." Print.term
  |> inline_simple_fun
  |@> Debug.printf "NORMALIZE6: %a@.@." Print.term
  |> fixed_point ~eq:same_term
       (Trans.inline_var
        |@- Debug.printf "NORMALIZE6.1: %a@.@." Print.term
        |- Trans.inline_simple_exp
        |@- Debug.printf "NORMALIZE6.2: %a@.@." Print.term
        |- Trans.bool_eta_reduce
        |@- Debug.printf "NORMALIZE6.3: %a@.@." Print.term
        |- Trans.reconstruct
        |@- Debug.printf "NORMALIZE6.4: %a@.@." Print.term
        |- Trans.elim_unused_let ~leave_last:true
        |@- Debug.printf "NORMALIZE6.5: %a@.@." Print.term)
  |@> Debug.printf "NORMALIZE7: %a@.@." Print.term
  |> Trans.add_id_if (function {desc=If _} -> add_id | _ -> false)
  |> snd
  |> Trans.reconstruct
  |> Trans.alpha_rename

(* `used_by f prog` returns top-level functions used (directly/indirectly) by f *)
let used_by f prog =
  let rec aux acc rest =
    match rest with
    | [] -> acc
    | f::rest' when Id.mem f acc -> aux acc rest'
    | f::rest' ->
        let xs,t = decomp_funs @@ Id.assoc f prog.fun_def_env in
        aux (f::acc) (List.Set.diff ~eq:Id.eq (get_fv t) (f::xs) @ rest')
  in
  let fs = List.unique ~eq:Id.eq @@ aux [] [f] in
  if Id.mem f @@ get_fv @@ snd @@ decomp_funs @@ Id.assoc f prog.fun_def_env then
    fs
  else
    List.filter_out (Id.same f) fs

let term_of_prog prog =
  prog.fun_def_env
  |> List.last
  |> fst
  |> make_var
  |> make_lets prog.fun_def_env


let take_funs_of_depth env f depth =
  let rec aux acc fs depth =
    if depth <= 0 then
      acc
    else
      let fs' =
        let aux g =
          let xs,t = decomp_funs @@ Id.assoc g env in
          List.Set.diff ~eq:Id.eq (get_fv t) (g::xs)
        in
        fs
        |> List.flatten_map aux
        |> List.unique ~eq:Id.eq
      in
      aux (fs@acc) fs' (depth-1)
  in
  aux [] [f] depth
