open! Util
open! Type
open! Syntax
open! Type_util
open! Term_util

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type cnf = term list list
and chc = {body:term list; head:term}

let print_chc fm {body; head} =
  Format.fprintf fm "@[<hov 4>%a :-@ %a@]" Print.term head (print_list Print.term ", ") body

let push_not_into (f:term) : term =
  (* (aux true t <=> not t) and (aux false t <=> t)*)
  let rec aux flip (f:term) =
    match f.desc with
    | BinOp(And, _, _) ->
        let fs = List.map (aux flip) @@ decomp_and f in
        if flip then Term.ors fs else Term.ands fs
    | BinOp(Or, _, _) ->
        let fs = List.map (aux flip) @@ decomp_or f in
        if flip then Term.ands fs else Term.ors fs
    | Not t -> aux (not flip) t
    | _ ->
        if flip then Term.not f else f
  in
  aux false f

let rec convert2cnf (f:term) : cnf =
  let make_or (cnf1:cnf) (cnf2:cnf) : cnf =
    Combination.product cnf1 cnf2
    |> List.map (fun (d1,d2) -> d1@d2)
  in
  match f.desc with
  | BinOp(And, _, _) ->
      let fs = decomp_and f in
      List.flatten_map convert2cnf fs
  | BinOp(Or, _, _) ->
      let fs = decomp_or f in
      List.fold_right (make_or -| convert2cnf) fs [[]]
  | _ -> [[f]]

let chc_of_cnf (cnf:cnf) : chc list =
  let conv fs =
    let pos,neg =
      List.partition (function {desc=App _} -> true | _ -> false) fs
    in
    let head =
      match pos with
      | [] -> Term.false_
      | [{desc=App _} as t] -> t
      | _ -> assert false
    in
    let body = List.map Term.not neg in
    {head; body}
  in
  List.map conv cnf

(* Change arguments in head into variables *)
let normalize_chc (cs:chc list) : chc list =
  if List.L.exists cs
       ~f:(function {head={desc=App(_,ts)}; _} ->
                      List.L.exists ts
                        ~f:(function {desc=Var _} -> false | _ -> true)
                  | _ -> false) then
    assert false;
  cs

let seqs_of_conj ts =
  List.L.fold_right ts ~init:Term.true_ ~f:(fun t acc ->
      match t.desc with
      | App _ -> Term.seq t acc
      | _ -> Term.assume t acc)

let normalize_body ts =
  let ts1,ts2 = List.partition (function {desc=App _} -> true | _ -> false) ts in
  make_ands ts2 :: ts1

let unify (f,xs,body1) (g,ys,body2) =
  assert Id.(f = g);
  assert (List.compare_lengths xs ys = 0);
  let body2' =
    if Id.List.eq xs ys then
      body2
    else
      subst_var_map (List.combine ys xs) body2
  in
  f, xs, Term.br body1 body2'

let add_rand bv t =
  let rands =
    get_fv t
    |> Id.List.Set.diff -$- bv
    |> List.filter_out is_fun_var
    |> Id.List.unique
    |> List.map (Pair.add_right (Id.typ |- Term.rand))
  in
  Term.lets rands t

let prog_of_chc cs =
  let defs,goals =
    List.L.partition_map cs ~f:(function
        | {head = {desc=App({desc=Var (LId f)},ts)}; body} ->
            let xs = List.map ValE.(_Var |- _LId) ts in
            let t =
              body
              |> normalize_body
              |> seqs_of_conj
            in
            Left (f, xs, add_rand xs t)
        | {head = {desc=Const False}; body} -> Right body
        | _ -> assert false)
  in
  let defs =
    defs
    |> List.classify ~eq:(Compare.eq_on Triple.fst)
    |> List.map (List.reduce_left unify)
    |> List.map (fun (f,xs,t) -> f, Term.funs xs t)
  in
  let defs_fv =
    let make f =
      let xs,ty = decomp_tfun (Id.typ f) in
      let xs = List.map Id.new_var_id xs in
      Term.(funs xs (bot ty))
    in
    let fv = List.flatten_map (snd |- get_fv) defs in
    let bv = List.map fst defs in
    Id.List.Set.(fv - bv)
    |> List.map (Pair.add_right make)
  in
  let goal =
    goals
    |> List.map seqs_of_conj
    |> List.map (add_rand [])
    |> Term.brs
  in
  Term.(lets defs_fv (let_ defs (seq (seq goal fail) unit)))

let rec remove_forall t =
  match t.desc with
  | BinOp(And, _, _) ->
      t
      |> decomp_and
      |> List.map remove_forall
      |> Term.ands
  | Forall(_, t) -> remove_forall t
  | _ -> t

let pr s t = Dbg.printf "@[##[chc2prog] %s:@\n  %a@]@\n@\n" s Print.term t
let pr_chc s chc = Dbg.printf "@[##[chc2prog] %s:@\n  %a@]@\n@\n" s (Print.list print_chc) chc

let normalize_var_name =
  let tr = Tr.make () in
  let rename s =
    let s' = String.sign_to_letters s in
    if s'.[0] = '_' then
      String.sub s' 1 (String.length s' - 1)
      |@> fun s'' -> assert (Char.is_letter s''.[0])
    else
      s
  in
  tr.var <- Id.map_name rename;
  tr.term <- set_afv_shallowly -| tr.term_rec;
  tr.term

let trans formula =
  formula
  |@> pr "input"
  |> remove_forall
  |@> pr "remove_forall"
  |> push_not_into
  |@> pr "push_not_into"
  |> convert2cnf
  |> chc_of_cnf
  |@> pr_chc "chc_of_cnf"
  |> normalize_chc
  |@> pr_chc "normalize_chc"
  |> prog_of_chc
  |> normalize_var_name
