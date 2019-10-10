open Util
open Syntax
open Term_util
open Type

type t = {head : term; body : term list}
type horn_clauses = t list

type pred_var = int

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let pred_var = Id.make (-1) "v" [] Ty.int
let pred_var_term = make_var pred_var
let make_pred_var p ts =
  let typs = List.map Syntax.typ ts in
  let typ = List.fold_right make_tfun typs Ty.bool in
  Id.make p PredVar.pvar_name [Id.Predicate] typ
let is_pred_var = PredVar.is_pvar
let get_pred_id = Id.id
let get_pred_id_of_term t =
  match t.desc with
  | App({desc=Var x}, ts) -> assert (is_pred_var x); Some (get_pred_id x)
  | _ -> None

let print fm {head;body} =
  let pr_aux fm t =
    if true then
      Print.term fm t
    else (* For rcaml *)
      t
      |> Format.asprintf "%a" Print.term
      |> String.remove_char '_'
      |> String.remove_char '\''
      |> Format.fprintf fm "@[%s@]"
  in
  let pr fm t =
    match t.desc with
    | Var p when is_pred_var p -> Format.fprintf fm "%a()" pr_aux t
    | App(p, ts) -> Format.fprintf fm "@[%a(%a)@]" pr_aux p (print_list pr_aux ", ") ts
    | _ -> pr_aux fm t
  in
  if head = false_term
  then Format.fprintf fm "@[?- %a.@]" (print_list pr ",@ ") body
  else Format.fprintf fm "@[<hov 4>%a :-@ %a.@]" pr head (print_list pr ",@ ") body
let print_horn_clauses fm hcs =
  Format.fprintf fm "@[%a@]" (print_list print "@\n") hcs

let of_pair_list xs = List.map (fun (body,head) -> {body;head}) xs

let map f {body;head} = {body = List.map f body; head = f head}
let flatten_map f {body;head} = {body = List.flatten_map f body; head = List.get @@ f head}

let get_pred_ids_hcs hcs =
  hcs
  |> List.flatten_map (fun {body;head} -> List.filter_map get_pred_id_of_term (head::body))
  |> List.unique

let decomp_pred_app t =
  match t.desc with
  | App({desc=Var p}, ts) when is_pred_var p -> Some (p, ts)
  | _ -> None

let inline need hcs =
  let hcs', env =
    let can_inline head hcs1 hcs2 =
      match decomp_pred_app head with
      | None -> false
      | Some (p,_) ->
          let aux {head} = not @@ Id.mem p @@ get_fv head in
          is_pred_var p &&
          not @@ List.mem (get_pred_id p) need &&
          List.for_all aux hcs1 &&
          List.for_all aux hcs2
    in
    let rec aux acc hcs_done hcs =
      match hcs with
      | [] -> hcs_done, acc
      | {head;body}::hcs' when can_inline head hcs_done hcs' ->
          let p,ts = Option.get @@ decomp_pred_app head in
          aux ((p,(ts,body))::acc) hcs_done hcs'
      | hc::hcs' -> aux acc (hc::hcs_done) hcs'
    in
    aux [] [] hcs
  in
  let replace env t =
    try
      let p,ts = Option.get @@ decomp_pred_app t in
      let ts',body = Id.assoc p env in
      List.map2 make_eq ts ts' @ body
    with _ -> [t]
  in
  let env' =
    let rec aux env_acc env_rest =
      match env_rest with
      | [] -> env_acc
      | (p,(ts,body))::env_rest' when List.exists (Id.mem_assoc -$- env) @@ List.flatten_map get_fv body ->
          let body' = List.flatten_map (replace (env_rest@@@env_acc)) body in
          aux env_acc ((p,(ts,body'))::env_rest')
      | x::env_rest' ->
          aux (x::env_acc) env_rest'
    in
    aux [] env
  in
  List.map (flatten_map @@ replace env') hcs'


let normalize hcs =
  let normalize_hc {head;body} =
    match decomp_pred_app head with
    | None -> {head;body}
    | Some(p, args) ->
        let aux arg (args,body) =
          if is_var arg then
            arg::args, body
          else
            let x = new_var_of_term arg in
            let arg' = make_var x in
            arg'::args, make_eq (make_var x) arg :: body
        in
        let args',body' = List.fold_right aux args ([],body) in
        {head=make_app (make_var p) args'; body=body'}
  in
  List.map normalize_hc hcs


let inline need hcs =
  Debug.printf "INLINE INPUT: %a@." print_horn_clauses hcs;
  let hcs' =
    hcs
    |> normalize
    |@> Debug.printf "INLINE NORMALIZED: %a@." print_horn_clauses
    |> List.map (fun hc -> hc, List.filter_map get_pred_id_of_term hc.body)
  in
  let has_multi_rule =
    let rec aux acc xs =
      match xs with
      | [] | [_] -> acc
      | x1::x2::xs' when Id.(x1 = x2) ->
          aux (x1::acc) xs'
      | x1::x2::xs' ->
          aux acc (x2::xs')
    in
    hcs
    |> List.filter_map (fun {head} -> decomp_pred_app head)
    |> List.map fst
    |> List.sort Id.compare
    |> aux []
  in
  let check_can_inline head ids =
    match decomp_pred_app head with
    | None -> false
    | Some(p,_) ->
        ids = [] &&
          not @@ List.mem (get_pred_id p) need &&
            not @@ Id.mem p has_multi_rule
  in
  let can_inline =
    let check i ({head},ids) =
      if check_can_inline head ids then
        Some i
      else
        None
    in
    ref @@ List.filter_mapi check hcs'
  in
  let a_hcs = Array.of_list hcs' in
  while !can_inline <> [] do
    let i = List.hd !can_inline in
    can_inline := List.tl !can_inline;
    let {head;body},_ = a_hcs.(i) in
    Debug.printf "CAN_INLINE: %d, %a@." i Print.term head;
    let p,args = Option.get @@ decomp_pred_app head in
    let id = get_pred_id p in
    let aux j (hc,ids) =
      let ids' = List.filter_out ((=) id) ids in
      Debug.printf "i: %d@." i;
      Debug.printf "ids[%d]: %a@." j (List.print Format.pp_print_int) ids;
      Debug.printf "ids'[%d]: %a@." j (List.print Format.pp_print_int) ids';
      if ids <> ids' then
        let replace t =
          try
            let p',args' = Option.get @@ decomp_pred_app t in
            Debug.printf "p: %a@." Id.print p;
            Debug.printf "p': %a@." Id.print p';
            if Id.(p = p') then
              let args'' = List.map (Option.get -| decomp_var) args in
              Debug.printf "args'': %a@." (List.print Id.print) args'';
              Debug.printf "args': %a@." (List.print Print.term) args';
              List.map (List.fold_right2 subst args'' args') body
            else
              [t]
          with Option.No_value -> [t]
        in
        Debug.printf "SUBST: %d@." j;
        let body' = List.flatten_map replace hc.body in
        let hc' = {hc with body=body'} in
        Debug.printf "  %a =>@." print hc;
        Debug.printf "  %a@."  print hc';
        if check_can_inline hc.head ids' then
          can_inline := j :: !can_inline;
        a_hcs.(j) <- hc', ids';
    in
    Array.iteri aux a_hcs
  done;
  a_hcs
  |> Array.to_list
  |> List.map fst
