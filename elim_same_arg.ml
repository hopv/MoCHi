open Util
open Syntax
open Term_util
open Type


module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)


(*let tbl = Hashtbl.create 0



let update_const = make_col2 (fun _ _ -> ()) ()

let update_constr_term t =
  match t with
  | Let(flag, [f,(xs),t1], t2) ->
      update_constr_term t1;
      update_constr_term t2;

      List.iter aux bindings;
      update_constr_term t2
  | Let _ -> unsupported "update_constr"
  | _ -> update_constr.tr_term_rec t

  try
    Hashtbl.find tbl (i, j, Id.to_string f)
  with
  | Not_found ->
*)



let get_args = make_col2 [] List.rev_append

let get_args_desc (f:id) desc =
  match desc with
    App({desc=Var g}, ts) when Id.(f = g) ->
      List.fold_left (fun args t -> get_args.col2_term f t @ args) ts ts
  | _ -> get_args.col2_desc_rec f desc

let () = get_args.col2_desc <- get_args_desc

let get_args = get_args.col2_term



let same_term env t1 t2 =
  if is_simple_aexp t1 && is_simple_aexp t2
  then
    let conv t = FpatInterface.conv_formula @@ snd @@ CEGAR_trans.trans_term t in
    let env' = List.map conv env in
    let p' = conv @@ make_eq t1 t2 in
    FpatInterface.implies env' [p']
  else t1.desc = t2.desc

let make_all xs =
  let n = List.length xs in
  let aux i j =
    match Id.typ (List.nth xs i), Id.typ (List.nth xs j) with
    | TBase TInt, TBase TInt -> [i,j]
    | _ -> []
  in
  List.fromto 1 n
  |> List.map (fun i -> List.flatten @@ List.map (aux (i-1)) @@ List.fromto i n)
  |> List.flatten

let make_env xs same_args =
  let aux (i,j) =
    let t1 = make_var @@ List.nth xs i in
    let t2 = make_var @@ List.nth xs j in
    match t1.typ, t2.typ with
    | TBase TInt, TBase TInt -> [make_eq t1 t2]
    | _ -> []
  in
  List.flatten @@ List.map aux same_args




let get_diff_args = make_col2 [] (@@@)

let rec get_same_args env f t args =
  let diff_args = get_diff_args.col2_term (env,f) t in
  let same_args = List.Set.diff args diff_args in
  if same_args = args
  then args
  else get_same_args env f t same_args

let is_partial f ts =
  let xs,_ = decomp_tfun @@ Id.typ f in
  List.length xs <> List.length ts

let get_diff_args_desc (env,f) desc =
  match desc with
  | Var g when Id.(f = g) ->
     make_all @@ fst @@ decomp_tfun @@ Id.typ g
  | App({desc=Var g}, ts) when Id.(f = g) && is_partial g ts ->
     make_all @@ fst @@ decomp_tfun @@ Id.typ g
  | App({desc=Var g}, ts) when Id.(f = g) ->
      let its = List.mapi (fun i t -> i,t) ts in
      let rec aux acc = function
          [] -> acc
        | (i,t)::its' ->
            let diff = List.map (fun (i',t') -> if same_term env t t' then [] else [i,i']) its' in
            let diff' = List.flatten diff in
            aux (diff' @ acc) its'
      in
      let diff_args = List.flatten @@ List.map (get_diff_args.col2_term (env,f)) ts in
      aux diff_args its
  | Local(Decl_let ([_] as bindings), t) ->
      let aux (g,t') =
        let xs,t' = decomp_funs t' in
        let all = make_all xs in
        let same_args = get_same_args env g t all in
        let env' = make_env xs same_args in
        get_diff_args.col2_term (env'@env,f) t'
      in
      let diff_args = get_diff_args.col2_term (env,f) t in
      List.flatten (List.map aux bindings) @ diff_args
  | Local(Decl_let bindings, t) -> raise (Fatal "Not implemented (get_diff_args)")
  | _ -> get_diff_args.col2_desc_rec (env,f) desc

let () = get_diff_args.col2_desc <- get_diff_args_desc

let get_diff_args env f t = get_diff_args.col2_term (env,f) t



let elim_nth ns xs = xs
  |> List.mapi (fun i x -> if List.mem i ns then [] else [x])
  |> List.flatten



let elim_arg = make_trans2 ()

let elim_arg_desc (f,args) desc =
  match desc with
    App({desc=Var g}, ts) when Id.(f = g) ->
      let ts' = List.map (elim_arg.tr2_term (f,args)) @@ elim_nth args ts in
      App(make_var g, ts')
  | _ -> elim_arg.tr2_desc_rec (f,args) desc

let () = elim_arg.tr2_desc <- elim_arg_desc

let elim_arg f args t = elim_arg.tr2_term (f,args) t




let elim_arg_typ args typ =
  match typ with
  | TFun _ ->
      let xs,typ' = decomp_tfun typ in
      let xs' = elim_nth args xs in
      List.fold_right (fun x typ -> TFun(x,typ)) xs' typ'
  | _ -> (if (args<>[]) then (Format.eprintf "typ:%a@." Print.typ typ; assert false)); typ






let trans = make_trans2 ()

let trans_desc env desc =
  match desc with
  | Local(Decl_let [f,t1], t2) ->
      let xs,t1 = decomp_funs t1 in
      let same_args = get_same_args env f t2 @@ make_all xs in
      let same_args' =
        if is_non_rec [f, make_funs xs t1] then
          same_args
        else
          let rec aux same_args =
(*
            let env' = make_env xs same_args @@@ env in (* unused for speed *)
*)
            let same_args' = get_same_args env f t1 same_args in
            if same_args = same_args'
            then same_args
            else aux same_args'
          in
          aux same_args
      in
      if Debug.check() then
        begin
          Color.printf Color.Reverse "%a: [" Id.print f;
          List.iter (fun (x,y) -> Color.printf Color.Reverse "%d,%d; " x y) same_args';
          Color.printf Color.Reverse "]@."
        end;
      let elim_args = List.map snd same_args' in
      let f' = Id.map_typ (elim_arg_typ elim_args) f in
      let xs' = elim_nth elim_args xs in
      let t1' = t1
                |> trans.tr2_term (make_env xs same_args' @ env)
                |> subst_map @@ List.map (fun (i,j) -> List.nth xs j, make_var @@ List.nth xs i) same_args'
                |> elim_arg f elim_args
                |> subst_var f f'
      in
      let t2' = t2
                |> trans.tr2_term env
                |> elim_arg f elim_args
                |> subst_var f f'
      in
      Local(Decl_let [f',make_funs xs' t1'], t2')
  | _ -> trans.tr2_desc_rec env desc

let () = trans.tr2_desc <- trans_desc

(** Assume that the input is in CPS *)
let trans t =
  assert (is_id_unique t);
  trans.tr2_term [] t
