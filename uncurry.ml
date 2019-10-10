open Syntax
open Term_util
open Type
open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type index = IVar of string | ITerm of int
type typ = TVar of typ option ref | TBase | TFun of typ * int * typ | TTuple of typ list

let gen counter = incr counter; !counter


let print_constr fm = function
  | (x, y) -> Format.fprintf fm "{%d} = {%d}" x y
let rec print fm typ =
  match typ with
  | TBase -> Format.fprintf fm "base"
  | TVar{contents=Some typ} -> print fm typ
  | TVar _ -> Format.fprintf fm "!!!"
  | TFun(typ1,id,typ2) ->
      Format.fprintf fm "@[<hov 2>(%a) -[%d]->@ %a@]" print typ1 id print typ2
  | TTuple typs ->
      Format.fprintf fm "(@[<hov 2>%a@])" (print_list print "@ *@ ") typs


let rec from_type typ =
  match typ with
  | Type.TBase _ -> TBase
  | Type.TFun(x,typ') -> TFun(from_type @@ Id.typ x, 0, from_type typ')
  | Type.TTuple typs -> TTuple (List.map (from_type -| Id.typ) typs)
  | Type.TApp _
  | Type.TData _
  | Type.TVarLazy _
  | Type.TVar _
  | Type.TAttr _
  | Type.TFuns _
  | Type.TVariant _
  | Type.TRecord _
  | Type.TModule _ -> unsupported "Uncurry.from_type"

let rec decomp_tfun sol = function
  | TVar {contents = Some typ} -> decomp_tfun sol typ
  | TFun(typ1,id,typ2) ->
      if sol id
      then [typ1], typ2
      else
        let typs, typ2' = decomp_tfun sol typ2 in
        typ1::typs, typ2'
  | typ -> [], typ


let add_env env idx = Hashtbl.add env idx @@ TVar (ref None)
let add_env_term env id = add_env env @@ ITerm id
let add_env_var env x = if false then Format.printf "ADD: %a@." Id.print x; add_env env @@ IVar (Id.to_string x)

let init = make_trans2 ()
let init_term (counter,env) t =
  let t' = init.tr2_term_rec (counter,env) t in
  let id = gen counter in
  add_env_term env id;
  add_attr (AId id) t'
let () = init.tr2_term <- init_term
let init = init.tr2_term


let get_id ({attr} as t) =
  match List.filter_map (function AId id -> Some id | _ -> None) attr with
  | [id] -> id
  | _ -> Format.eprintf "%a@." Print.term t;assert false
let get_typ env t = Hashtbl.find env @@ ITerm (get_id t)
let get_typ_var env x = Hashtbl.find env @@ IVar (Id.to_string x)

let rec unify typ1 typ2 =
  match typ1, typ2 with
  | TVar {contents = Some typ1}, _ -> unify typ1 typ2
  | _, TVar {contents = Some typ2} -> unify typ1 typ2
  | TBase, TBase -> []
  | TFun(typ11, b1, typ12), TFun(typ21, b2, typ22) ->
      let constr1 = unify typ11 typ21 in
      let constr2 = unify typ12 typ22 in
      (b1, b2)::constr1@constr2
  | TTuple typs1, TTuple typs2 ->
      List.flatten @@ List.map2 unify typs1 typs2
  | TVar r1, TVar r2 when r1 == r2 -> []
  | TVar({contents = None} as r), typ
  | typ, TVar({contents = None} as r) ->
      r := Some typ;
      []
  | _ -> assert false

let set =ref false

let rec infer (env,counter) t =
  match t.desc with
  | Event _
  | Const _
  | Bottom -> unify (get_typ env t) @@ from_type t.typ
  | Var x when Id.is_coefficient x -> unify (get_typ env t) TBase
  | Var x ->
      if false then Format.printf "x: %a@." Print.id x;
      unify (get_typ env t) @@ get_typ_var env x
  | App(t1, ts) ->
      assert (ts <> []);
      let constr = List.flatten_map (infer (env,counter)) (t1::ts) in
      let id = ref None in
      let aux t typ =
        let id' = gen counter in
        if !id = None then id := Some id';
        TFun(get_typ env t, id', typ)
      in
      let typ = List.fold_right aux ts @@ get_typ env t in
      if false then if !id <> None then Format.printf "LET: %d@." @@ Option.get !id;
      (0, Option.get !id) :: unify (get_typ env t1) typ @ constr
  | Local(Decl_let bindings, t2) ->
      let aux (f,t1) =
        let xs,t1 = decomp_funs t1 in
        List.iter (add_env_var env) (f::xs);
        let id = ref None in
        let aux x typ =
          let id' = gen counter in
          if !id = None then id := Some id';
          TFun(get_typ_var env x, id', typ)
        in
        let typ = List.fold_right aux xs @@ get_typ env t1 in
        if false then Format.printf "id[%a]: %a@." Id.print f (Option.print Format.pp_print_int) !id;
        if false then if !id <> None then Format.printf "LET: %d@." @@ Option.get !id;
        let constr1 = (if xs <> [] then [0, Option.get !id] else []) @ unify (get_typ_var env f) typ in
        let constr2 = infer (env,counter) t1 in
        constr1 @ constr2
      in
      infer (env,counter) t2 @ List.flatten_map aux bindings
  | BinOp(op, t1, t2) ->
      infer (env,counter) t1 @ infer (env,counter) t2
  | Not t1 ->
      infer (env,counter) t1
  | If(t1, t2, t3) ->
      infer (env,counter) t1 @ infer (env,counter) t2 @ infer (env,counter) t3
  | Tuple ts ->
      List.flatten_map (infer (env,counter)) ts
  | Proj(i,t) ->
      infer (env,counter) t
  | _ ->
      Format.eprintf "%a@." Print.term t;
      unsupported "Uncurry.infer"



let rec solve sets constr =
  if false then if constr <> [] then Format.printf "%a@." print_constr @@ List.hd constr;
  if false then Format.printf "rest: %d@." @@ List.length constr;
  if false then Format.printf "sets: %a@.@." (List.print @@ List.print Format.pp_print_int) @@ List.map IntSet.elements sets;
  match constr with
  | [] ->
      let set = List.find (IntSet.mem 0) sets in
      fun n -> IntSet.mem n set
  | (x,y)::constr' ->
      let sets1,sets2 = List.partition (fun set -> IntSet.mem x set || IntSet.mem y set) sets in
      let sets' = List.fold_left IntSet.union (IntSet.of_list [x;y]) sets1 :: sets2 in
      solve sets' constr'
let solve constr = solve [IntSet.singleton 0] constr

let uncurry = make_trans2 ()
let uncurry_term (env,sol) t =
  match t.desc with
  | Var x ->
      let rec aux typ1 typ2 =
        let typs,typ1' = decomp_tfun sol typ1 in
        let xs,typ2' = Type.decomp_tfun typ2 in
        if typs = []
        then typ2
        else
          let xs1,xs2 = List.split_nth (List.length typs) xs in
          TFun(new_var_of_term @@ make_tuple @@ List.map make_var xs1, aux typ1' @@ List.fold_right _TFun xs2 typ2')
      in
      make_var @@ Id.set_typ x @@ aux (get_typ_var env x) @@ Id.typ x
  | App(t1, ts) ->
      let rec aux ts typ =
        if ts = []
        then []
        else
          let typs,typ' = decomp_tfun sol typ in
          assert (typs <> []);
          let ts1,ts2 = List.split_nth (List.length typs) ts in
          make_tuple ts1 :: aux ts2 typ'
      in
      let t1' = uncurry.tr2_term (env,sol) t1 in
      let ts' = List.map (uncurry.tr2_term (env,sol)) ts in
      make_app t1' @@ aux ts' @@ get_typ env t1
  | Local(Decl_let bindings, t2) ->
      let aux (f,t1) =
        let xs,t1 = decomp_funs t1 in
        let rec aux xs typ =
          let typs,typ' = decomp_tfun sol typ in
          if false then Format.printf "f: %a@." Id.print f;
          if false then Format.printf "typ: %a@." print typ;
          if false then Format.printf "|typs|: %d@." @@ List.length typs;
          if false then Format.printf "|xs|: %d@." @@ List.length xs;
          if xs = []
          then []
          else
            let xs1,xs2 = List.split_nth (List.length typs) xs in
            xs1 :: aux xs2 typ'
        in
        let xss = aux xs @@ get_typ_var env f in
        let aux' ys t1 =
          let y = new_var_of_term @@ make_tuple @@ List.map make_var ys in
          match ys with
          | [] -> assert false
          | [z] -> make_fun y @@ subst_var z y t1
          | _ -> make_fun y @@ subst_map (List.mapi (fun i z -> z, make_proj i @@ make_var y) ys) t1
        in
        let t1' = uncurry.tr2_term (env,sol) t1 in
        let t = List.fold_right aux' xss t1' in
        Id.set_typ f t.typ, t
      in
      let bindings' = List.map aux bindings in
      make_let bindings' @@ uncurry.tr2_term (env,sol) t2
  | _ -> uncurry.tr2_term_rec (env,sol) t

let () = uncurry.tr2_term <- uncurry_term
let uncurry = uncurry.tr2_term


let uncurry t =
  let counter = ref 0 in
  let env = Hashtbl.create 0 in
  let t' = init (counter,env) t in
  let constr = infer (env,counter) t' in
  if false then Format.printf "constr: %a@." (List.print print_constr) constr;
  let sol = solve constr in
  t'
  |> uncurry (env,sol)
  |> Trans.remove_id

let to_tfuns = make_trans2 ()

let to_funs_var env sol x =
  let rec decomp typ n =
    if false then Format.printf "decomp: %a, %d@." Print.typ typ n;
    if n = 0
    then [], typ
    else
      match typ with
      | Type.TFun(x,typ') ->
          let xs',typ'' = decomp typ' (n-1) in
          x::xs', typ''
      | _ -> assert false
  in
  let rec aux typ1 typ2 =
    if false then Format.printf "typ1: %a@." print typ1;
    if false then Format.printf "typ2: %a@.@." Print.typ typ2;
    let typs,typ1' = decomp_tfun sol typ1 in
    if typs = []
    then typ2
    else
      let xs,typ2' = decomp typ2 (List.length typs) in
      let xs' = List.map2 (fun x typ -> Id.set_typ x @@ aux typ (Id.typ x)) xs typs in
      TFuns(xs', aux typ1' typ2')
  in
  Id.set_typ x @@ aux (get_typ_var env x) @@ Id.typ x


let to_tfuns_desc (env,sol) desc =
  match desc with
  | Local(Decl_let bindings, t) ->
      let aux (f,t) (bindings',t') =
        let xs,t = decomp_funs t in
        if false then Format.printf "f: %a@." Id.print f;
        let f' = to_funs_var env sol f in
        if false then Format.printf "f': %a@." Print.id_typ f';
        let xs' = List.map (to_funs_var env sol) xs in
        let sbst = List.fold_right2 subst_var (f::xs) (f'::xs') in
        (f', make_funs xs' @@ sbst @@ to_tfuns.tr2_term (env,sol) t)::bindings', sbst t'
      in
      let bindings',t' = List.fold_right aux bindings @@ ([], to_tfuns.tr2_term (env,sol) t) in
      let map = List.map2 (fun (f,_) (f',_) -> f, f') bindings bindings' in
      let bindings'' = List.map (Pair.map_snd @@ List.fold_right (Fun.uncurry subst_var) map) bindings' in
      Local(Decl_let bindings'', t')
  | _ -> to_tfuns.tr2_desc_rec (env,sol) desc

let () = to_tfuns.tr2_desc <- to_tfuns_desc

let to_tfuns t =
  Debug.printf "[UNCURRY] INPUT; %a@." Print.term t;
  let counter = ref 0 in
  let env = Hashtbl.create 0 in
  let t' = init (counter,env) t in
  Debug.printf "[UNCURRY] t'; %a@." Print.term t';
  let constr = infer (env,counter) t' in
  Debug.printf "[UNCURRY] constr: %a@." (List.print print_constr) constr;
  let sol = solve constr in
  Trans.reconstruct @@ to_tfuns.tr2_term (env,sol) t
