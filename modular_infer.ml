open Util
open Syntax
open Term_util
open Type
open Modular_common

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

module CT = Comp_tree
module HC = Horn_clause

(* How to instansiate predicates which do not occur in constraints *)
type mode = ToTrue | ToFalse | ToNatural | ToStronger


type constr =
  | Exp of term
  | And of constr * constr
  | Imply of constr * constr
  | Sub of type_template * type_template
  | Pred of id * term list
and type_template =
  | Var of id
  | Arg of type_template * term list
  | PApp of type_template * term list
  | Singleton of term
  | Base of (Type.base * HC.pred_var) option (** None represents the result type X *)
  | Const of id * term
  | Fun of id * type_template * type_template
  | Inter of typ * type_template list


let print_mode fm = function
  | ToTrue -> Format.fprintf fm "ToTrue"
  | ToFalse -> Format.fprintf fm "ToFalse"
  | ToNatural -> Format.fprintf fm "ToNatural"
  | ToStronger -> Format.fprintf fm "ToStronger"

let rec print_constr fm = function
  | Exp t -> Format.fprintf fm "%a" Print.term t
  | And(c1, c2) -> Format.fprintf fm "@[<hov 3>(%a@ &&@ %a)@]" print_constr c1 print_constr c2
  | Imply(c1, c2) -> Format.fprintf fm "@[<hov 3>(%a@ =>@ %a)@]" print_constr c1 print_constr c2
  | Sub(typ1, typ2) -> Format.fprintf fm "@[<hov 3>(%a@ <:@ %a)@]" print_template typ1 print_template typ2
  | Pred(x,ts) -> Format.fprintf fm "@[P%a%a@]" Id.print x (List.print Print.term) ts

and print_template fm = function
  | Var f -> Id.print fm f
  | Arg(typ, ts) -> Format.fprintf fm "%a(%a)" print_template typ (print_list Print.term ",") ts
  | PApp(typ, ts) -> Format.fprintf fm "%a%a" print_template typ (List.print Print.term) ts
  | Singleton t -> Format.fprintf fm "{%a}" Print.term t
  | Base None -> Format.fprintf fm "*"
  | Base (Some(base, p)) -> Format.fprintf fm "%a[P_%d]" Type.print_base base p
  | Const(x,t) -> Format.fprintf fm "{%a:int | %a}" Id.print x Print.term t
  | Fun(x, tmp1, tmp2) when is_fun_var x -> Format.fprintf fm "(@[<hov 2>%a ->@ %a@])" print_template tmp1 print_template tmp2
  | Fun(x, tmp1, tmp2) -> Format.fprintf fm "(@[<hov 2>%a:%a ->@ %a@])" Id.print x print_template tmp1 print_template tmp2
  | Inter(_, []) -> Format.fprintf fm "T"
  | Inter(_, tmps) -> Format.fprintf fm "(@[%a@])" (print_list print_template " /\\@ ") tmps

let print_tmp_env fm env =
  let print_idx fm x =(*
    match nid with
    | None -> Format.fprintf fm "%a" Id.print x
    | Some nid' -> Format.fprintf fm "%a{%d}" Id.print x nid'
                             *)
    Format.fprintf fm "%a" Id.print x
  in
  Format.fprintf fm "%a" (List.print @@ Pair.print print_idx print_template) env


let _And c1 c2 =
  if c1 = Exp true_term then
    c2
  else if c2 = Exp true_term then
    c1
  else
    And(c1, c2)
let _Ands constrs = List.fold_right _And constrs (Exp true_term)
let rec inline_PApp typ ts =
  match typ with
  | Var _ -> PApp(typ, ts)
  | Arg _ -> PApp(typ, ts)
  | PApp(typ', ts') -> PApp(typ', ts'@ts)
  | Singleton _ -> typ
  | Base None -> typ
  | Base _ -> PApp(typ, ts)
  | Const _ -> typ
  | Fun(x, typ1, typ2) -> Fun(x, _PApp typ1 ts, _PApp typ2 ts)
  | Inter(styp, typs) -> Inter(styp, List.map (inline_PApp -$- ts) typs)
and _PApp typ ts =
  let dbg = 0=1 in
  let typ' = inline_PApp typ @@ List.filter (is_base_typ -| Syntax.typ) ts in
  if dbg then Debug.printf "        _PApp(%a, %a)" print_template typ (List.print Print.term) ts;
  if dbg then Debug.printf " = %a@." print_template typ';
  match typ' with
  | PApp(typ'', []) -> typ''
  | _ -> typ'
let rec _Imply cs c =
  if c = Exp true_term then
    Exp true_term
  else
    match cs with
    | [] -> c
    | c1::cs' ->
        if c1 = Exp true_term then
          _Imply cs' c
        else Imply(c1, _Imply cs' c)
let _Inter styp tmps =
  match tmps with
  | [tmp] -> tmp
  | _ -> Inter(styp, tmps)

let rec apply f = function
  | Exp t -> Exp t
  | And(c1,c2) -> And(apply f c1, apply f c2)
  | Imply(c1, c2) -> Imply(apply f c1, apply f c2)
  | Sub(typ1, typ2) -> Sub(f typ1, f typ2)
  | Pred(x,ts) -> Pred(x,ts)
let apply = ()

let rec from_ref_type typ =
  match typ with
  | Ref_type.Base(_, x, t) -> Const(x, t)
  | Ref_type.ADT(_, x, t) -> assert false
  | Ref_type.Fun(x, typ1, Ref_type.Base(base,_,t)) ->
      assert (base = TUnit && t.desc = Const True);
      Fun(x, from_ref_type typ1, Base None)
  | Ref_type.Fun(x, typ1, typ2) -> Fun(x, from_ref_type typ1, from_ref_type typ2)
  | Ref_type.Tuple _ -> assert false
  | Ref_type.Inter(styp, typs) -> _Inter styp @@ List.map from_ref_type typs
  | Ref_type.Union _ -> assert false
  | Ref_type.ExtArg _ -> assert false
  | Ref_type.List _ -> assert false
  | Ref_type.App _ -> assert false
  | Ref_type.Exn _ -> assert false

let rec get_fv_typ = function
  | Var f -> [f]
  | Arg(typ, ts) -> get_fv_typ typ @ List.flatten_map Syntax.get_fv ts
  | PApp(typ, ts) -> get_fv_typ typ @ List.flatten_map Syntax.get_fv ts
  | Singleton t -> Syntax.get_fv t
  | Base _ -> []
  | Const _ -> []
  | Fun(x,typ1,typ2) -> List.filter_out (Id.eq x) @@ (get_fv_typ typ1 @ get_fv_typ typ2)
  | Inter(_, typs) -> List.flatten_map get_fv_typ typs
let rec get_fv_constr = function
  | Exp t -> Syntax.get_fv t
  | And(c1, c2) -> get_fv_constr c1 @ get_fv_constr c2
  | Imply _ -> assert false
  | Sub(typ1,typ2) -> get_fv_typ typ1 @ get_fv_typ typ2
  | Pred(x,ts) -> x :: List.flatten_map Syntax.get_fv ts
let get_fv_constr = ()

let rec constr_of_typ typ =
  match typ with
  | PApp(Base(Some(_,p1)), ts) ->
      let ts' = List.filter_out (Syntax.typ |- is_fun_typ) ts in
      Debug.printf "      constr_of_typ: ts: %a@." (List.print Print.term) ts;
      Exp (make_app (make_var @@ HC.make_pred_var p1 ts') ts')
  | PApp(Const(x, t), _) -> Exp t
  | Fun _
  | PApp(Fun _, _) -> Exp true_term
  | Inter(_, typs) ->
      _Ands (List.map constr_of_typ typs)
  | _ ->
      Format.eprintf "  typ: %a@." print_template typ;
      assert false

let rec subst_template x t tmp =
  let sbst = subst_template x t in
  match tmp with
  | Var _ -> tmp
  | Arg(tmp', ts) -> Arg(sbst tmp', List.map (Term_util.subst x t) ts)
  | PApp(tmp', ts) -> PApp(sbst tmp', List.map (Term_util.subst x t) ts)
  | Singleton t' -> Singleton (Term_util.subst x t t')
  | Base _ -> tmp
  | Const _ -> tmp
  | Fun(x, tmp1, tmp2) -> Fun(x, sbst tmp1, sbst tmp2)
  | Inter(typ, tmps) -> Inter(typ, List.map sbst tmps)

let rec subst_constr x t constr =
  let sbst = subst_constr x t in
  match constr with
  | Exp t' -> Exp (Term_util.subst x t t')
  | And(c1, c2) -> _And (sbst c1) (sbst c2)
  | Imply(c1, c2) -> _Imply [sbst c1] (sbst c2)
  | Sub(tmp1, tmp2) -> Sub(subst_template x t tmp1, subst_template x t tmp2)
  | Pred _ -> assert false

let rec expand_type templates val_env typ =
  let dbg = 0=1 in
  let pr f = if dbg then Debug.printf @@ "        ET " ^^ f else Format.ifprintf Format.std_formatter f in
  let et = expand_type templates val_env in
  let r =
  match typ with
  | Singleton _
  | Base _
  | Const _ -> typ
  | Var x ->
      let val_env_x =
        Id.assoc x val_env
        |> CT.val_env_of_value
        |> List.filter_out (fun (x,_) -> Id.mem_assoc x val_env)
      in
      pr "  TEMPLATE: %a@." print_tmp_env templates;
      pr "x: %a@." Id.print x;
      templates
      |> List.filter (Id.eq x -| fst)
      |@> List.iter (fun (x,typ) -> pr "  VAR[%a]: typ: %a@." Id.print x print_template typ)
      |> List.sort compare
      |> List.hd
      |> snd
      |@> pr "  VAR[%a]: typ: %a@." Id.print x print_template
      |> et
      |> List.fold_right (fun (y,v) typ -> subst_template y (CT.term_of_value v) typ) val_env_x
  | PApp(Base None, _) -> Base None
  | PApp(Singleton t, _) -> Singleton t
  | PApp(typ, ts) ->
      begin
        match et typ with
        | Fun(x, typ1, typ2) -> Fun(x, et (PApp(typ1,ts)), et (PApp(typ2,ts)))
        | Inter(typ, typs) -> Inter(typ, List.map (fun typ' -> et @@ PApp(typ',ts)) typs)
        | typ' -> _PApp typ' ts
      end
  | Arg(typ, ts) ->
      begin
        match et typ with
        | Fun(x, typ1, typ2) ->
            begin
              match ts with
              | [] -> typ1
              | t::ts' ->
                  Arg(typ2, ts')
                  |> subst_template x t
                  |> et
                  |@> pr "@[<hov 2>[%a |-> %a]%a = %a@]@." Id.print x Print.term t print_template (Arg(typ2, ts')) print_template
            end
        | Inter(styp, typs) ->
            Inter(styp, List.map (fun typ -> et @@ Arg(typ, ts)) typs)
        | typ' ->
            Format.eprintf "@.typ: %a@." print_template typ;
            Format.eprintf "typ': %a@.@." print_template typ';
            assert false
      end
  | Fun(x, typ1, typ2) -> Fun(x, et typ1, et typ2)
  | Inter(styp, typs) -> Inter(styp, List.map et typs)
  in
  if dbg then pr "typ: %a@." print_template typ;
  if dbg then pr "r: %a@." print_template r;
  r

let rec _PAppSelf typ t =
  match typ with
  | Base _ -> _PApp typ [t]
  | PApp(Base(Some _) as typ', ts) -> _PApp typ' (t::ts)
  | Inter(styp,typs) ->
      Inter(styp, List.map (_PAppSelf -$- t) typs)
  | _ ->
      Format.eprintf "%a@." print_template typ;
      assert false

let rec inline_sub templates val_env typ1 typ2 =
  let _dbg = false in
  let r =
  match typ1,typ2 with
  | Inter(_,typs1), Inter(_,typs2) -> _Ands @@ List.map2 (inline_sub templates val_env) typs1 typs2
  | Singleton t, _ -> constr_of_typ @@ _PAppSelf typ2 t
  | Base None, Base None -> Exp true_term
  | PApp(Base(Some p1) as typ1', ts1), PApp(Base(Some p2) as typ2', ts2) ->
      _PApp typ2' (HC.pred_var_term::ts2)
      |> constr_of_typ
      |> _Imply [constr_of_typ @@ _PApp typ1' (HC.pred_var_term::ts1)]
  | Fun(_, (Fun _ as typ11), typ12), Fun(_, (Fun _ as typ21), typ22) ->
      _And (inline_sub templates val_env typ21 typ11) (inline_sub templates val_env typ12 typ22)
  | Fun(x1,typ11,typ12), Fun(x2,typ21,typ22) ->
      let c1 = subst_constr x1 (make_var x2) @@ inline_sub templates val_env typ21 typ11 in
      let app typ =
        if is_fun_var x2
        then typ
        else expand_type [] val_env @@ _PApp typ [make_var x2]
      in
      let c2 = constr_of_typ @@ app typ21 in
      let c3 = subst_constr x1 (make_var x2) @@ inline_sub templates val_env (app typ12) (app typ22) in
      _And c1 @@ _Imply [c2] c3
  | _ ->
      Format.eprintf "  typ1: %a@." print_template typ1;
      Format.eprintf "  typ2: %a@." print_template typ2;
      assert false
  in
  Debug.printf "    typ1: %a@." print_template typ1;
  Debug.printf "    typ2: %a@." print_template typ2;
  Debug.printf "    r: %a@.@." print_constr r;
  r
(*
let inline_sub templates typ1 typ2 =
  Debug.printf "  typ1: %a@." print_template typ1;
  Debug.printf "  typ2: %a@." print_template typ2;
  inline_sub templates typ1 typ2
*)
let get_nid (Rose_tree.Node({CT.nid}, _)) = nid

let in_comp_tree ct nid =
  Rose_tree.exists (fun {CT.nid=nid'} -> nid' = nid) ct


let hd_of_inter typ =
  match typ with
  | Inter(_, typs) -> List.hd typs
  | _ -> typ

let make_sub_flag = ref true (* for debug *)

let rec decomp_inter typ =
  match typ with
  | Inter(styp, typs) -> List.flatten_map decomp_inter typs
  | _ -> [typ]

let rec decomp_tfun typ =
  match typ with
  | Var _ -> assert false
  | Fun(x,typ1,typ2) -> Pair.map_fst (List.cons (x,typ1)) @@ decomp_tfun typ2
  | Inter(_, [typ']) -> decomp_tfun typ'
  | Inter _ ->
      Format.eprintf "decomp_tfun: %a@." print_template typ;
      assert false
  | _ -> [], typ

let rec copy_template cnt typ =
  match typ with
  | Var _ -> assert false
  | Arg _ -> assert false
  | PApp(typ, _) -> copy_template cnt typ
  | Singleton _ -> assert false
  | Base None -> Base None
  | Base (Some(base, p)) -> Base (Some (base, Counter.gen cnt))
  | Const _ -> typ
  | Fun(x,typ1,typ2) -> Fun(x, copy_template cnt  typ1, copy_template cnt typ2)
  | Inter(styp, typs) -> Inter(styp, List.map (copy_template cnt) typs)

let rec elim_papp typ =
  match typ with
  | PApp(typ, _) -> elim_papp typ
  | Fun(x,typ1,typ2) -> Fun(x, elim_papp typ1, elim_papp typ2)
  | Inter(styp, typs) -> Inter(styp, List.map elim_papp typs)
  | _ -> typ

let merge_template ts = List.flatten ts
let new_pred base cnt = Base (Some(base, Counter.gen cnt))

let rec decomp_fun typ =
  match typ with
  | Fun(x, typ1, typ2) -> Pair.map_fst (List.cons (x, typ1)) @@ decomp_fun typ2
  | _ -> [], typ

let base_of_typ ty =
  match decomp_base ty with
  | Some b -> b
  | None ->
      match ty with
      | TData s -> TPrim s
      | _ ->
          Format.eprintf "%a@." Print.typ ty;
          assert false

let rec init_with_pred_var cnt typ =
  let ip typ = init_with_pred_var cnt typ in
  match typ with
  | Var _ -> assert false
  | Arg _ -> assert false
  | PApp _ -> assert false
  | Singleton _ -> assert false
  | Base None -> Base None
  | Base (Some (base, _)) -> new_pred base cnt
  | Const(x, _) -> new_pred (base_of_typ @@ Id.typ x) cnt
  | Fun(x, typ1, typ2) -> Fun(x, ip typ1, ip typ2)
  | Inter(styp, typs) -> _Inter styp @@ List.map ip typs

let make_sub templates val_env typ1 typ2 =
  Debug.printf "      make_sub: %a@." print_constr (Sub(typ1,typ2));
  let typ1' = expand_type templates val_env typ1 in
  let typ2' = expand_type templates val_env typ2 in
  Debug.printf "      make_sub: %a@." print_constr (Sub(typ1',typ2'));
  let r = inline_sub templates val_env typ1' typ2' in
  Debug.printf "          ===>: %a@." print_constr r;
  r(*;
  Sub(typ1',typ2')*)

let filter_assumption val_env assumption =
  let vars = List.map fst val_env in
  assumption
  |> List.filter (fun t -> List.Set.subset (Syntax.get_fv t) vars)
  |> List.map (fun t -> Exp t)

let make_assumption templates val_env =
  let dbg = 0=0 in
  if dbg then Debug.printf "  [MA] Dom(val_env): %a@." (List.print Id.print) @@ List.map fst val_env;
  let aux x =
    Debug.printf "  [MA] Dom(val_env(%a)): %a@." Id.print x (List.print Id.print) @@ List.map fst @@ CT.val_env_of_value @@ Id.assoc x val_env;
    let val_env_x =
      Id.assoc x val_env
      |> CT.val_env_of_value
      |> List.filter_out (fun (x,_) -> Id.mem_assoc x val_env)
    in
    try
      if dbg then Debug.printf "    [MA] x: %a@." Id.print x;
      make_var x
      |> _PAppSelf @@ List.assoc ~eq:Id.eq x templates
      |@dbg&> Debug.printf "      [MA] typ of %a: %a@." Id.print x print_template
      |> List.fold_right (fun (y,v) typ -> subst_template y (CT.term_of_value v) typ) val_env_x
      |@dbg&> Debug.printf "      [MA] typ' of %a: %a@." Id.print x print_template
      |> constr_of_typ
      |@dbg&> Debug.printf "      [MA] constr: %a@." print_constr
      |> Option.some
    with Not_found -> None
  in
  val_env
  |> List.map fst
  |@dbg&> Debug.printf "  [MA] vars: %a@." (List.print Id.print)
  |> List.filter is_base_var
  |@dbg&> Debug.printf "  [MA] base_vars: %a@." (List.print Id.print)
  |> List.filter_map aux
  |@dbg&> Debug.printf "  [MA] base_vars_constr: %a@." (List.print print_constr)


let subst_template x t typ =
  let r = subst_template x t typ in
  if false then
    Debug.printf "ST: [%a |-> %a] %a = %a@." Id.print x Print.term t print_template typ print_template r;
  r

let new_template_of_simple cnt ty =
  ty
  |> Ref_type.of_simple
  |> from_ref_type
  |> init_with_pred_var cnt

let arg_of x y =
  try
    let s1,s2 = String.split (Id.to_string y) ~by:(Id.to_string x ^ ":") in
    ignore (int_of_string s2);
    s1 = ""
  with _ -> false

let rec make_template cnt args (Rose_tree.Node({CT.nid; var_env; val_env; ce_env; nlabel}, children)) =
  let dbg = 0=0 in
  let pr f = if dbg then Debug.printf @@ "[MT] " ^^ f else Format.ifprintf Format.std_formatter f in
  let templates = merge_template @@ List.map (make_template cnt args) children in
  Debug.printf "@.@.";
  match nlabel with
  | CT.App(f, map) ->
      pr "APP: %a@." CT.print_nlabel nlabel;
      pr "  TEMPLATE: %a@." print_tmp_env templates;
      pr "  Dom(val_env): %a@." (List.print Id.print) @@ List.map fst val_env;
      let typ =
        let head =
          let pargs' =
            pr "  f: %a@." Id.print f;
            pr "  var_env: %a@." (List.print @@ Pair.print Id.print @@ List.print Id.print) var_env;
            Id.assoc f var_env
            |@> pr "  var_env(%a): %a@." Id.print f (List.print Id.print)
            |> List.map make_var
            |@> pr "  pargs': %a@." (List.print Print.term)
          in
          let aux' (pargs,k) (x,CT.Closure(_,_,t)) =
            pr "  x: %a@." Id.print x;
            pr "  pargs,t: %a, %a@." (List.print Print.term) pargs Print.term t;
            let tmp1 =
              if is_base_typ t.typ then
                _PApp (new_pred (base_of_typ t.typ) cnt) (pargs@pargs')
              else
                let typs =
                  templates
                  |> List.filter (fun (y,_) -> arg_of x y)
                  |> List.sort compare
                  |> List.map snd
                in
                if typs = [] then
                  new_template_of_simple cnt t.typ
                else
                  _Inter t.typ typs
            in
            pr "    [%a] tmp1: %a@." Id.print x print_template tmp1;
            make_var x :: pargs, fun tmp2 -> k @@ Fun(x, tmp1, tmp2)
          in
          (snd @@ List.fold_left aux' ([], Fun.id) map) @@ Base None
          |@> pr "  head: %a@." print_template
        in
        head
      in
      pr "  typ[%a]: %a@." Id.print f print_template typ;
      (f, typ) :: templates
      |@> pr "  TEMPLATE: %a@." print_tmp_env
  | CT.Spawn f ->
      let typ =
        templates
        |> List.filter_map (fun (h,typ) -> if same_top_fun f h then Some typ else None)
        |> _Inter (Id.typ f)
      in
      (f, typ)::templates
  | CT.Let(f, t) ->
      assert (is_fun_var f);
      templates
  | CT.Branch _ -> templates
  | CT.Assume _ -> templates
  | CT.End ->
      assert (children = []);
      []
  | CT.Fail ->
      assert (children = []);
      []

let rec make_arg_templates_aux typ =
  let aux = make_arg_templates_aux in
  match typ with
  | Base _
    | PApp _ -> []
  | Fun(x, typ1, typ2) -> (x,typ1) :: aux typ2
  | Inter(styp,typs) -> List.flatten_map aux typs
  | _ ->
      Format.eprintf "%a@." print_template typ;
      assert false

let make_arg_templates templates =
  let spawned (x,typ) =
    match decomp_id x with
    | _, Some _, [] -> Some typ
    | _ -> None
  in
  templates
  |> List.filter_map spawned
  |> List.flatten_map make_arg_templates_aux

let make_template env t =
  let is_top (x,_) =
    match decomp_id x with
    | _, _, [] -> true
    | _ -> false
  in
  let cnt = Counter.create() in
  let templates =
    make_template cnt [] t
    |> List.filter is_top
  in
  let templates_unused =
(*
    env
    |> List.filter_map (fun (f,_) -> if Id.mem_assoc f templates then None else Some (f, new_template_of_simple cnt @@ Id.typ f))
 *)
    []
  in
  templates_unused @ templates





let rec generate_constraints templates arg_templates assumption (Rose_tree.Node({CT.nid; var_env; val_env; ce_env; nlabel}, children)) =
  let dbg = 0=0 in
  if dbg then Debug.printf "label: %a@." CT.print_nlabel nlabel;
  if dbg then Debug.printf "  Dom(val_env): %a@." (List.print Id.print) @@ List.map fst val_env;
  let r =
  let constr tmp asm = List.flatten_map (generate_constraints templates tmp asm) children in
  let templates' =
    List.map (fun (y,(env,typ)) ->
        y,(*
        match typ with
        | Base _ | PApp _ ->
            List.fold_right (fun (x,v) typ -> subst_template x (CT.term_of_value v) typ) env typ
        | _ ->*) typ)
             arg_templates @ templates in
  match nlabel with
  | CT.App(f, map) ->
      if dbg then Debug.printf "  map: %a@." (List.print @@ Pair.print Id.print CT.print_value) map;
      let asm =
        Debug.printf "  templates': %a@." print_tmp_env templates';
        let asm1 = filter_assumption val_env assumption in
        let asm2 = make_assumption templates' val_env in
        if dbg then Debug.printf "  asm1: %a@." (List.print print_constr) asm1;
        if dbg then Debug.printf "  asm2: %a@." (List.print print_constr) asm2;
        asm1 @ asm2
      in
      let constr1 =
        let aux (env,acc) (_, CT.Closure(var_env,val_env,t)) =
          let constr =
            if is_base_typ t.typ then
              let typ1 = Singleton t in
              let typ2 =
                Arg(Var f, env)
                |*> List.fold_right (fun (y,v) typ -> subst_template y (CT.term_of_value v) typ) val_env
              in
              make_sub templates' val_env typ1 typ2
            else
              Exp true_term
          in
          if dbg then Debug.printf "    nid: %d@." nid;
          if dbg then Debug.printf "    constr: %a@." print_constr constr;
          let env' = env @ [t] in
          let acc' =
            if constr = Exp true_term then
              acc
            else
              _Imply asm constr :: acc
          in
          env', acc'
        in
        if dbg then Debug.printf "    map: %a@." (List.print @@ Pair.print Id.print CT.print_value) map;
        snd @@ List.fold_left aux ([],[]) map
      in
      if dbg then Debug.printf "  constr1: %a@." (List.print print_constr) constr1;
      if dbg then Debug.printf "@.";
      let arg_templates' =
        let arg_templates = make_arg_templates_aux @@ Id.assoc f templates' in
        Debug.printf "  ARG_TEMPLATE: %a@." print_tmp_env arg_templates;
        List.map (fun (x,typ) -> x, (map, typ)) arg_templates
      in
(*
      Debug.printf "  ARG_TEMPLATE': %a@." print_tmp_env arg_templates';
 *)
      constr1 @ constr (arg_templates'@arg_templates) assumption
  | CT.Spawn _ ->
      constr arg_templates assumption
  | CT.Let(f, t) ->
      constr arg_templates assumption
  | CT.Branch _ ->
      constr arg_templates assumption
  | CT.Assume t ->
      constr arg_templates @@ t::assumption
  | CT.End ->
      [Exp true_term]
  | CT.Fail ->
      assert (children = []);
      let asm1 = filter_assumption val_env assumption in
      let asm2 = make_assumption templates' val_env in
      let asm = asm1 @ asm2 in
      if dbg then Debug.printf "  FAIL: asm1: %a@." (List.print print_constr) asm1;
      if dbg then Debug.printf "  FAIL: asm2: %a@." (List.print print_constr) asm2;
      [_Imply asm @@ Exp false_term]
  in
  if dbg then Debug.printf "  label: %a@." CT.print_nlabel nlabel;
  if dbg then Debug.printf "  assumption: %a@." (List.print Print.term) assumption;
  if dbg then Debug.printf "  r: %a@.@." (List.print print_constr) r;
  r

let generate_constraints templates ct =
  generate_constraints templates [] [] ct





let rec to_horn_clause asm constr =
  match constr with
  | Exp t -> [asm, t]
  | And(c1, c2) -> to_horn_clause asm c1 @ to_horn_clause asm c2
  | Imply(Exp t, c2) -> to_horn_clause (asm@[t]) c2
  | _ -> assert false
let to_horn_clause constr = to_horn_clause [] constr

let check_arity hcs =
  let ts = List.flatten_map (fun {HC.head;HC.body} -> head::body) hcs in
  let aux env t =
    match t.desc with
    | App({desc=Var f}, ts) ->
        let n = List.length ts in
        begin
          try
            if Id.assoc f env <> List.length ts then
              (Format.eprintf "%a@." Id.print f; assert false);
            env
          with Not_found -> (f,n)::env
        end
    | _ -> env
  in
  ignore @@ List.fold_left aux [] ts


let rec pvars t =
  match t.desc with
  | App({desc=Var p}, _) -> [p]
  | BinOp(_, t1, t2) -> pvars t1 @ pvars t2
  | _ -> []

let print_solution fm (p,(xs,t)) =
  Format.fprintf fm "P_%d(%a) := %a" p (print_list Id.print ",") xs Print.term t

let solve hcs =
  let dbg = 0=1 in
  let vars =
    hcs
    |> List.flatten_map (fun {HC.body;HC.head} -> List.flatten_map pvars body @ pvars head)
    |> List.unique ~eq:Id.eq
    |@dbg&> Debug.printf "vars: %a@." (List.print Id.print)
  in
  let sol =
    let tr t =
      t
      |> FpatInterface.of_term
      |> Fpat.Formula.of_term
    in
    let tr' {HC.head;HC.body} =
      let hd,bd = tr head, List.map tr body in
      Fpat.Formula.fvs hd @@@ List.flatten_map Fpat.Formula.fvs bd, hd, bd
    in
    hcs
    |> List.map tr'
    |> List.map (Triple.uncurry Fpat.HornClause.of_formulas)
    |> Fpat.HCCSSolver.solve_dyn
    |> Fpat.PredSubst.normalize
  in
  Debug.printf "SOLUTION: %a@." Fpat.PredSubst.pr sol;
  let sol' =
    let tr_typ typ =
      let base =
        match typ with
        | _ when typ = Fpat.Type.mk_int -> Type.TInt
        | _ when typ = Fpat.Type.mk_bool -> Type.TBool
        | _ when typ = Fpat.Type.mk_unit -> Type.TUnit
        | _ ->
            Format.eprintf "%a@." Fpat.Type.pr typ;
            assert false
      in
      TBase base
    in
    let aux p =
      Debug.printf "p: %a@." Print.id_typ p;
      let var_of_env (x,typ) = Id.from_string (Fpat.Idnt.string_of x) (tr_typ typ) in
      let sbst xtyp y = subst_var (var_of_env xtyp) y in
      let sol' = List.assoc_all (Fpat.Idnt.make @@ Id.to_string ~plain:false p) sol in
      match sol' with
      | [] -> fst @@ Type.decomp_tfun @@ Id.typ p, false_term
      | (env,_)::_ ->
          let xs = List.map var_of_env env in
          let tr = CEGAR_trans.trans_inv_term -| FpatInterface.inv_term -| Fpat.Formula.term_of  in
          xs, make_ors @@ List.map (fun (tenv,phi) -> List.fold_right2 sbst tenv xs @@ tr phi) sol'
    in
    List.map (Pair.make Id.id aux) vars
  in
  Debug.printf "SOLUTION: %a@." (List.print print_solution) sol';
  sol'
let solve_option hcs =
  try Some (solve hcs) with
  | Fpat.HCCSSolver.Unknown
  | Fpat.HCCSSolver.NoSolution -> None

let any_var = Id.make (-1) "any" [] Ty.bool

let rec apply_sol mode sol x vars tmp =
  let dbg = 0=0 in
  let r =
  match tmp with
  | Base(Some _)
  | PApp(Base (Some _), _) ->
      if x = None then
        Ref_type.Base(TUnit, Id.new_var Ty.unit, true_term)
      else
        let base,p,ts =
          match tmp with
          | Base(Some(base,p)) -> base, p, []
          | PApp(Base (Some (base,p)), ts) -> base, p, [](*ts*)
          | _ -> assert false
        in
        if dbg then Debug.printf "  P_%d@." p;
        if dbg then Debug.printf "  tmp: %a@." print_template tmp;
        if dbg then Debug.printf "  Dom(sol): %a@." (List.print Format.pp_print_int) @@ List.map fst sol;
        if dbg then Debug.printf "  vars: %a@." (List.print Id.print) vars;
        let x' = Option.get x in
        let p =
          let vars' = List.filter is_base_var vars in
          let ts' = make_var x' :: List.map make_var vars' @ ts in
          try
            let xs,t = List.assoc p sol in
            if dbg then Debug.printf "  t: %a@." Print.term t;
            if dbg then Debug.printf "  xs: %a@." (List.print Id.print) xs;
            if dbg then Debug.printf "  ts': %a@." (List.print Print.term) ts';
            List.fold_right2 subst xs ts' t
          with Not_found -> make_var any_var
        in
        Ref_type.Base(base, x', p)
  | Base None -> Ref_type.Base(TUnit, Id.new_var Ty.unit, true_term)
  | Fun(y,typ1,typ2) ->
      Ref_type.Fun(y, apply_sol mode sol (Some y) vars typ1, apply_sol mode sol None (y::vars) typ2)
  | Inter(styp, []) ->
      Ref_type.inter styp []
  | Inter(styp, tmps) -> Ref_type.Inter(styp, List.map (apply_sol mode sol x vars) tmps)
  | _ ->
      Format.eprintf "%a@." print_template tmp;
      assert false
  in
  if dbg then Debug.printf "[AS] tmp: %a@." print_template tmp;
  if dbg then Debug.printf "[AS] r: %a@." Ref_type.print r;
  r
let apply_sol mode sol tmp = apply_sol mode sol None [] tmp



let lift_arg =
  let tr = make_trans () in
  let tr_desc desc =
    match tr.tr_desc_rec desc with
    | App(t1,ts) ->
        let bindings,ts' =
          let aux t =
            match t.desc with
            | Fun _ ->
                let x = new_var_of_term t in
                [x,t], make_var x
            | Local(Decl_let bindings, t') ->
                bindings, t'
            | _ -> [], t
          in
          ts
          |> List.map aux
          |> List.split
        in
        let bindings' = List.flatten bindings in
        (make_lets bindings' (make_app t1 ts')).desc
    | desc' -> desc'
  in
  tr.tr_desc <- tr_desc;
  tr.tr_term



let rec normalize t =
  t
  |> Trans.eta_normal
  |> lift_arg
  |> Trans.reconstruct
  |*> Trans.alpha_rename ~whole:true


let trans_CPS env funs t =
  let t',make_get_rtyp_cps =
    t
    |> List.fold_right (fun (f,t1) t -> add_attr ADoNotInline @@ make_let [f, t1] t) env
    |@> Debug.printf "trans_CPS: %a@." Print.term_typ
    |> CPS.trans_as_direct
  in
  Debug.printf "trans_CPS t': %a@." Print.term t';
  Type_check.check t';
  let t'',make_get_rtyp_pair = Curry.remove_pair_direct t' in
  Debug.printf "trans_CPS t'': %a@." Print.term t'';
  let env',t_main =
    t''
    |@> Debug.printf "trans_CPS INPUT: %a@." Print.term
    |> Trans.reduce_fail_unit
    |@> Debug.printf "trans_CPS reduce_fail_unit: %a@." Print.term
    |> normalize
    |@> Debug.printf "trans_CPS normalized: %a@." Print.term
    |> decomp_prog
  in
  let make_get_rtyp = make_get_rtyp_cps -| make_get_rtyp_pair in
  let env1,env2 =
    env'
    |> List.flatten
    |> List.partition (fst |- Id.mem_assoc -$- env)
  in
  Debug.printf "funs: %a@." (List.print Id.print) funs;
  if false then
    (Debug.printf "env1: %a@." (List.print @@ Pair.print Id.print @@ Print.term) env1;
     Debug.printf "env2: %a@." (List.print @@ Pair.print Id.print @@ Print.term) env2)
  else
    (Debug.printf "Dom(env1): %a@." (List.print Id.print) @@ List.map fst env1;
     Debug.printf "Dom(env2): %a@." (List.print Id.print) @@ List.map fst env2);
  if not @@ List.for_all (Id.mem_assoc -$- env1) funs then
    begin
      let removed = List.filter_out (Id.mem_assoc -$- env1) funs in
      Format.eprintf "REMOVED: %a@." (List.print Id.print) removed;
      assert false
    end;
  env1, make_lets env2 t_main, make_get_rtyp


let add_context for_infer prog f typ =
  let dbg = 0=0 in
  if dbg then Debug.printf "ADD_CONTEXT: %a :? %a@." Print.id f Ref_type.print typ;
  let t' =
    let af = "Assert_failure" in
    let etyp = TVariant(false, prog.exn_decl@[af,[]]) in
    let typ_exn = Encode.typ_of Encode.all etyp in
    let make_fail typ =
      make_raise (make_construct af [] etyp) typ
      |> Problem.safety
      |> Encode.all
      |> Problem.term
    in
    Trans.ref_to_assert ~make_fail ~typ_exn (Ref_type.Env.of_list [f,typ]) end_of_definitions
  in
  if dbg then Debug.printf "ADD_CONTEXT t': %a@." Print.term_typ t';
  let env = prog.fun_def_env in
  let funs =
    env
    |> List.map fst
    |> List.takewhile (not -| Id.same f)
  in
  trans_CPS env funs t'

module Dependency =
  Set.Make(
    struct
      type t = int * int
      let compare = compare
    end)

let add_dependency deps (x,y) =
  if 0=1 then Debug.printf "ADD_DEP: %d -> %d@." x y;
  let deps' = Dependency.elements deps in
  let from_y = y :: List.filter_map (fun (z,w) -> if y = z then Some w else None) deps' in
  let to_x   = x :: List.filter_map (fun (z,w) -> if x = w then Some z else None) deps' in
  let new_dep = Dependency.of_list @@ List.map Pair.of_list @@ Combination.take_each [to_x; from_y] in
  Dependency.union new_dep deps

let get_dependencies hcs =
  let dbg = 0=1 in
  let aux acc {HC.body;HC.head} =
    if dbg then Debug.printf "  HC: %a@." HC.print {HC.body;HC.head};
    if dbg then Debug.printf "  deps_cls: %a@." (List.print @@ Pair.print Format.pp_print_int Format.pp_print_int) @@ Dependency.elements acc;
    let fv1 = List.filter_map HC.get_pred_id_of_term body in
    let fv2 = Option.to_list @@ HC.get_pred_id_of_term head in
    let new_dep = List.flatten_map (fun x -> List.map (Pair.pair x) fv2) fv1 in
    List.fold_left add_dependency acc new_dep
  in
  List.fold_left aux Dependency.empty hcs

let transitive_closure deps =
  List.fold_left add_dependency Dependency.empty deps

let save_dep deps_cls hcs filename =
  let dbg = 0=1 in
  let aux acc {HC.body;HC.head} =
    let fv1 = List.filter_map HC.get_pred_id_of_term body in
    let fv2 = Option.to_list @@ HC.get_pred_id_of_term head in
    let new_dep = List.flatten_map (fun x -> List.map (Pair.pair x) fv2) fv1 in
    let aux' acc (x,y) = new_dep @@@ acc in
    List.fold_left aux' acc new_dep
  in
  let deps = List.unique @@ List.fold_left aux [] hcs in
  let deps_cls' = transitive_closure deps in
  Format.printf "Save %s@." filename;
  Graph.(save_as_dot filename @@ from_edges deps);
  if dbg then Debug.printf "deps_cls: %a@." (List.print @@ Pair.print Format.pp_print_int Format.pp_print_int) @@ Dependency.elements deps_cls;
  if dbg then Debug.printf "deps_cls': %a@." (List.print @@ Pair.print Format.pp_print_int Format.pp_print_int) @@ Dependency.elements deps_cls';
  if dbg then Debug.printf "deps_cls'\\deps_cls: %a@." (List.print @@ Pair.print Format.pp_print_int Format.pp_print_int) @@ Dependency.elements @@ Dependency.diff deps_cls' deps_cls;
  assert (Dependency.subset deps_cls' deps_cls)


let merge_predicate_variables  hcs =
  let dependencies = get_dependencies hcs in
  dependencies

let subst_horn_clause x t (body,head) =
  List.map (subst x t) body, subst x t head


let replace_id p1 p2 t =
  match t.desc with
  | App({desc=Var x}, ts) when HC.get_pred_id x = p1 ->
      assert (HC.is_pred_var x);
      make_app (make_var @@ Id.set_id x p2) ts
  | _ -> t


let cnt = ref 0

let same_last_sol last_sol p1 p2 =
  try
    let xs1,t1 = List.assoc p1 last_sol in
    let xs2,t2 = List.assoc p2 last_sol in
    t2 = List.fold_right2 subst_var xs1 xs2 t1
  with Not_found -> false

let add_merged (p1,p2) merged =
  if List.mem_assoc p1 merged then
    (p2, List.assoc p1 merged)::merged
  else if List.mem_assoc p2 merged then
    (p1, List.assoc p2 merged)::merged
  else
    (p1,p2)::merged

let can_merge (p1,p2) deps =
  not @@ Dependency.mem (p1,p2) deps &&
  not @@ Dependency.mem (p2,p1) deps

let merge_same_sol sol map merged deps hcs =
  let rec loop acc sol map merged deps hcs =
    match map with
    | [] -> acc, merged, deps, hcs
    | (p1,p2)::map' when can_merge (p1,p2) deps ->
        let merged' = add_merged (p1,p2) merged in
        let hcs' = List.map (Horn_clause.map @@ replace_id p1 p2) hcs in
        let deps' = add_dependency (add_dependency deps (p1,p2)) (p2,p1) in
        loop acc sol map' merged' deps' hcs'
    | pp::map' -> loop (pp::acc) sol map' merged deps hcs
  in
  loop [] sol map merged deps hcs

let solve_merged map hcs =
  let dependencies = get_dependencies hcs in
  let sbst (p1,p2) map =
    let aux p = if p = p1 then p2 else p in
    List.map (Pair.map aux aux) map
  in
  let rec loop used last_sol merged deps map hcs =
    Debug.printf "merged: %a@." (List.print @@ Pair.print Format.pp_print_int Format.pp_print_int) merged;
    match map with
    | [] -> last_sol, merged
    | (p1,p2)::map' when p1 = p2 ->
        Debug.printf "MERGED %d@." p1;
        loop used last_sol merged deps map' hcs
    | (p1,p2)::map' when Dependency.mem (p1,p2) deps || Dependency.mem (p2,p1) deps ->
        Debug.printf "NOT MERGE %d, %d@." p1 p2;
        loop used last_sol merged deps map' hcs
    | (p1,p2)::map' when not (List.mem p1 used && List.mem p2 used) ->
        Debug.printf "MERGE1 %d, %d@." p1 p2;
        let merged' = add_merged (p1,p2) merged in
        let map'' = sbst (p1,p2) map' in
        loop used last_sol merged' deps map'' hcs
    | (p1,p2)::map' ->
        let hcs' = List.map (Horn_clause.map @@ replace_id p1 p2) hcs in
        incr cnt;
        match solve_option hcs' with
        | exception e ->
            Debug.printf "DEPS: %a@." (List.print @@ Pair.print Format.pp_print_int Format.pp_print_int) @@ Dependency.elements deps;
            raise e
        | None ->
            Debug.printf "CANNOT MERGE %d, %d@." p1 p2;
            loop used last_sol merged deps map' hcs
        | Some sol ->
            Debug.printf "MERGE3 %d, %d@." p1 p2;
            let merged' = add_merged (p1,p2) merged in
            let map'' = sbst (p1,p2) map' in
            let deps' = add_dependency (add_dependency deps (p1,p2)) (p2,p1) in
            if 0=1 && !!Debug.check then save_dep deps' hcs' @@ Format.sprintf "tmp/test%d.dot" !cnt;
            Debug.printf "SOLVED@.";
            let map''',merged'',deps'',hcs'' = merge_same_sol sol map'' merged' deps' hcs' in
            let used' = List.remove used p1 in
            loop used' sol merged'' deps'' map''' hcs''
  in
  if 0=1 then Debug.printf "init_deps: %a@." (List.print @@ Pair.print Format.pp_print_int Format.pp_print_int) @@ Dependency.elements dependencies;
  if 0=1 && !!Debug.check then save_dep dependencies hcs "tmp/test.dot";
  match solve_option hcs with
  | None -> None
  | Some sol ->
      let map = [] in
      let used = HC.get_pred_ids_hcs hcs in
      let map',merged,deps',hcs' = merge_same_sol sol map [] dependencies hcs in
      let sol',merged' = loop used sol merged deps' map' hcs' in
      Debug.printf "map: %a@." (List.print @@ Pair.print Format.pp_print_int Format.pp_print_int) map;
      Debug.printf "merged': %a@." (List.print @@ Pair.print Format.pp_print_int Format.pp_print_int) merged';
      Debug.printf "Dom(sol'): %a@." (List.print Format.pp_print_int) @@ List.map fst sol';
      let aux (x,y) =
        try
          Some (x, List.assoc y sol')
        with Not_found -> None
      in
      Some (List.filter_map aux merged' @ sol')

let assoc_pred_var p hcs =
  if 0=1 then Format.printf "APV: P_%d@." p;
  let rec find hcs =
    match hcs with
    | [] -> HC.make_pred_var p []
    | (body,head)::hcs' ->
        match List.find_option (fun x -> HC.is_pred_var x && Id.id x = p) @@ get_fv @@ make_ands (head::body) with
        | None -> find hcs'
        | Some x -> x
  in
  find hcs

let rec get_pred_ids tmp =
  match tmp with
  | Var _ -> []
  | Arg(tmp', _) -> get_pred_ids tmp'
  | PApp(tmp', _) -> get_pred_ids tmp'
  | Singleton _ -> []
  | Base None -> []
  | Base(Some(_,p)) -> [p]
  | Const _ -> []
  | Fun(_, tmp1, tmp2) -> get_pred_ids tmp1 @ get_pred_ids tmp2
  | Inter(_, tmps) -> List.flatten_map get_pred_ids tmps

let rec get_merge_candidates_aux typ1 typ2 =
  match typ1, typ2 with
  | Base None, Base _ -> []
  | Base _, Base None -> []
  | Base (Some(_, p1)), Base (Some(_, p2)) -> [p1, p2]
  | PApp(typ1', _), _ -> get_merge_candidates_aux typ1' typ2
  | _, PApp(typ2', _) -> get_merge_candidates_aux typ1 typ2'
  | Fun(_, typ11, typ12), Fun(_, typ21, typ22) -> get_merge_candidates_aux typ11 typ21 @ get_merge_candidates_aux typ12 typ22
  | Inter(_, typs), _ -> List.flatten_map (get_merge_candidates_aux typ2) typs
  | _, Inter(_, typs) -> List.flatten_map (get_merge_candidates_aux typ1) typs
  | _ ->
      Format.eprintf "get_merge_candidates_aux typ1: %a@." print_template typ1;
      Format.eprintf "get_merge_candidates_aux typ2: %a@." print_template typ2;
      assert false

let get_merge_candidates templates =
  let aux typs =
    match typs with
    | []
    | [_] -> []
    | typ::typs' ->
        if 0=0 then Debug.printf "GMC typs: %a@." (List.print print_template) typs;
        List.flatten_map (get_merge_candidates_aux @@ typ) @@ typs'
  in
  templates
  |> List.classify ~eq:(Compare.eq_on ~eq:Id.eq fst)
  |> List.map (List.flatten_map (snd |- decomp_inter))
  |> List.flatten_map aux


let map_with_replacing_tuples f t =
  let rec aux map t =
    match t.desc with
    | Const _ -> map, t
    | Var x -> map, t
    | Proj(i, {desc=Var x}) ->
        if List.exists (snd |- same_term t) map then
          map, make_var @@ fst @@ List.find (snd |- same_term t) map
        else
          let x' = Id.new_var t.typ in
          [x', t], make_var x'
    | Not t ->
        let map',t' = aux map t in
        map', make_not t'
    | BinOp(op, t1, t2) ->
        let map1,t1' = aux map t1 in
        let map2,t2' = aux map1 t2 in
        map2, {t with desc=BinOp(op,t1',t2')}
    | _ -> unsupported "map_with_replacing_tuples"
  in
  let map,t' = aux [] t in
  let t'' = f t' in
  subst_map map t''


let widen t =
  if get_fv t = [] then
    t
  else
    let () = Debug.printf "widen INPUT: %a@." Print.term t in
    let aux =
      FpatInterface.of_term
      |- Fpat.Formula.of_term
      |- Fpat.Polyhedron.convex_hull_dyn
      |- Fpat.Formula.term_of
      |- FpatInterface.inv_term
      |- CEGAR_trans.trans_inv_term
    in
    map_with_replacing_tuples aux t
    |@> Debug.printf "widen OUTPUT: %a@." Print.term


let rec instantiate_any mode pos typ =
  let open Ref_type in
  match typ with
  | Base(base,y,p) ->
      let p' =
        let t =
          match mode with
          | ToTrue -> true_term
          | ToFalse -> false_term
          | ToNatural -> true_term
          | ToStronger -> make_bool (not pos)
        in
        Term_util.subst any_var t p
      in
      Base(base, y, p')
  | ADT(_,_,_) -> assert false
  | Fun(y,typ1,typ2) -> Fun(y, instantiate_any mode (not pos) typ1, instantiate_any mode pos typ2)
  | Tuple xtyps -> Tuple (List.map (Pair.map_snd @@ instantiate_any mode pos) xtyps)
  | Inter(typ, typs) -> Inter(typ, List.map (instantiate_any mode pos) typs)
  | Union(typ, typs) -> Union(typ, List.map (instantiate_any mode pos) typs)
  | ExtArg(y,typ1,typ2) -> unsupported "instantiate_any"
  | List(y,p_len,z,p_i,typ) -> unsupported "instantiate_any"
  | App _ -> unsupported "instantiate_any"
  | Exn(typ1, typ2) ->
      let mode' =
        if mode = ToNatural then
          ToStronger
        else
          mode
      in
      Exn(instantiate_any mode pos typ1, instantiate_any mode' pos typ2)

let infer prog f typ (ce_set:ce_set) depth merge =
  let ce_set =
    if 0=1 then
      List.filter (fun (x,ce) -> Format.printf "%a, %a@.?: @?" Id.print x print_ce ce; read_int() <> 0) ce_set
    else
      ce_set
  in
  let {fun_typ_env=env; fun_def_env=fun_env} = prog in
  Debug.printf "INFER prog: %a@." print_prog prog;
  let fun_env',t,make_get_rtyp = add_context true prog f typ in
  Debug.printf "add_context t: %a@.@." Print.term t;
  let comp_tree =
    Debug.printf "Dom(Fun_env'): %a@.@." (List.print Id.print) @@ List.map fst fun_env';
    Debug.printf "t with def: %a@.@." Print.term @@ make_lets fun_env' t;
    Debug.printf "t: %a@.@." Print.term t;
    CT.from_program fun_env' ce_set depth t
  in
  let templates = make_template fun_env' comp_tree in
  Debug.printf "TEMPLATES: @[%a@.@." print_tmp_env templates;
(*
  let arg_templates = make_arg_templates templates in
  Debug.printf "ARG_TEMPLATES: @[%a@.@." print_tmp_env arg_templates;
 *)
  let constrs = generate_constraints templates comp_tree in
  Debug.printf "CONSTR: @[%a@.@." (List.print print_constr) constrs;
  let need = List.flatten_map (fun (f,tmp) -> if Id.mem_assoc f fun_env' then get_pred_ids tmp else []) templates in
  Debug.printf "NEED: @[%a@.@." (List.print Format.pp_print_int) need;
  let hcs =
    constrs
    |> List.flatten_map to_horn_clause
    |> List.map @@ Pair.map (List.map Trans.init_base_rand) Trans.init_base_rand
    |> HC.of_pair_list
    |@> Debug.printf "HORN CLAUSES:@.@[%a@.@." HC.print_horn_clauses
    |@!!Debug.check&> check_arity
    |*> HC.inline need
    |*@> Debug.printf "INLINED HORN CLAUSES:@.@[%a@.@." HC.print_horn_clauses
  in
  let merge_candidates =
    if merge then
      templates
      |> List.filter_out (Id.is_external -| fst)
      |> get_merge_candidates
    else
      []
  in
  match solve_merged merge_candidates hcs with
  | None -> fun _ -> None
  | Some sol ->
      Debug.printf "TEMPLATES of TOP_FUNS: @[%a@.@." print_tmp_env @@ List.filter (fun (f,_) -> Id.mem_assoc f fun_env') templates;
      Debug.printf "  Dom(sol): %a@." (List.print Format.pp_print_int) @@ List.map fst sol;
      let top_funs =
        prog.fun_def_env
        |> List.map fst
        |> List.filter (Id.mem_assoc -$- fun_env')
        |> List.filter_out (Id.same f)
      in
      Debug.printf "TOP_FUNS[%a]: %a@.@." Id.print f (List.print Id.print) top_funs;
      fun mode ->
      let env' =
        let aux (g,tmp) =
          if Id.mem g top_funs then
            Some (g, apply_sol mode sol tmp)
          else
            None
        in
        List.filter_map aux templates
      in
      let env'' =
        let aux (x,typ') =
          let typ = Ref_type.Env.assoc x prog.fun_typ_env in
          let x',_ = Ref_type.Env.find (fst |- Id.same x) env in
          Debug.printf "  %a: %a@." Id.print x' Ref_type.print typ';
          let typ_ =
            Debug.printf "  typ: %a@." Ref_type.print typ;
            Debug.printf "  typ': %a@." Ref_type.print typ';
            make_get_rtyp (fun y -> assert Id.(y = x); typ') x
            |@> Debug.printf "  rtyp: %a@." Ref_type.print
            |> instantiate_any mode true
            |@> Debug.printf "  [%a] typ_: %a@." print_mode mode Ref_type.print
          in
          x', typ_
        in
        env'
        |> List.map aux
        |> List.map (Pair.map_snd Ref_type.contract)
        |> List.flatten_map (fun (x,typ) -> List.map (fun typ -> x, typ) @@ Ref_type.decomp_inter typ)
        |> List.remove_lower (fun (x,typ) (x',typ') -> Id.(x = x') && Ref_type.equiv typ typ')
        |> List.filter_out (fun (g,typ') -> Id.(f = g) && Ref_type.subtype typ typ')
        |> Ref_type.Env.of_list
      in
      let env'' =
        if true then
          env''
        else
          let env'' = Ref_type.Env.to_list env'' in
          let env'' = env'' @ List.map (Pair.map_snd @@ Ref_type.map_pred widen) env'' in
          let env'' = List.flatten_map (fun (x,typ) -> List.map (fun typ' -> x, typ') @@ Ref_type.split_inter typ) env'' in
          Ref_type.Env.of_list env''
      in
      let env_unused =
        let aux f =
          if Id.mem_assoc f env' then
            None
          else
            match mode with
            | ToTrue
            | ToNatural -> Some (f, Ref_type.of_simple @@ Id.typ f)
            | _ -> Some (f, Ref_type.make_strongest @@ Id.typ f)
        in
        env
        |> Ref_type.Env.dom
        |> List.takewhile (not -| Id.same f)
        |> List.filter_map aux
        |> Ref_type.Env.of_list
      in
      Debug.printf "env_unused: %a@.@." Ref_type.Env.print env_unused;
      Debug.printf "env'': %a@.@." Ref_type.Env.print env'';
      let env''' = Ref_type.Env.merge env_unused env'' in
      Debug.printf "Modular_infer.infer: %a@.@." Ref_type.Env.print env''';
      Some env'''

let modes = [ToNatural; ToTrue; ToStronger; ToFalse]

let next_mode mode =
  let rec aux mds =
    match mds with
    | []
    | [_] -> None
    | m1::m2::_ when m1 = mode -> Some m2
    | _::mds' -> aux mds'
  in
  Option.get @@ aux modes

let init_mode = List.hd modes

let is_last_mode mode =
  try
    ignore @@ next_mode mode;
    false
  with Option.No_value -> true
