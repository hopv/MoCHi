open Util
open Type

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)
module Dbg_share = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__^".share") end)

let print_as_ocaml = ref false
let set_print_as_ocaml () = print_as_ocaml := true
let tmp_set_print_as_ocaml f = Ref.tmp_set print_as_ocaml true f

type 'a config =
  {occur : 'a tid -> 'a t -> bool;             (** occur checker *)
   print_pred : Format.formatter -> 'a -> unit; (** printer for terms *)
   depth : int;                                 (** max length of printing terms *)
   length : int}                                (** max depth of printing terms *)

let rec decomp_tfun typ =
  match typ with
  | TFun(x,typ) ->
      let xs,typ = decomp_tfun typ in
      x :: xs, typ
  | _ -> [], typ

let init_print_length = ref (-1)
let init_print_depth = ref (-1)
let set_print_length l = init_print_length := l
let set_print_depth d = init_print_depth := d

let init_config () =
  let occur _ _ = false in
  let print_pred _ _ = assert false in
  let length = !init_print_length in
  let depth = !init_print_depth in
  {occur; print_pred; length; depth}

let remove_some_attr ty =
  match ty with
  | TAttr(attrs, ty) ->
    let attrs' =
      if !!Dbg_share.check then
        attrs
      else
        List.filter (function TAPredShare _ | TAId _ -> false | _ -> true) attrs
    in
    TAttr(attrs', ty)
  | _ -> ty



let print_effect fm e =
  match e with
  | EVar n -> Format.fprintf fm "'e%d" n
  | EEvent -> Format.fprintf fm "event"
  | EDiv -> Format.fprintf fm "div"
  | ENonDet -> Format.fprintf fm "nondet"
  | EExcep -> Format.fprintf fm "excep"

let rec print_attr cfg fm a =
  match a with
  | TAPred _ -> Format.fprintf fm "TAPred"
  | TARefPred _ -> Format.fprintf fm "TARefPred"
  | TAPureFun -> Format.fprintf fm "TAPureFun"
  | TAEffect e -> Format.fprintf fm "TAEffect %a" (List.print print_effect) e
  | TAPredShare x -> Format.fprintf fm "TAPredShare %d" x
  | TAId(s,x) -> Format.fprintf fm "TAId(%s,%d)" s x
  | TARaise ty -> Format.fprintf fm "TARaise %a" (print cfg) ty

and print_tvar ?(weak=false) fm n =
  if n < 0 then
    Format.fprintf fm "'_for_debug"
  else
    let c = char_of_int @@ int_of_char 'a' + n mod 26 in
    let d = if n < 26 then "" else string_of_int (n/26) in
    Format.fprintf fm "'%s%c%s" (if weak then "_" else "") c d

and print_label = Id.print
and print_constr = Id.print
and print_tconstr = Id.print
and print_path = Path.print

and print_base fm b =
  match b with
  | TUnit -> Format.fprintf fm "unit"
  | TBool -> Format.fprintf fm "bool"
  | TInt -> Format.fprintf fm "int"

and print_params cfg fm params =
  let pr = print cfg in
  match params with
  | [] -> ()
  | [ty] -> Format.fprintf fm "%a " pr ty
  | _ -> Format.fprintf fm "(%a) " (print_list pr ",") params

and print_decl_item cfg ~first ~last fm (c,(params,ty)) =
  let header = if first then "type" else "and" in
  Format.fprintf fm "@[<hov 2>%s %a%a = %a@]"
    header
    (print_params cfg) params
    print_constr c
    (print cfg) ty
    [@@ocaml.warning "-27"]

and print_declaration ?(need_new_line=true) cfg fm decls =
  let pr ~first ~last fm decl : unit =
    print_list_with_flag (print_decl_item cfg) "@\n" fm decl
      [@@ocaml.warning "-27"]
  in
  Format.pp_open_hbox fm ();
  print_list_with_flag pr "@\n" ~last:need_new_line fm decls;
  Format.pp_close_box fm ()

and print_ext cfg fm (tc, (params, row)) =
  if C.is_exn tc then
    Format.fprintf fm "@[<hov 2>exception"
  else
    Format.fprintf fm "@[<hov 2>type %a%a +=" (print_params cfg) params print_path tc;
  let row =
    {row_constr = Id.make (Path.to_string @@ row.ext_row_path) ();
     row_args = row.ext_row_args;
     row_ret = row.ext_row_ret}
  in
  Format.fprintf fm " %a@]" (print cfg) (TVariant(VNonPoly,[row]))

and print_ext_list cfg ?(has_cont=false) fm ext =
  print_list (print_ext cfg) ~last:has_cont "@\n" fm ext

and print_signature cfg fm ({sig_types; sig_values; sig_ext} as sgn) =
  if sgn = empty_signature then
    Format.fprintf fm "sig end"
  else if !Flag.Print.signature then
    let pr = print cfg in
    let pr_decls has_cont fm decls = print_declaration ~need_new_line:has_cont cfg fm decls in
    let pr_vals =
      let pr_val fm x = Format.fprintf fm "@[<hov 2>val %a : %a@]" Id.print x pr (Id.typ x) in
      print_list pr_val "@\n"
    in
    Format.fprintf fm "(@[sig@[<hv -1>@ %a%a%a@]@ end@])"
      (pr_decls (sig_ext <> [] || sig_values <> [])) sig_types
      (print_ext_list cfg ~has_cont:(sig_values <> [])) sig_ext
      pr_vals sig_values
  else
    Format.fprintf fm "sig...end"

and print_row cfg poly fm {row_constr; row_args; row_ret} =
  match row_ret with
  | None ->
      let s = if poly then "`" else "" in
      if row_args = [] then
        Format.fprintf fm "%s%a" s print_constr row_constr
      else
        Format.fprintf fm "@[%s%a of %a@]" s print_constr row_constr (print_list (print cfg) "@ *@ ") row_args
  | Some ty ->
      if row_args = [] then
        Format.fprintf fm "%a : %a" print_constr row_constr (print cfg) ty
      else
        Format.fprintf fm "@[%a : %a@]" print_constr row_constr (print_list (print cfg) "@ ->@ ") (row_args@[ty])


and print cfg fm typ =
  let print' = print cfg in
  let print_preds ps = print_list cfg.print_pred "; " ps in
  let print_list = print_list ~limit:cfg.length in
  match remove_some_attr typ with
  | TBase b -> print_base fm b
  | TVar(_,{contents=Some typ},_) -> print' fm typ
  | TVar(weak,{contents=None}, n) -> print_tvar ~weak fm n
  | TFun _ ->
      let rec aux fm (xs, typ) =
        match xs with
        | [] ->
            print' fm typ
        | x::xs' ->
            if List.exists (cfg.occur x) (typ :: List.map Id.typ xs) || (is_mod_typ @@ Id.typ x)
            then Format.fprintf fm "@[<hov 2>%a:%a ->@ %a@]" Id.print x print' (Id.typ x) aux (xs',typ)
            else Format.fprintf fm "@[<hov 2>%a ->@ %a@]" print' (Id.typ x) aux (xs',typ)
      in
      Format.fprintf fm "(%a)" aux @@ decomp_tfun typ
  | TFuns(xs,typ) ->
      let rec aux fm (xs, typ) =
        match xs with
        | [] -> Format.fprintf fm "[%a]" print' typ
        | x::xs' ->
            if List.exists (cfg.occur x) (typ :: List.map Id.typ xs)
            then Format.fprintf fm "@[<hov 2>%a:%a ->@ %a@]" Id.print x print' (Id.typ x) aux (xs',typ)
            else Format.fprintf fm "@[<hov 2>%a ->@ %a@]" print' (Id.typ x) aux (xs',typ)
      in
      Format.fprintf fm "(%a)" aux (xs, typ)
  | TTuple [] ->
      Format.fprintf fm "()"
  | TTuple [x] ->
      Format.fprintf fm "(@[<hov 2>%a * @])" print' (Id.typ x)
  | TTuple xs ->
      let pr fm x =
        if cfg.occur x typ then Format.fprintf fm "%a:" Id.print x;
        print' fm @@ Id.typ x
      in
      Format.fprintf fm "(@[<hov 2>%a@])" (print_list pr " *@ ") xs
  | TAttr(_, ty) when !print_as_ocaml -> print' fm ty
  | TAttr([], typ) -> print' fm typ
  | TAttr(TAPred(x,ps)::preds, typ) when not !!Dbg.check ->
      Format.fprintf fm "@[%a@[<hov 3>[\\%a. %a]@]@]" print' (TAttr(preds,typ)) Id.print x print_preds ps
  | TAttr([TAPureFun], (TFun(x,typ))) when not !!Dbg.check ->
      let pr_arg fm x = if cfg.occur x typ then Format.fprintf fm "%a:" Id.print x in
      Format.fprintf fm "(@[<hov 2>%a%a -*>@ %a@])" pr_arg x print' (Id.typ x) print' typ
  | TAttr(TAPureFun::attrs, ty) when not !!Dbg.check ->
      print' fm (TAttr(attrs@[TAPureFun],ty))
  | TAttr(TAEffect e::attrs, typ) when not !!Dbg.check ->
      let ty = TAttr(attrs,typ) in
      Format.fprintf fm "(@[%a # %a@])" print' ty (List.print print_effect) e
  | TAttr(TARefPred(x,p)::attrs, ty) ->
      let ty' = TAttr(attrs,ty) in
      Format.fprintf fm "@[{%a:%a|%a}@]" Id.print x print' ty' cfg.print_pred p
  | TAttr(TAId(_,x)::attrs, ty) when not !!Dbg.check ->
      let ty' = TAttr(attrs,ty) in
      let s1,s2 =
        match ty with
        | TFun _ -> "(", ")"
        | _ -> "", ""
      in
      Format.fprintf fm "@[%s%a%s^%d@]" s1 print' ty' s2 x
  | TAttr(attrs, ty) ->
      Format.fprintf fm "(%a @@ %a)" print' ty (List.print (print_attr cfg)) attrs
  | TVariant(_, []) ->
      Format.fprintf fm "(|)"
  | TVariant(VNonPoly, rows) ->
      let s1,s2 = if List.length rows > 1 then "(",")" else "","" in
      Format.fprintf fm "%s@[%a@]%s" s1 (print_list (print_row cfg false) "@ | ") rows s2
  | TVariant(VPoly{closed; tvar; lower}, labels) ->
      let s =
        if not closed then
          ">"
        else if lower = None then
          ""
        else
          "<"
      in
      let pr_lower fm =
        if not closed then
          ()
        else
          match lower with
          | None | Some [] -> ()
          | Some lower ->
              let pr fm c = Format.fprintf fm "`%a" print_constr c in
              Format.fprintf fm "@ > %a" (print_list pr "@ ") lower
      in
      let pr_tvar fm =
        match tvar with
        | None -> ()
        | Some _ -> Format.fprintf fm " as _"
      in
      Format.fprintf fm "[%s @[%a%t@]%t ]" s (print_list (print_row cfg true) "@ | ") labels pr_lower pr_tvar
  | TRecord fields ->
      let pr fm (l, (f, typ)) =
        let flag = if f = Mutable then "mutable " else "" in
        Format.fprintf fm "@[%s%a: %a@]" flag print_label l print' typ
      in
      Format.fprintf fm "{@[%a@]}" (print_list pr ";@ ") fields
  | TModSig sgn -> Format.fprintf fm "@[%a@]" (print_signature cfg) sgn
  | TModLid x -> Format.fprintf fm "@[(module type of %a)@]" Path.print x
  | TConstr(c, []) -> Format.fprintf fm "%a" Path.print c
  | TConstr(c, [ty]) -> Format.fprintf fm "@[@[%a@] %a@]" print' ty Path.print c
  | TConstr(c, tys) -> Format.fprintf fm "@[@[(%a)@] %a@]" (print_list print' ",@ ") tys Path.print c
  | TPackage ty -> Format.fprintf fm "(module %a)" print' ty
  | TPoly(vars, ty) -> (* assumed not to be nested *)
      assert (List.for_all (fun r -> !r = None) vars);
      let names = List.mapi (fun i _ -> "'t" ^ string_of_int i) vars in
      let tys = List.map (fun name -> Some (TConstr(LId (Id.make name ()), []))) names in
      List.iter2 (:=) vars tys;
      Format.fprintf fm "@[%a. %a@]" (print_list Format.pp_print_string  " ") names print' ty;
      List.iter (fun x -> x := None) vars
  | TConstraint(ty, cs) ->
      let pr fm (p,c) =
        Format.fprintf fm "@ constraint %a = %a" print' p print' c
      in
      Format.fprintf fm "@[%a%a@]" print' ty (print_list pr "") cs
  | TOpen ->
      Format.fprintf fm ".."

let typ_init fm typ = print !!init_config fm typ
let typ ?(occur = !!init_config.occur) print_pred fm typ =
  let cfg = {!!init_config with occur; print_pred} in
  Format.fprintf fm "@[%a@]" (print cfg) typ
let decl_item_init fm decl = print_decl_item !!init_config fm ~first:true ~last:true decl
let decl_init fm decl = print_declaration !!init_config fm decl
let decl ?(occur = !!init_config.occur) print_pred fm decl =
  let cfg = {!!init_config with occur; print_pred} in
  print_declaration cfg fm decl
let attr fm attr = print_attr !!init_config fm attr
let tvar = print_tvar
let constr = print_constr
let path = print_path
let label = print_constr
let tconstr = print_tconstr
let effect = print_effect
let base = print_base
let signature fm sgn = print_signature !!init_config fm sgn
let row = print_row
let row_init fm row = print_row !!init_config false fm row
let ext fm ext = print_ext !!init_config fm ext
let exts fm exts = print_ext_list !!init_config ~has_cont:false fm exts
